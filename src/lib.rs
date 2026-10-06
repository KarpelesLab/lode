//! The Lode compiler.
//!
//! The pipeline: [`load`] (the root file and the packages it imports, each
//! [`lex`]ed and [`parse`]d) → [`sema`] (types, `unsafe`, and proof
//! obligations, over all the code, generic bodies once, for one
//! [`target`]; constants are computed there, by its evaluator) → [`lower`] (to
//! LatticeFoundry IR, only the code `main` reaches: the instances [`mono`]
//! makes) → LatticeFoundry's verify, optimize, codegen and link. The design
//! of the language is in `docs/`.
//!
//! This is an early compiler: it supports functions, generic functions,
//! traits and `impl` blocks, integers, `bool`, `str`,
//! arrays and slices, structs, enums and `match`, optionals, raw pointers in
//! `unsafe` code, constants computed at compile time, `if comptime`,
//! local variables, arithmetic, control flow (including `for` loops) and
//! packages. Everything else in the design is
//! reported as "not supported by the compiler yet".

pub mod ast;
pub mod debug;
pub mod diag;
pub mod fmt;
pub mod lex;
pub mod load;
pub mod lower;
pub mod mono;
pub mod parse;
pub mod sema;
pub mod source;
pub mod stack;
pub mod target;
pub mod types;

use std::path::PathBuf;

use latticefoundry::Module;
use latticefoundry::codegen::CodegenOptions;
use latticefoundry::ir::text;
use latticefoundry::link::{self, ImageOptions};
use latticefoundry::mc::object::{
    ObjectModule, Section, SectionKind, Symbol, SymbolBinding, SymbolType,
};
use latticefoundry::target::x86_64;
use latticefoundry::transform::pipeline::{self, OptLevel};
use latticefoundry::verify;

use crate::diag::{Diagnostic, has_errors};
use crate::lower::Lowered;
use crate::source::{FileId, SourceMap, Span};
use crate::stack::StackReport;
pub use crate::target::Target;

pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// Why compiling failed.
#[derive(Debug)]
pub enum Error {
    /// Problems in the source, to be rendered against the [`SourceMap`].
    Source(Vec<Diagnostic>),
    /// A backend failure. For a checked program this is a compiler bug.
    Backend(String),
}

/// Where the standard library's sources are: `$LODE_STD` if set, otherwise
/// the `std/` directory of the compiler's source tree.
pub fn std_root() -> PathBuf {
    std::env::var_os("LODE_STD")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/std")))
}

/// Load, parse and check the program whose root file is `root`, along with
/// every package it imports. Warnings don't fail the check: they're in the
/// program's [`sema::Program::warnings`] (or with the errors, if there are
/// any).
pub fn check(files: &mut SourceMap, root: FileId) -> Result<sema::Program, Error> {
    check_for(files, root, Target::host())
}

/// [`check`] for `target`.
pub fn check_for(
    files: &mut SourceMap,
    root: FileId,
    target: &Target,
) -> Result<sema::Program, Error> {
    let (packages, mut diags) = load::load(files, root, &std_root());
    if has_errors(&diags) {
        return Err(Error::Source(diags));
    }
    let (mut program, sema_diags) = check_packages(&packages, target);
    diags.extend(sema_diags);
    if has_errors(&diags) {
        return Err(Error::Source(diags));
    }
    program.warnings = diags;
    Ok(program)
}

/// Check a program for each of `targets` (docs/comptime.md, Keeping dead
/// branches from rotting). It's loaded and parsed once. For each target,
/// in order: its errors and warnings. An error loading the program is
/// `Err`.
pub fn check_targets(
    files: &mut SourceMap,
    root: FileId,
    targets: &[&Target],
) -> Result<Vec<Vec<Diagnostic>>, Error> {
    let (packages, diags) = load::load(files, root, &std_root());
    if has_errors(&diags) {
        return Err(Error::Source(diags));
    }
    Ok(targets
        .iter()
        .map(|target| {
            let mut all = diags.clone();
            all.extend(check_packages(&packages, target).1);
            all
        })
        .collect())
}

/// How much stack the checker gets: compile-time evaluation recurses with
/// the program's calls (docs/generics.md, The evaluator). Only what's used
/// is committed.
const CHECK_STACK: usize = 256 << 20;

/// Run the checker on loaded packages, on a thread with a deep stack.
fn check_packages(packages: &[load::Package], target: &Target) -> (sema::Program, Vec<Diagnostic>) {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .name("lode-check".to_owned())
            .stack_size(CHECK_STACK)
            .spawn_scoped(s, || sema::check(packages, target))
            .expect("can start the checker's thread")
            .join()
            .unwrap_or_else(|e| std::panic::resume_unwind(e))
    })
}

/// Compile a program to a verified, optimized IR module.
pub fn compile_ir(files: &mut SourceMap, root: FileId, opt: OptLevel) -> Result<Lowered, Error> {
    compile_ir_with(files, root, opt, false)
}

/// [`compile_ir`]; with `debug`, its instructions have source lines
/// ([`Lowered::lines`]).
pub fn compile_ir_with(
    files: &mut SourceMap,
    root: FileId,
    opt: OptLevel,
    debug: bool,
) -> Result<Lowered, Error> {
    let program = check(files, root)?;
    let name = &files.get(root).name;
    let mut lowered = if debug {
        lower::lower_debug(&program, name, files)
    } else {
        lower::lower(&program, name)
    };
    verify_module(&lowered.module, "lowered")?;
    let decl_lines: Vec<_> = lowered
        .funcs
        .iter()
        .map(|&(id, _)| (id, lowered.module.function(id).decl_line))
        .collect();
    pipeline::optimize(&mut lowered.module, opt);
    if opt != OptLevel::O0 {
        // The pipeline ends with an inlining round and no `simplify_cfg`:
        // the blocks inlining leaves are merged here, then the functions
        // it left without callers are dropped.
        pipeline::run_passes(
            &mut lowered.module,
            ["simplify_cfg", "sccp", "dce"]
                .iter()
                .map(|n| pipeline::pass_by_name(n).expect("a pass"))
                .collect(),
        );
        drop_unreferenced(&mut lowered);
        verify_module(&lowered.module, "optimized")?;
        if debug {
            // LF's passes rebuild the functions they change without their
            // declaration lines (or their instructions' lines).
            for (id, line) in decl_lines {
                let f = lowered.module.function(id);
                if f.decl_line != line && !f.is_declaration() {
                    let mut f = f.clone();
                    f.decl_line = line;
                    lowered.module.replace_function(id, f);
                }
            }
        }
    }
    Ok(lowered)
}

/// Make the internal functions that nothing reaches any more (inlined into
/// every caller) declarations, so no code is emitted for them. A function
/// is reached from the external ones (the entry) through the functions its
/// code refers to.
fn drop_unreferenced(lowered: &mut Lowered) {
    use latticefoundry::ir::{Function, ValueDef};
    let module = &mut lowered.module;
    let mut reached: std::collections::HashSet<latticefoundry::ir::FuncId> = lowered
        .funcs
        .iter()
        .filter(|(_, internal)| !internal)
        .map(|&(id, _)| id)
        .collect();
    let mut work: Vec<_> = reached.iter().copied().collect();
    while let Some(id) = work.pop() {
        let f = module.function(id);
        let insts = f
            .blocks()
            .flat_map(|(_, b)| b.insts().iter().copied().chain(b.terminator()));
        for inst in insts {
            for &v in f.inst(inst).operands() {
                if let ValueDef::Func(g) = f.value(v).def
                    && reached.insert(g)
                {
                    work.push(g);
                }
            }
        }
    }
    for &(id, _) in &lowered.funcs {
        if !reached.contains(&id) {
            let f = module.function(id);
            let decl = Function::new(f.name, f.sig);
            module.replace_function(id, decl);
        }
    }
}

/// The IR of a program in LatticeFoundry's text format.
pub fn ir_text(files: &mut SourceMap, root: FileId, opt: OptLevel) -> Result<String, Error> {
    let lowered = compile_ir(files, root, opt)?;
    Ok(text::print_module(&lowered.module, &lowered.syms))
}

/// How to build an executable.
#[derive(Clone, Debug, Default)]
pub struct BuildOptions {
    /// The optimization level.
    pub opt: OptLevel,
    /// Whether to include debug information: DWARF line tables and
    /// functions, section headers and a symbol table ([`debug`]).
    pub debug: bool,
}

/// A built program.
#[derive(Debug)]
pub struct Executable {
    /// The static x86-64 Linux ELF image.
    pub image: Vec<u8>,
    /// Every function's stack frame, and the program's worst-case stack depth.
    pub stack: StackReport,
    /// Warnings about the program, which compiled anyway.
    pub warnings: Vec<Diagnostic>,
}

/// Compile a program to a static x86-64 Linux executable, with its stack
/// usage. The program's `main` return value is its exit status.
pub fn build(
    files: &mut SourceMap,
    root: FileId,
    options: &BuildOptions,
) -> Result<Executable, Error> {
    let program = check(files, root)?;
    if program.main.is_none() {
        let end = files.get(root).text.len();
        return Err(Error::Source(vec![Diagnostic::error(
            Span::new(root, end, end),
            "this program has no `main` function",
        )]));
    }
    let lowered = compile_ir_with(files, root, options.opt, options.debug)?;
    let entry = lowered
        .entry
        .clone()
        .expect("a program with `main` has an entry");
    let codegen = CodegenOptions::default();
    let (mut object, stack) = if options.debug {
        // LF's DWARF is for one file, its lines the IR line numbers:
        // replaced by Lode's, over the program's files.
        let comp_dir = std::env::current_dir()
            .ok()
            .and_then(|p| p.to_str().map(str::to_owned))
            .unwrap_or_default();
        let source = x86_64::DebugSource {
            file_name: files.get(root).name.clone(),
            comp_dir: comp_dir.clone(),
        };
        let compiled =
            x86_64::compile_module_debug_with(&lowered.module, &lowered.syms, &source, &codegen);
        let object = debug::rewrite(&compiled.object, &lowered.lines, files, root, &comp_dir)
            .map_err(Error::Backend)?;
        (object, compiled.stack)
    } else {
        let compiled = x86_64::compile_module_with(&lowered.module, &lowered.syms, &codegen);
        (compiled.object, compiled.stack)
    };
    emit_rodata(&mut object, &lowered.strings, &lowered.tables);
    emit_data(&mut object, &lowered.data);
    let link_options = ImageOptions {
        entry: entry.clone(),
        debug: options.debug,
        ..ImageOptions::default()
    };
    let image = link::link_executable(vec![object], &link_options)
        .map_err(|e| Error::Backend(format!("link error: {e}")))?;
    Ok(Executable {
        image,
        stack: StackReport::new(stack, entry),
        warnings: lowered.warnings,
    })
}

/// Compile a program to a static x86-64 Linux executable, returning the ELF
/// image bytes. [`build`] also returns its stack usage.
pub fn build_executable(
    files: &mut SourceMap,
    root: FileId,
    opt: OptLevel,
) -> Result<Vec<u8>, Error> {
    build(
        files,
        root,
        &BuildOptions {
            opt,
            ..BuildOptions::default()
        },
    )
    .map(|e| e.image)
}

/// Define the symbols of the string literals and of the array constants
/// (`(symbol, bytes, alignment)`) in a read-only data section (the IR
/// globals are references to these). The tables come first, each at its
/// alignment, then the strings, which need none.
fn emit_rodata(
    object: &mut ObjectModule,
    strings: &[(String, Vec<u8>)],
    tables: &[(String, Vec<u8>, u64)],
) {
    if strings.is_empty() && tables.is_empty() {
        return;
    }
    let align = tables.iter().map(|t| t.2).max().unwrap_or(1);
    let section = object.add_section(Section::new(".rodata", SectionKind::Rodata, align));
    let mut bytes = Vec::new();
    let items = tables
        .iter()
        .map(|(name, data, align)| (name, data, *align))
        .chain(strings.iter().map(|(name, data)| (name, data, 1)));
    for (name, data, align) in items {
        bytes.resize(bytes.len().next_multiple_of(align as usize), 0);
        let offset = bytes.len() as u64;
        bytes.extend_from_slice(data);
        object.add_symbol(Symbol::defined(
            name.clone(),
            SymbolBinding::Local,
            SymbolType::Object,
            section,
            offset,
            data.len() as u64,
        ));
    }
    object.section_mut(section).bytes = bytes;
}

/// Define the symbols of the `static`s (`(symbol, bytes, alignment)`):
/// those whose bytes are all zeros in a `.bss` section, which takes no
/// space in the file, the others in a `.data` section.
fn emit_data(object: &mut ObjectModule, data: &[(String, Vec<u8>, u64)]) {
    for bss in [true, false] {
        let items: Vec<&(String, Vec<u8>, u64)> = data
            .iter()
            .filter(|(_, bytes, _)| bytes.iter().all(|&b| b == 0) == bss)
            .collect();
        if items.is_empty() {
            continue;
        }
        let align = items.iter().map(|d| d.2).max().unwrap_or(1).max(1);
        let mut bytes = Vec::new();
        let mut placed = Vec::new();
        for (name, data, align) in &items {
            bytes.resize(bytes.len().next_multiple_of((*align).max(1) as usize), 0);
            placed.push((name.clone(), bytes.len() as u64, data.len() as u64));
            bytes.extend_from_slice(data);
        }
        let section = if bss {
            object.add_section(Section::bss(".bss", align, (bytes.len() as u64).max(1)))
        } else {
            let mut s = Section::new(".data", SectionKind::Data, align);
            s.bytes = bytes;
            object.add_section(s)
        };
        for (name, offset, size) in placed {
            object.add_symbol(Symbol::defined(
                name,
                SymbolBinding::Local,
                SymbolType::Object,
                section,
                offset,
                size,
            ));
        }
    }
}

fn verify_module(module: &Module, stage: &str) -> Result<(), Error> {
    verify::verify_module(module).map_err(|diags| {
        let messages: Vec<String> = diags.iter().map(|d| d.message.clone()).collect();
        Error::Backend(format!(
            "{stage} IR failed verification: {}",
            messages.join("; ")
        ))
    })
}
