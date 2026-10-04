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
//! This is an early compiler: it supports functions, generic functions over
//! the built-in traits, integers, `bool`, `str`,
//! arrays and slices, structs, enums and `match`, optionals, raw pointers in
//! `unsafe` code, constants computed at compile time, `if comptime`,
//! local variables, arithmetic, control flow (including `for` loops) and
//! packages. Everything else in the design is
//! reported as "not supported by the compiler yet".

pub mod ast;
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
    let program = check(files, root)?;
    let mut lowered = lower::lower(&program, &files.get(root).name);
    verify_module(&lowered.module, "lowered")?;
    pipeline::optimize(&mut lowered.module, opt);
    if opt != OptLevel::O0 {
        verify_module(&lowered.module, "optimized")?;
    }
    Ok(lowered)
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
    let lowered = compile_ir(files, root, options.opt)?;
    let entry = lowered
        .entry
        .clone()
        .expect("a program with `main` has an entry");
    let compiled =
        x86_64::compile_module_with(&lowered.module, &lowered.syms, &CodegenOptions::default());
    let mut object = compiled.object;
    emit_rodata(&mut object, &lowered.strings, &lowered.tables);
    let link_options = ImageOptions {
        entry: entry.clone(),
        ..ImageOptions::default()
    };
    let image = link::link_executable(vec![object], &link_options)
        .map_err(|e| Error::Backend(format!("link error: {e}")))?;
    Ok(Executable {
        image,
        stack: StackReport::new(compiled.stack, entry),
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
    build(files, root, &BuildOptions { opt }).map(|e| e.image)
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

fn verify_module(module: &Module, stage: &str) -> Result<(), Error> {
    verify::verify_module(module).map_err(|diags| {
        let messages: Vec<String> = diags.iter().map(|d| d.message.clone()).collect();
        Error::Backend(format!(
            "{stage} IR failed verification: {}",
            messages.join("; ")
        ))
    })
}
