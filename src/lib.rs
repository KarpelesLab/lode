//! The Lode compiler.
//!
//! The pipeline: [`load`] (the root file and the packages it imports, each
//! [`lex`]ed and [`parse`]d) → [`sema`] (types, `unsafe`, and proof
//! obligations) → [`lower`] (to LatticeFoundry IR) → LatticeFoundry's verify,
//! optimize, codegen and link. The design of the language is in `docs/`.
//!
//! This is an early compiler: it supports functions, integers, `bool`, `str`,
//! raw pointers in `unsafe` code, constants, local variables, arithmetic,
//! control flow and packages. Everything else in the design is reported as
//! "not supported by the compiler yet".

pub mod ast;
pub mod diag;
pub mod fmt;
pub mod lex;
pub mod load;
pub mod lower;
pub mod parse;
pub mod sema;
pub mod source;
pub mod stack;
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

pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// The address width of the only target the backend can link for today
/// (x86-64 Linux).
pub const PTR_BITS: u32 = 64;

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
/// every package it imports.
pub fn check(files: &mut SourceMap, root: FileId) -> Result<sema::Program, Error> {
    let (packages, mut diags) = load::load(files, root, &std_root());
    if has_errors(&diags) {
        return Err(Error::Source(diags));
    }
    let (program, sema_diags) = sema::check(&packages, PTR_BITS);
    diags.extend(sema_diags);
    if has_errors(&diags) {
        return Err(Error::Source(diags));
    }
    Ok(program)
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
    let compiled =
        x86_64::compile_module_with(&lowered.module, &lowered.syms, &CodegenOptions::default());
    let mut object = compiled.object;
    emit_strings(&mut object, &lowered.strings);
    let link_options = ImageOptions {
        entry: lower::ENTRY_SYMBOL.to_owned(),
        ..ImageOptions::default()
    };
    let image = link::link_executable(vec![object], &link_options)
        .map_err(|e| Error::Backend(format!("link error: {e}")))?;
    Ok(Executable {
        image,
        stack: StackReport::new(compiled.stack, lower::ENTRY_SYMBOL),
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

/// Define the string literals' symbols in a read-only data section (the code
/// generator only emits code; the IR globals are references to these).
fn emit_strings(object: &mut ObjectModule, strings: &[(String, Vec<u8>)]) {
    if strings.is_empty() {
        return;
    }
    let section = object.add_section(Section::new(".rodata", SectionKind::Rodata, 1));
    let mut bytes = Vec::new();
    for (name, data) in strings {
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
