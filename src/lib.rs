//! The Lode compiler.
//!
//! The pipeline: [`lex`] → [`parse`] → [`sema`] (types and proof obligations)
//! → [`lower`] (to LatticeFoundry IR) → LatticeFoundry's verify, optimize,
//! codegen and link. The design of the language is in `docs/`.
//!
//! This is a scaffold: it supports functions, integers, `bool`, local
//! variables, arithmetic and control flow. Everything else in the design is
//! reported as "not supported by the compiler yet".

pub mod ast;
pub mod diag;
pub mod lex;
pub mod lower;
pub mod parse;
pub mod sema;
pub mod source;
pub mod types;

use latticefoundry::Module;
use latticefoundry::ir::text;
use latticefoundry::link::{self, ImageOptions};
use latticefoundry::support::StrInterner;
use latticefoundry::target::x86_64;
use latticefoundry::transform::pipeline::{self, OptLevel};
use latticefoundry::verify;

use crate::diag::{Diagnostic, has_errors};
use crate::source::{SourceFile, Span};

pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// The address width of the only target the backend can link for today
/// (x86-64 Linux).
pub const PTR_BITS: u32 = 64;

/// Why compiling a file failed.
#[derive(Debug)]
pub enum Error {
    /// Problems in the source, to be rendered against the file.
    Source(Vec<Diagnostic>),
    /// A backend failure. For a checked program this is a compiler bug.
    Backend(String),
}

/// Lex, parse and check a source file.
pub fn check(file: &SourceFile) -> Result<sema::Program, Error> {
    let (tokens, mut diags) = lex::lex(&file.text);
    let (ast, parse_diags) = parse::parse(tokens);
    diags.extend(parse_diags);
    if has_errors(&diags) {
        return Err(Error::Source(diags));
    }
    let (program, sema_diags) = sema::check(&ast, PTR_BITS);
    diags.extend(sema_diags);
    if has_errors(&diags) {
        return Err(Error::Source(diags));
    }
    Ok(program)
}

/// Compile a source file to a verified, optimized IR module.
pub fn compile_ir(file: &SourceFile, opt: OptLevel) -> Result<(Module, StrInterner), Error> {
    let program = check(file)?;
    let (mut module, syms) = lower::lower(&program);
    verify_module(&module, "lowered")?;
    pipeline::optimize(&mut module, opt);
    if opt != OptLevel::O0 {
        verify_module(&module, "optimized")?;
    }
    Ok((module, syms))
}

/// The IR of a source file in LatticeFoundry's text format.
pub fn ir_text(file: &SourceFile, opt: OptLevel) -> Result<String, Error> {
    let (module, syms) = compile_ir(file, opt)?;
    Ok(text::print_module(&module, &syms))
}

/// Compile a source file to a static x86-64 Linux executable, returning the
/// ELF image bytes. The program's `main` return value is its exit status.
pub fn build_executable(file: &SourceFile, opt: OptLevel) -> Result<Vec<u8>, Error> {
    let program = check(file)?;
    if program.main.is_none() {
        let end = file.text.len();
        return Err(Error::Source(vec![Diagnostic::error(
            Span::new(end, end),
            "this program has no `main` function",
        )]));
    }
    let (module, syms) = compile_ir(file, opt)?;
    let object = x86_64::compile_module(&module, &syms);
    let options = ImageOptions {
        entry: lower::ENTRY_SYMBOL.to_owned(),
        ..ImageOptions::default()
    };
    link::link_executable(vec![object], &options)
        .map_err(|e| Error::Backend(format!("link error: {e}")))
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
