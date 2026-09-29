//! `lode`: the Lode compiler driver.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use latticefoundry::transform::pipeline::OptLevel;
use lode::source::SourceFile;

const USAGE: &str = "\
lode: the Lode compiler

usage:
  lode build <file.lode> [-o <output>] [-O0|-O1|-O2|-O3] [--emit=ir]
  lode run <file.lode> [-O0|-O1|-O2|-O3]
  lode check <file.lode>
  lode version | help

  build   compile to a static x86-64 Linux executable
          (--emit=ir prints the LatticeFoundry IR instead)
  run     build to a temporary file, run it, exit with its status
  check   check the program without generating code
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some(command) = args.first() else {
        eprint!("{USAGE}");
        return ExitCode::FAILURE;
    };
    let rest = &args[1..];
    let result = match command.as_str() {
        "build" => build(rest),
        "run" => run(rest),
        "check" => check(rest),
        "fmt" => Err("`lode fmt` is not implemented yet".to_owned()),
        "version" | "--version" | "-V" => {
            println!("lode {}", lode::VERSION);
            Ok(ExitCode::SUCCESS)
        }
        "help" | "--help" | "-h" => {
            print!("{USAGE}");
            Ok(ExitCode::SUCCESS)
        }
        other => Err(format!("unknown command `{other}` (see `lode help`)")),
    };
    match result {
        Ok(code) => code,
        Err(msg) => {
            eprintln!("lode: {msg}");
            ExitCode::FAILURE
        }
    }
}

struct Options {
    input: String,
    output: Option<String>,
    opt: OptLevel,
    emit_ir: bool,
}

fn parse_options(args: &[String]) -> Result<Options, String> {
    let mut input = None;
    let mut output = None;
    let mut opt = OptLevel::O0;
    let mut emit_ir = false;
    let mut it = args.iter();
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "-o" => output = Some(it.next().ok_or("`-o` needs a path")?.clone()),
            "--emit=ir" => emit_ir = true,
            flag if OptLevel::parse_flag(flag).is_some() => {
                opt = OptLevel::parse_flag(flag).expect("checked")
            }
            flag if flag.starts_with('-') => return Err(format!("unknown option `{flag}`")),
            path if input.is_none() => input = Some(path.to_owned()),
            extra => return Err(format!("unexpected argument `{extra}`")),
        }
    }
    let input = input.ok_or("no input file (see `lode help`)")?;
    Ok(Options {
        input,
        output,
        opt,
        emit_ir,
    })
}

fn load(path: &str) -> Result<SourceFile, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("cannot read {path}: {e}"))?;
    Ok(SourceFile::new(path, text))
}

/// Print a compile error; returns the failure exit code.
fn report(file: &SourceFile, err: lode::Error) -> ExitCode {
    match err {
        lode::Error::Source(diags) => {
            for d in &diags {
                eprint!("{}", d.render(file));
            }
            let errors = diags.iter().filter(|d| d.is_error()).count();
            eprintln!("lode: {errors} error(s)");
        }
        lode::Error::Backend(msg) => eprintln!("lode: internal compiler error: {msg}"),
    }
    ExitCode::FAILURE
}

fn check(args: &[String]) -> Result<ExitCode, String> {
    let opts = parse_options(args)?;
    let file = load(&opts.input)?;
    Ok(match lode::check(&file) {
        Ok(_) => ExitCode::SUCCESS,
        Err(e) => report(&file, e),
    })
}

fn build(args: &[String]) -> Result<ExitCode, String> {
    let opts = parse_options(args)?;
    let file = load(&opts.input)?;
    if opts.emit_ir {
        return Ok(match lode::ir_text(&file, opts.opt) {
            Ok(text) => {
                print!("{text}");
                ExitCode::SUCCESS
            }
            Err(e) => report(&file, e),
        });
    }
    let image = match lode::build_executable(&file, opts.opt) {
        Ok(image) => image,
        Err(e) => return Ok(report(&file, e)),
    };
    let output = opts.output.unwrap_or_else(|| default_output(&opts.input));
    latticefoundry::link::write_executable(&output, &image)?;
    Ok(ExitCode::SUCCESS)
}

fn run(args: &[String]) -> Result<ExitCode, String> {
    let opts = parse_options(args)?;
    let file = load(&opts.input)?;
    let image = match lode::build_executable(&file, opts.opt) {
        Ok(image) => image,
        Err(e) => return Ok(report(&file, e)),
    };
    let path = temp_path(&opts.input);
    let path_str = path.to_str().ok_or("temporary path is not valid UTF-8")?;
    latticefoundry::link::write_executable(path_str, &image)?;
    let status = std::process::Command::new(&path).status();
    let _ = std::fs::remove_file(&path);
    let status = status.map_err(|e| format!("cannot run the program: {e}"))?;
    Ok(match status.code() {
        Some(code) => ExitCode::from(code as u8),
        None => {
            eprintln!("lode: the program was killed by a signal");
            ExitCode::FAILURE
        }
    })
}

/// The input's file name without its extension, in the current directory.
fn default_output(input: &str) -> String {
    Path::new(input)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("a.out")
        .to_owned()
}

fn temp_path(input: &str) -> PathBuf {
    let stem = default_output(input);
    std::env::temp_dir().join(format!("lode-run-{}-{stem}", std::process::id()))
}
