//! `lode`: the Lode compiler driver.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use latticefoundry::transform::pipeline::OptLevel;
use lode::Target;
use lode::source::{FileId, SourceFile, SourceMap};

const USAGE: &str = "\
lode: the Lode compiler

usage:
  lode build <file.lode> [-o <output>] [-O0|-O1|-O2|-O3] [--emit=ir]
             [--stack-usage]
  lode run <file.lode> [-O0|-O1|-O2|-O3]
  lode check <file.lode> [--targets=<target,...>|--targets=all]
  lode targets
  lode fmt [--check] <files or directories...>
  lode version | help

  build   compile to a static x86-64 Linux executable
          (--emit=ir prints the LatticeFoundry IR instead;
          --stack-usage prints each function's stack frame and the
          worst-case stack depth, or why there is no bound)
  run     build to a temporary file, run it, exit with its status
  check   check the program without generating code, for x86_64-linux
          or for each of --targets (all: every target the compiler
          knows)
  targets list the targets: each can be checked, x86_64-linux built
  fmt     rewrite files in the canonical format (directories are searched
          for .lode files); --check changes nothing, lists the files that
          aren't canonical and fails if there are any
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
        "targets" => Ok(targets()),
        "fmt" => fmt(rest),
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
    stack_usage: bool,
    /// `--targets=...`, for `lode check`.
    targets: Option<Vec<&'static Target>>,
}

/// Reject the options only `lode build` takes.
fn build_only(opts: &Options, command: &str) -> Result<(), String> {
    for (set, flag) in [
        (opts.emit_ir, "--emit=ir"),
        (opts.stack_usage, "--stack-usage"),
    ] {
        if set {
            return Err(format!(
                "`{flag}` is for `lode build`, not `lode {command}`"
            ));
        }
    }
    Ok(())
}

/// Reject `--targets`, which only `lode check` takes.
fn check_only(opts: &Options) -> Result<(), String> {
    if opts.targets.is_some() {
        return Err(format!(
            "`--targets` is for `lode check`: only {} can be built",
            Target::host().name
        ));
    }
    Ok(())
}

fn parse_options(args: &[String]) -> Result<Options, String> {
    let mut input = None;
    let mut output = None;
    let mut opt = OptLevel::O0;
    let mut emit_ir = false;
    let mut stack_usage = false;
    let mut targets = None;
    let mut it = args.iter();
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "-o" => output = Some(it.next().ok_or("`-o` needs a path")?.clone()),
            "--emit=ir" => emit_ir = true,
            "--stack-usage" => stack_usage = true,
            flag if flag.starts_with("--targets=") => {
                targets = Some(parse_targets(&flag["--targets=".len()..])?)
            }
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
        stack_usage,
        targets,
    })
}

/// The targets of `--targets=`: a comma-separated list of names, or `all`.
fn parse_targets(list: &str) -> Result<Vec<&'static Target>, String> {
    if list == "all" {
        return Ok(lode::target::TARGETS.iter().collect());
    }
    let mut out: Vec<&'static Target> = Vec::new();
    for name in list.split(',') {
        let t = Target::by_name(name).ok_or_else(|| {
            format!(
                "unknown target `{name}` (the targets are {}, or `all`)",
                lode::target::names()
            )
        })?;
        if !out.contains(&t) {
            out.push(t);
        }
    }
    Ok(out)
}

/// `lode targets`: every target, and what can be done for it.
fn targets() -> ExitCode {
    for t in lode::target::TARGETS {
        let what = if t.can_build {
            "check and build"
        } else {
            "check"
        };
        println!("{:<14} {:>2}-bit  {what}", t.name, t.pointer_bits);
    }
    ExitCode::SUCCESS
}

fn load(path: &str) -> Result<(SourceMap, FileId), String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("cannot read {path}: {e}"))?;
    let mut files = SourceMap::new();
    let root = files.add(SourceFile::new(path, text));
    Ok((files, root))
}

/// Print the warnings of a program that compiled.
fn warn(files: &SourceMap, warnings: &[lode::diag::Diagnostic]) {
    for d in warnings {
        eprint!("{}", d.render(files));
    }
}

/// Print a compile error; returns the failure exit code.
fn report(files: &SourceMap, err: lode::Error) -> ExitCode {
    match err {
        lode::Error::Source(diags) => {
            for d in &diags {
                eprint!("{}", d.render(files));
            }
            let errors = diags.iter().filter(|d| d.is_error()).count();
            eprintln!("lode: {errors} error(s)");
        }
        lode::Error::Backend(msg) => eprintln!("lode: internal compiler error: {msg}"),
    }
    ExitCode::FAILURE
}

fn check(args: &[String]) -> Result<ExitCode, String> {
    let mut opts = parse_options(args)?;
    let targets = opts.targets.take();
    build_only(&opts, "check")?;
    let (mut files, root) = load(&opts.input)?;
    if let Some(targets) = targets {
        return Ok(check_targets(&mut files, root, &targets));
    }
    Ok(match lode::check(&mut files, root) {
        Ok(program) => {
            warn(&files, &program.warnings);
            ExitCode::SUCCESS
        }
        Err(e) => report(&files, e),
    })
}

/// `lode check --targets=...`: check for each target, and print each
/// message once, saying which targets it's for unless it's all of them.
fn check_targets(files: &mut SourceMap, root: FileId, targets: &[&'static Target]) -> ExitCode {
    let per_target = match lode::check_targets(files, root, targets) {
        Ok(diags) => diags,
        Err(e) => return report(files, e),
    };
    // Each distinct message, in order, with the targets it's for.
    let mut found: Vec<(String, lode::diag::Diagnostic, Vec<&str>)> = Vec::new();
    for (target, diags) in targets.iter().zip(per_target) {
        for d in diags {
            let text = d.render(files);
            match found.iter_mut().find(|(t, ..)| *t == text) {
                Some((.., on)) => on.push(target.name),
                None => found.push((text, d, vec![target.name])),
            }
        }
    }
    let mut errors = 0;
    for (text, d, on) in found {
        if d.is_error() {
            errors += 1;
        }
        if on.len() == targets.len() {
            eprint!("{text}");
        } else {
            let d = d.with_help(format!("for the target(s) {}", on.join(", ")));
            eprint!("{}", d.render(files));
        }
    }
    let names: Vec<&str> = targets.iter().map(|t| t.name).collect();
    if errors > 0 {
        eprintln!("lode: {errors} error(s), checking for {}", names.join(", "));
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

fn build(args: &[String]) -> Result<ExitCode, String> {
    let opts = parse_options(args)?;
    check_only(&opts)?;
    if opts.emit_ir && opts.stack_usage {
        return Err("`--stack-usage` needs machine code, not `--emit=ir`".to_owned());
    }
    let (mut files, root) = load(&opts.input)?;
    if opts.emit_ir {
        return Ok(match lode::compile_ir(&mut files, root, opts.opt) {
            Ok(lowered) => {
                warn(&files, &lowered.warnings);
                let text = latticefoundry::ir::text::print_module(&lowered.module, &lowered.syms);
                print!("{text}");
                ExitCode::SUCCESS
            }
            Err(e) => report(&files, e),
        });
    }
    let build_options = lode::BuildOptions { opt: opts.opt };
    let exe = match lode::build(&mut files, root, &build_options) {
        Ok(exe) => exe,
        Err(e) => return Ok(report(&files, e)),
    };
    warn(&files, &exe.warnings);
    let output = opts.output.unwrap_or_else(|| default_output(&opts.input));
    latticefoundry::link::write_executable(&output, &exe.image)?;
    if opts.stack_usage {
        print!("{}", exe.stack);
    }
    Ok(ExitCode::SUCCESS)
}

fn run(args: &[String]) -> Result<ExitCode, String> {
    let opts = parse_options(args)?;
    check_only(&opts)?;
    build_only(&opts, "run")?;
    let (mut files, root) = load(&opts.input)?;
    let build_options = lode::BuildOptions { opt: opts.opt };
    let image = match lode::build(&mut files, root, &build_options) {
        Ok(exe) => {
            warn(&files, &exe.warnings);
            exe.image
        }
        Err(e) => return Ok(report(&files, e)),
    };
    let path = temp_path(&opts.input);
    let path_str = path.to_str().ok_or("temporary path is not valid UTF-8")?;
    latticefoundry::link::write_executable(path_str, &image)?;
    let status = std::process::Command::new(&path).status();
    let _ = std::fs::remove_file(&path);
    let status = status.map_err(|e| format!("cannot run the program: {e}"))?;
    Ok(match status.code() {
        Some(code) => ExitCode::from(code as u8),
        None => killed(&status),
    })
}

/// Report a program killed by a signal; exit like a shell would, with
/// 128 plus the signal number (Linux numbering; the only target).
#[cfg(target_os = "linux")]
fn killed(status: &std::process::ExitStatus) -> ExitCode {
    use std::os::unix::process::ExitStatusExt;
    let Some(signal) = status.signal() else {
        eprintln!("lode: the program was killed by a signal");
        return ExitCode::FAILURE;
    };
    // Signals 1 to 31, in order.
    const NAMES: &str = "HUP INT QUIT ILL TRAP ABRT BUS FPE KILL USR1 SEGV USR2 PIPE ALRM TERM \
                         STKFLT CHLD CONT STOP TSTP TTIN TTOU URG XCPU XFSZ VTALRM PROF WINCH \
                         IO PWR SYS";
    let name = usize::try_from(signal)
        .ok()
        .and_then(|n| NAMES.split(' ').nth(n.checked_sub(1)?));
    match name {
        Some(name) => eprintln!("lode: the program was killed by SIG{name} (signal {signal})"),
        None => eprintln!("lode: the program was killed by signal {signal}"),
    }
    ExitCode::from((128 + signal).clamp(0, 255) as u8)
}

#[cfg(not(target_os = "linux"))]
fn killed(_: &std::process::ExitStatus) -> ExitCode {
    eprintln!("lode: the program was killed");
    ExitCode::FAILURE
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

fn fmt(args: &[String]) -> Result<ExitCode, String> {
    let mut check = false;
    let mut paths = Vec::new();
    for arg in args {
        match arg.as_str() {
            "--check" => check = true,
            flag if flag.starts_with('-') => return Err(format!("unknown option `{flag}`")),
            path => paths.push(PathBuf::from(path)),
        }
    }
    if paths.is_empty() {
        return Err("no files or directories to format (see `lode help`)".to_owned());
    }
    let mut files = Vec::new();
    for path in &paths {
        if path.is_dir() {
            lode_files(path, &mut files)
                .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
        } else {
            files.push(path.clone());
        }
    }
    let mut failed = false;
    for path in &files {
        let name = path.display().to_string();
        let text = std::fs::read_to_string(path).map_err(|e| format!("cannot read {name}: {e}"))?;
        let mut map = SourceMap::new();
        let id = map.add(SourceFile::new(name.clone(), text));
        let text = &map.get(id).text;
        match lode::fmt::format(text, id) {
            Ok(formatted) if formatted == *text => {}
            Ok(_) if check => {
                println!("{name}");
                failed = true;
            }
            Ok(formatted) => {
                std::fs::write(path, formatted).map_err(|e| format!("cannot write {name}: {e}"))?
            }
            Err(diags) => {
                for d in &diags {
                    eprint!("{}", d.render(&map));
                }
                eprintln!("lode: {name} is left unchanged");
                failed = true;
            }
        }
    }
    Ok(if failed {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    })
}

/// Every `.lode` file under `dir`, sorted, skipping hidden directories.
fn lode_files(dir: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
    let mut entries: Vec<PathBuf> = std::fs::read_dir(dir)?
        .map(|e| e.map(|e| e.path()))
        .collect::<Result<_, _>>()?;
    entries.sort();
    for path in entries {
        let hidden = path
            .file_name()
            .and_then(|n| n.to_str())
            .is_some_and(|n| n.starts_with('.'));
        if path.is_dir() {
            if !hidden {
                lode_files(&path, out)?;
            }
        } else if path.extension().is_some_and(|e| e == "lode") {
            out.push(path);
        }
    }
    Ok(())
}
