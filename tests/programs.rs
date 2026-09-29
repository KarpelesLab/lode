//! End-to-end tests over `tests/programs/*.lode`.
//!
//! Each program starts with comment lines saying what must happen:
//!
//! - `// exit: N`: it compiles, and running it exits with status `N`. It is
//!   built and run at `-O0` and `-O2`.
//! - `// error: text`: compiling fails with an error whose message contains
//!   `text` (one line per expected error; every error must be listed).

use std::path::{Path, PathBuf};

use latticefoundry::transform::pipeline::OptLevel;
use lode::source::SourceFile;

enum Expect {
    Exit(i32),
    Errors(Vec<String>),
}

fn expectation(text: &str) -> Expect {
    let mut exit = None;
    let mut errors = Vec::new();
    for line in text.lines().take_while(|l| l.starts_with("//")) {
        if let Some(code) = line.strip_prefix("// exit:") {
            exit = Some(code.trim().parse().expect("exit status"));
        } else if let Some(msg) = line.strip_prefix("// error:") {
            errors.push(msg.trim().to_owned());
        }
    }
    match exit {
        Some(code) => Expect::Exit(code),
        None => {
            assert!(!errors.is_empty(), "no `// exit:` or `// error:` header");
            Expect::Errors(errors)
        }
    }
}

fn programs() -> Vec<PathBuf> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/programs");
    let mut paths: Vec<PathBuf> = std::fs::read_dir(dir)
        .expect("tests/programs")
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().is_some_and(|e| e == "lode"))
        .collect();
    paths.sort();
    paths
}

fn run_image(image: &[u8], name: &str) -> i32 {
    let path = std::env::temp_dir().join(format!("lode-test-{}-{name}", std::process::id()));
    let path_str = path.to_str().expect("utf-8 temp path");
    latticefoundry::link::write_executable(path_str, image).expect("write executable");
    // A freshly written executable can briefly be busy (ETXTBSY) under
    // parallel tests; retry a few times.
    let status = (0..50)
        .find_map(|_| match std::process::Command::new(&path).status() {
            Ok(s) => Some(s),
            Err(e) if e.raw_os_error() == Some(26) => {
                std::thread::sleep(std::time::Duration::from_millis(5));
                None
            }
            Err(e) => panic!("running {name}: {e}"),
        })
        .expect("executable stayed busy");
    let _ = std::fs::remove_file(&path);
    status.code().expect("exited normally")
}

#[test]
fn programs_behave_as_declared() {
    let mut failures = Vec::new();
    for path in programs() {
        let name = path.file_stem().unwrap().to_string_lossy().into_owned();
        let text = std::fs::read_to_string(&path).expect("read program");
        let file = SourceFile::new(path.display().to_string(), text);
        match expectation(&file.text) {
            Expect::Exit(expected) => {
                if !cfg!(all(target_arch = "x86_64", target_os = "linux")) {
                    continue;
                }
                for opt in [OptLevel::O0, OptLevel::O2] {
                    match lode::build_executable(&file, opt) {
                        Ok(image) => {
                            let code = run_image(&image, &format!("{name}-{opt:?}"));
                            if code != expected {
                                failures.push(format!(
                                    "{name} ({opt:?}): exited {code}, expected {expected}"
                                ));
                            }
                        }
                        Err(lode::Error::Source(diags)) => {
                            let rendered: String = diags.iter().map(|d| d.render(&file)).collect();
                            failures
                                .push(format!("{name} ({opt:?}): failed to compile:\n{rendered}"));
                        }
                        Err(lode::Error::Backend(msg)) => {
                            failures.push(format!("{name} ({opt:?}): {msg}"))
                        }
                    }
                }
            }
            Expect::Errors(expected) => match lode::check(&file) {
                Ok(_) => failures.push(format!("{name}: compiled, but errors were expected")),
                Err(lode::Error::Source(diags)) => {
                    let messages: Vec<&str> = diags.iter().map(|d| d.message.as_str()).collect();
                    for want in &expected {
                        if !messages.iter().any(|m| m.contains(want.as_str())) {
                            failures
                                .push(format!("{name}: missing error `{want}`; got {messages:#?}"));
                        }
                    }
                    if messages.len() != expected.len() {
                        failures.push(format!(
                            "{name}: expected {} errors, got {}: {messages:#?}",
                            expected.len(),
                            messages.len()
                        ));
                    }
                }
                Err(lode::Error::Backend(msg)) => failures.push(format!("{name}: {msg}")),
            },
        }
    }
    assert!(failures.is_empty(), "\n{}", failures.join("\n"));
}
