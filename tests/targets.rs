//! Checking for several targets: `lode check --targets=...`, `lode targets`
//! and [`lode::check_targets`] (docs/comptime.md, Keeping dead branches from
//! rotting).

use std::process::Command;

use lode::Target;
use lode::source::{SourceFile, SourceMap};

/// Run `lode` in the repository: whether it succeeded, its standard output
/// and its standard error.
fn lode(args: &[&str]) -> (bool, String, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_lode"))
        .args(args)
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("lode runs");
    (
        out.status.success(),
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

#[test]
fn hello_world_checks_for_both_linux_targets() {
    let (ok, _, err) = lode(&[
        "check",
        "--targets=x86_64-linux,aarch64-linux",
        "tests/programs/hello_world.lode",
    ]);
    assert!(ok, "{err}");
    assert_eq!(err, "");
}

#[test]
fn std_os_reports_other_targets_once() {
    let (ok, _, err) = lode(&["check", "--targets=all", "tests/programs/hello_world.lode"]);
    assert!(!ok);
    assert_eq!(
        err.matches("error: std/os: unsupported target").count(),
        1,
        "{err}"
    );
    assert!(
        err.contains("for the target(s) wasm32, thumbv7m, avr"),
        "{err}"
    );
    assert!(
        err.contains("lode: 1 error(s), checking for x86_64-linux"),
        "{err}"
    );
}

#[test]
fn untaken_branches_are_checked_for_their_target() {
    // The host takes the branch that's fine; aarch64 takes the other one.
    let (ok, _, err) = lode(&[
        "check",
        "--targets=x86_64-linux,aarch64-linux",
        "tests/programs/comptime_target.lode",
    ]);
    assert!(!ok);
    assert!(
        err.contains("cannot find function `this_is_not_checked`"),
        "{err}"
    );
    assert!(err.contains("for the target(s) aarch64-linux"), "{err}");
    assert!(err.contains("lode: 1 error(s)"), "{err}");
}

#[test]
fn unknown_targets_and_misplaced_flags() {
    let (ok, _, err) = lode(&[
        "check",
        "--targets=pdp11",
        "tests/programs/hello_world.lode",
    ]);
    assert!(!ok);
    assert!(err.contains("unknown target `pdp11`"), "{err}");
    let (ok, _, err) = lode(&["build", "--targets=all", "tests/programs/hello_world.lode"]);
    assert!(!ok);
    assert!(err.contains("`--targets` is for `lode check`"), "{err}");
}

#[test]
fn targets_lists_what_can_be_built() {
    let (ok, out, _) = lode(&["targets"]);
    assert!(ok);
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(lines.len(), lode::target::TARGETS.len());
    assert!(lines[0].starts_with("x86_64-linux") && lines[0].ends_with("check and build"));
    assert!(lines[1].starts_with("aarch64-linux") && lines[1].ends_with("check"));
}

/// The messages for each target, checking `text` (with no imports).
fn check_each(text: &str) -> Vec<Vec<String>> {
    let mut files = SourceMap::new();
    let root = files.add(SourceFile::new("main.lode", text.to_owned()));
    let targets: Vec<&Target> = lode::target::TARGETS.iter().collect();
    lode::check_targets(&mut files, root, &targets)
        .unwrap_or_else(|_| panic!("loads"))
        .into_iter()
        .map(|diags| diags.into_iter().map(|d| d.message).collect())
        .collect()
}

#[test]
fn usize_is_the_targets() {
    // `usize` is 64, 32 or 16 bits wide, and `target` says which.
    let found = check_each(
        "package main\n\nconst BITS: u32 = target.pointer_bits\nconst WIDE: usize = 4294967295\n\n\
         fn main() -> u32 {\n\tif comptime BITS == 16 {\n\t\treturn 16\n\t}\n\treturn u32(WIDE / 2)\n}\n",
    );
    for (target, messages) in lode::target::TARGETS.iter().zip(&found) {
        if target.pointer_bits == 16 {
            assert_eq!(
                messages,
                &["`4294967295` does not fit in `usize` (0..=65535)"],
                "{}",
                target.name
            );
        } else {
            assert!(messages.is_empty(), "{}: {messages:?}", target.name);
        }
    }
}

/// A program that names no prelude item (docs/packages.md, The prelude)
/// loads nothing for it, and checks for every target: here its own `Box`
/// hides the prelude's.
#[test]
fn programs_without_prelude_names_check_for_every_target() {
    let found = check_each(
        "package main\n\nstruct Box {\n\tv: u32\n}\n\nfn open(b: Box) -> u32 {\n\treturn b.v\n}\n\n\
         fn main() -> u32 {\n\treturn open(Box{v: 7})\n}\n",
    );
    for (target, messages) in lode::target::TARGETS.iter().zip(&found) {
        assert!(messages.is_empty(), "{}: {messages:?}", target.name);
    }
}

/// `Box` without an import loads `std/alloc`, and with it `std/os`: for
/// the targets `std/os` doesn't support, that's the error, and the only
/// one.
#[test]
fn the_prelude_box_needs_std_os() {
    let found = check_each(
        "package main\n\nfn boxed() uses alloc throws(AllocError) -> u32 {\n\
         \tlet b = try Box.new(u32(7))\n\treturn b.value\n}\n\n\
         fn main() uses alloc -> u32 {\n\treturn boxed() catch _ {\n\t\treturn 1\n\t}\n}\n",
    );
    for (target, messages) in lode::target::TARGETS.iter().zip(&found) {
        if target.name.ends_with("-linux") {
            assert!(messages.is_empty(), "{}: {messages:?}", target.name);
        } else {
            assert_eq!(messages, &["std/os: unsupported target"], "{}", target.name);
        }
    }
}

/// `lode check --targets` over a program file without prelude names, for
/// the targets `std/os` doesn't support.
#[test]
fn a_program_without_imports_checks_for_small_targets() {
    let (ok, _, err) = lode(&[
        "check",
        "--targets=wasm32,thumbv7m,avr",
        "tests/programs/prelude_unused.lode",
    ]);
    assert!(ok, "{err}");
    assert_eq!(err, "");
}
