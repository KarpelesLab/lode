//! `os.Fd` owns a file descriptor and closes it once, when it's destroyed
//! or by `os.close` (docs/allocation.md, M8a): programs run under `strace`,
//! with their `openat`, `close` and `write` calls checked in order.
//! Skipped when `strace` isn't installed or can't trace (such as in a
//! container without ptrace).

use std::path::{Path, PathBuf};
use std::process::Command;

/// A scratch directory for this test process.
fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("lode-fds-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("scratch directory");
    dir
}

/// Whether `strace` can trace a program here.
fn strace_works() -> bool {
    Command::new("strace")
        .args(["-o", "/dev/null", "true"])
        .output()
        .is_ok_and(|o| o.status.success())
}

/// Build `source` at `opt` and run it under `strace`: its `openat`,
/// `close` and `write` calls, each shortened to what the test compares
/// (`open data = 3`, `close 3 = 0`, `write 1 "x"`).
fn calls(dir: &Path, name: &str, source: &str, opt: &str) -> Vec<String> {
    let src = dir.join(format!("{name}.lode"));
    std::fs::write(&src, source).expect("write the program");
    let exe = dir.join(format!("{name}{opt}"));
    let out = Command::new(env!("CARGO_BIN_EXE_lode"))
        .arg("build")
        .arg(&src)
        .arg(opt)
        .arg("-o")
        .arg(&exe)
        .output()
        .expect("lode runs");
    assert!(
        out.status.success(),
        "{name} {opt}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let trace = dir.join(format!("{name}{opt}.trace"));
    let run = Command::new("strace")
        .args(["-e", "trace=openat,close,write", "-o"])
        .arg(&trace)
        .arg(&exe)
        .current_dir(dir)
        .output()
        .expect("strace runs");
    assert!(run.status.success(), "{name} {opt}: {run:?}");
    let trace = std::fs::read_to_string(&trace).expect("the trace");
    trace
        .lines()
        .filter_map(|l| {
            let (call, result) = l.rsplit_once(" = ")?;
            let result = result.split_whitespace().next()?;
            if let Some(args) = call.strip_prefix("openat(") {
                let path = args.split('"').nth(1)?;
                return Some(format!("open {path} = {result}"));
            }
            if let Some(args) = call.strip_prefix("close(") {
                return Some(format!(
                    "close {} = {result}",
                    args.trim().trim_end_matches(')')
                ));
            }
            let args = call.strip_prefix("write(")?;
            let (fd, rest) = args.split_once(", ")?;
            let text = rest.split('"').nth(1)?;
            Some(format!("write {fd} \"{text}\""))
        })
        .collect()
}

/// Check the calls of `source` at `-O0` and `-O2`.
fn check(name: &str, source: &str, expected: &[&str]) {
    if !strace_works() {
        eprintln!("strace can't trace here: skipped");
        return;
    }
    let dir = scratch(name);
    for opt in ["-O0", "-O2"] {
        assert_eq!(calls(&dir, name, source, opt), expected, "{name} {opt}");
    }
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn each_descriptor_is_closed_once() {
    let source = r#"package main

import "std/io"
import "std/os"

enum Fail {
	open
}

// Each file is closed at the end of the block that owns it.
fn write_file() throws(os.Error) {
	let f = try os.open("data", os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o644)
	try io.File.from_fd(f.fd).write("abc")
}

// `os.close` closes it, and reports an error: nothing closes it again.
fn read_file() throws(os.Error) {
	let f = try os.open("data", os.O_RDONLY, 0)
	var buf: [8]u8 = [0; 8]
	let n = try io.File.from_fd(f.fd).read(&buf)
	try io.stdout().write_bytes(buf[..n])
	try os.close(f)
}

// One per iteration.
fn reopen() throws(os.Error) {
	for i in 0..2 {
		let f = try os.open("data", os.O_RDONLY, 0)
	}
}

// `errdefer` moves the first file to close it when the second fails;
// on success, it's returned instead.
fn both(second: str) throws(os.Error) -> os.Fd {
	let a = try os.open("data", os.O_RDONLY, 0)
	errdefer os.close(a) catch _ {}
	let b = try os.open(second, os.O_RDONLY, 0)
	return a
}

fn main() -> i32 {
	write_file() catch _ {
		return 1
	}
	read_file() catch _ {
		return 2
	}
	reopen() catch _ {
		return 3
	}
	match both("missing") {
		ok(f) => io.print("?")
		err(e) => io.print("!")
	}
	let kept = both("data") catch _ {
		return 4
	}
	io.print(".")
	return 0
}
"#;
    check(
        "each_descriptor_is_closed_once",
        source,
        &[
            "open data = 3",
            "write 3 \"abc\"",
            "close 3 = 0",
            "open data = 3",
            "write 1 \"abc\"",
            "close 3 = 0",
            "open data = 3",
            "close 3 = 0",
            "open data = 3",
            "close 3 = 0",
            "open data = 3",
            "open missing = -1",
            "close 3 = 0",
            "write 1 \"!\"",
            "open data = 3",
            "open data = 4",
            "close 4 = 0",
            "write 1 \".\"",
            "close 3 = 0",
        ],
    );
}

#[test]
fn a_boxed_descriptor_is_closed_once() {
    let source = r#"package main

import "std/alloc"
import "std/io"
import "std/os"

// A box owns its descriptor: destroying the box closes it, then frees it.
fn boxed() uses alloc throws(AllocError) {
	let f = os.open("/dev/null", os.O_RDONLY, 0) catch _ {
		return
	}
	let b = try alloc.Box.new(f)
	io.print("boxed")
	let moved = b
	io.print(".")
}

fn main() uses alloc -> i32 {
	boxed() catch _ {
		return 1
	}
	io.print("!")
	return 0
}
"#;
    check(
        "a_boxed_descriptor_is_closed_once",
        source,
        &[
            "open /dev/null = 3",
            "write 1 \"boxed\"",
            "write 1 \".\"",
            "close 3 = 0",
            "write 1 \"!\"",
        ],
    );
}
