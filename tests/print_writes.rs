//! `io.print` and `io.eprint` make one `write` each (std/io): programs run
//! under `strace`, counting their `write` calls. Skipped when `strace` isn't
//! installed or can't trace (such as in a container without ptrace).

use std::path::{Path, PathBuf};
use std::process::Command;

/// A `write` a program made: its file descriptor and the bytes, as `strace`
/// shows them (`\n` for a newline).
#[derive(Debug, PartialEq)]
struct Write {
    fd: i32,
    text: String,
}

fn w(fd: i32, text: &str) -> Write {
    Write {
        fd,
        text: text.replace('\n', "\\n"),
    }
}

/// A scratch directory for this test process.
fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("lode-print-writes-{}-{name}", std::process::id()));
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

/// Build `source` at `opt` and run it under `strace`: the `write` calls it
/// made, in order.
fn writes(dir: &Path, name: &str, source: &str, opt: &str) -> Vec<Write> {
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
        .args(["-e", "trace=write", "-s", "4096", "-o"])
        .arg(&trace)
        .arg(&exe)
        .output()
        .expect("strace runs");
    assert!(run.status.success(), "{name} {opt}: {run:?}");
    let trace = std::fs::read_to_string(&trace).expect("the trace");
    trace
        .lines()
        .filter_map(|l| l.strip_prefix("write("))
        .map(|l| {
            let (fd, rest) = l.split_once(", \"").expect("write(fd, \"...");
            let (text, _) = rest.rsplit_once("\", ").expect("\"..., n)");
            Write {
                fd: fd.parse().expect("a file descriptor"),
                text: text.to_owned(),
            }
        })
        .collect()
}

/// Check the `write` calls of `source` at `-O0` and `-O2`.
fn check(name: &str, source: &str, expected: &[Write]) {
    if !strace_works() {
        eprintln!("skipped: strace isn't available");
        return;
    }
    let dir = scratch(name);
    for opt in ["-O0", "-O2"] {
        assert_eq!(writes(&dir, name, source, opt), expected, "{name} {opt}");
    }
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn hello_world_is_one_write() {
    check(
        "hello",
        "package main\n\nimport \"std/io\"\n\nfn main() {\n\tio.print(\"hello world\\n\")\n}\n",
        &[w(1, "hello world\n")],
    );
}

const FORMATS: &str = r#"package main

import "std/io"
import "std/os"

struct Point {
	x: i32
	y: i32
}

impl io.Format for Point {
	fn format[W: io.Writer](self, inout w: W) throws(os.Error) {
		try io.write_fmt(&w, "({}, {})", self.x, self.y)
	}
}

fn main() {
	let x: u32 = 7
	let y: i8 = -3
	let name = "lode"
	io.print("x = {}, y = {}, ok = {}, name = {}\n", x, y, x > 3, name)
	io.print("{}", name)
	io.print("{}\n", x)
	io.print("{} {}\n", i64(-9223372036854775808), u64(18446744073709551615))
	io.print("p = {}\n", Point{x: 1, y: -2})
	io.print("{{braces}} {{{}}}\n", x)
	io.print("{{no arguments}}\n")
	io.print("")
	io.eprint("error: {} at {}\n", name, x)
}
"#;

#[test]
fn each_print_is_one_write() {
    check(
        "formats",
        FORMATS,
        &[
            w(1, "x = 7, y = -3, ok = true, name = lode\n"),
            w(1, "lode"),
            w(1, "7\n"),
            w(1, "-9223372036854775808 18446744073709551615\n"),
            w(1, "p = (1, -2)\n"),
            w(1, "{braces} {7}\n"),
            w(1, "{no arguments}\n"),
            w(2, "error: lode at 7\n"),
        ],
    );
}

/// A print longer than the buffer (`io.PRINT_BUF_SIZE`, 256 bytes) is
/// written each time the buffer is full, then at the end.
#[test]
fn a_long_print_is_written_a_buffer_at_a_time() {
    let long = "a".repeat(600);
    let source = format!(
        "package main\n\nimport \"std/io\"\n\nfn main() {{\n\tlet s = \"{long}\"\n\tio.print(\"[{{}}]\\n\", s)\n}}\n"
    );
    let all = format!("[{long}]\n");
    check(
        "long",
        &source,
        &[w(1, &all[..256]), w(1, &all[256..512]), w(1, &all[512..])],
    );
}
