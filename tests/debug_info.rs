//! Debug information (`lode build -g`): the image has DWARF sections and a
//! symbol table, the code is the same as without `-g`, and, when gdb is
//! installed and can run programs, breakpoints on Lode functions and lines
//! stop where they should.

use std::path::PathBuf;
use std::process::Command;

use latticefoundry::transform::pipeline::OptLevel;
use lode::BuildOptions;
use lode::source::{SourceFile, SourceMap};

const NAME: &str = "debug_lines.lode";

/// The program. Line numbers matter: the tests set breakpoints on them.
const PROGRAM: &str = "\
package main

import \"std/io\"

fn add(a: u32, b: u32) -> u32 {
	let sum = a +% b
	return sum
}

fn main() -> u8 {
	var total: u32 = 0
	for i in 0..4 {
		total = add(total, u32(i))
	}
	io.print(\"done\\n\")
	return u8(total & 255)
}
";

fn build(opt: OptLevel, debug: bool) -> Vec<u8> {
    let mut files = SourceMap::new();
    let root = files.add(SourceFile::new(NAME, PROGRAM));
    match lode::build(&mut files, root, &BuildOptions { opt, debug }) {
        Ok(exe) => exe.image,
        Err(e) => panic!("{NAME} failed to build: {e:?}"),
    }
}

/// The names of an ELF64 image's sections (none without a section header
/// table).
fn section_names(image: &[u8]) -> Vec<String> {
    let u16_at = |at: usize| u16::from_le_bytes([image[at], image[at + 1]]) as usize;
    let u64_at = |at: usize| u64::from_le_bytes(image[at..at + 8].try_into().unwrap()) as usize;
    assert_eq!(&image[..4], b"\x7fELF");
    let (shoff, shentsize, shnum, shstrndx) =
        (u64_at(0x28), u16_at(0x3a), u16_at(0x3c), u16_at(0x3e));
    if shnum == 0 {
        return Vec::new();
    }
    let header = |i: usize| shoff + i * shentsize;
    let strtab = u64_at(header(shstrndx) + 0x18);
    (0..shnum)
        .map(|i| {
            let start = strtab
                + u32::from_le_bytes(image[header(i)..header(i) + 4].try_into().unwrap()) as usize;
            let end = start + image[start..].iter().position(|&b| b == 0).unwrap();
            String::from_utf8_lossy(&image[start..end]).into_owned()
        })
        .collect()
}

#[test]
fn the_image_has_dwarf_and_the_same_code() {
    for opt in [OptLevel::O0, OptLevel::O2] {
        let plain = build(opt, false);
        let debug = build(opt, true);
        assert!(
            section_names(&plain).is_empty(),
            "{opt:?}: no sections without -g"
        );
        let names = section_names(&debug);
        for want in [
            ".text",
            ".symtab",
            ".debug_abbrev",
            ".debug_info",
            ".debug_line",
        ] {
            assert!(
                names.iter().any(|n| n == want),
                "{opt:?}: no {want} in {names:?}"
            );
        }
        // Past the ELF header (whose section-table fields differ), the
        // image starts with exactly the image built without `-g`.
        assert!(debug.len() > plain.len());
        assert_eq!(
            debug[64..plain.len()],
            plain[64..],
            "{opt:?}: -g changed the code"
        );
    }
}

/// Write `image` to a temporary file, removed when dropped.
struct TempExe(PathBuf);

impl TempExe {
    fn new(tag: &str, image: &[u8]) -> TempExe {
        let path = std::env::temp_dir().join(format!("lode-debug-{}-{tag}", std::process::id()));
        latticefoundry::link::write_executable(path.to_str().unwrap(), image)
            .expect("write executable");
        TempExe(path)
    }
}

impl Drop for TempExe {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

/// Run gdb in batch mode on `exe` with `commands`: its output, or `None`
/// if gdb isn't installed.
fn gdb(exe: &TempExe, commands: &[&str]) -> Option<String> {
    let mut cmd = Command::new("gdb");
    cmd.args(["-batch", "-nx"]);
    for c in commands {
        cmd.args(["-ex", c]);
    }
    let out = cmd.arg(&exe.0).output().ok()?;
    Some(format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    ))
}

/// Whether gdb ran the program to a breakpoint (it can't where tracing
/// processes isn't allowed).
fn stopped(out: &str) -> bool {
    // `Breakpoint N, function (...) at file:line`, not `Breakpoint N at
    // 0x...` (set).
    if out
        .lines()
        .any(|l| l.starts_with("Breakpoint ") && !l.contains(" at 0x"))
    {
        return true;
    }
    eprintln!("gdb couldn't run the program, not checking where it stops:\n{out}");
    false
}

#[test]
fn gdb_stops_on_lode_lines_and_functions() {
    let exe = TempExe::new("O0", &build(OptLevel::O0, true));
    let Some(out) = gdb(
        &exe,
        &[
            "break debug_lines.lode:6",
            "break 'main.main'",
            "break 'std/os.write_all'",
            "run",
            "bt",
        ],
    ) else {
        eprintln!("gdb isn't installed, skipping");
        return;
    };
    // Setting breakpoints only reads the debug information.
    assert!(out.contains("Breakpoint 1 at 0x"), "{out}");
    assert!(out.contains("file debug_lines.lode, line 6."), "{out}");
    // `main`: after its prologue, at its first statement.
    assert!(out.contains("file debug_lines.lode, line 11."), "{out}");
    // A function of the standard library, in its own file.
    assert!(out.contains("std/os/os.lode, line "), "{out}");
    if stopped(&out) {
        // `main` runs first; then the line in `add`, called from line 13.
        assert!(
            out.contains("Breakpoint 2, main.main () at debug_lines.lode:11"),
            "{out}"
        );
        assert!(!out.contains("Breakpoint 1, "), "{out}");
    }

    let Some(out) = gdb(
        &exe,
        &[
            "break debug_lines.lode:6",
            "run",
            "bt",
            "continue",
            "info line",
        ],
    ) else {
        return;
    };
    if stopped(&out) {
        assert!(
            out.contains("main.add (") && out.contains("at debug_lines.lode:6"),
            "{out}"
        );
        assert!(
            out.contains("in main.main () at debug_lines.lode:13"),
            "{out}"
        );
        // The loop calls `add` again.
        assert!(out.contains("\nBreakpoint 1, main.add ("), "{out}");
        assert!(out.contains("Line 6 of \"debug_lines.lode\""), "{out}");
    }
}

/// At `-O2`, LatticeFoundry's passes drop the instructions' lines (and
/// `add` is inlined): functions are still known, at their declarations.
#[test]
fn gdb_knows_optimized_functions() {
    let exe = TempExe::new("O2", &build(OptLevel::O2, true));
    let Some(out) = gdb(&exe, &["break 'main.main'", "run", "bt"]) else {
        eprintln!("gdb isn't installed, skipping");
        return;
    };
    assert!(out.contains("file debug_lines.lode, line 10."), "{out}");
    if stopped(&out) {
        assert!(
            out.contains("Breakpoint 1, ") && out.contains("main.main () at debug_lines.lode:10"),
            "{out}"
        );
    }
}
