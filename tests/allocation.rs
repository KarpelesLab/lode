//! Allocation (docs/allocation.md, M8b): what it costs, in bytes, system
//! calls and stack. A program that doesn't allocate is the same program
//! whether or not it imports `std/alloc` or declares `uses alloc`; the
//! root allocator maps memory with `mmap` and gives large blocks back with
//! `munmap` (checked under `strace`, skipped when it can't trace); and a
//! chain of boxes is destroyed with a bounded stack.

use std::path::{Path, PathBuf};
use std::process::Command;

use latticefoundry::transform::pipeline::OptLevel;
use lode::source::{SourceFile, SourceMap};
use lode::{BuildOptions, Executable};

fn build(name: &str, text: &str, opt: OptLevel) -> Executable {
    let mut files = SourceMap::new();
    let root = files.add(SourceFile::new(name, text.to_owned()));
    let options = BuildOptions {
        opt,
        ..BuildOptions::default()
    };
    match lode::build(&mut files, root, &options) {
        Ok(exe) => exe,
        Err(e) => panic!("{name} failed to build: {e:?}"),
    }
}

const HELLO: &str =
    "package main\n\nimport \"std/io\"\n\nfn main() {\n\tio.print(\"hello world\\n\")\n}\n";

/// Importing `std/alloc` and declaring `uses alloc` cost nothing in a
/// program that doesn't allocate: no hidden parameter, no allocator.
#[test]
fn not_allocating_costs_nothing() {
    let with_alloc = "package main\n\nimport \"std/alloc\"\nimport \"std/io\"\n\nfn greet() uses alloc {\n\tio.print(\"hello world\\n\")\n}\n\nfn main() uses alloc {\n\tgreet()\n}\n";
    for opt in [OptLevel::O0, OptLevel::O2] {
        let plain = build("hello.lode", HELLO, opt);
        let alloc = build("hello_alloc.lode", with_alloc, opt);
        if opt == OptLevel::O2 {
            assert_eq!(plain.image.len(), 577, "hello world's size");
            assert_eq!(plain.image, alloc.image, "{opt:?}");
        }
        assert!(
            !alloc
                .stack
                .functions()
                .iter()
                .any(|f| f.name.contains("std/alloc")),
            "{opt:?}: {}",
            alloc.stack
        );
    }
}

/// A chain of boxes is destroyed by a loop: the call graph has no
/// recursion, so the program has a stack bound.
#[test]
fn a_chain_of_boxes_has_a_stack_bound() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/programs/alloc_chain.lode"
    );
    let text = std::fs::read_to_string(path).expect("alloc_chain.lode");
    for opt in [OptLevel::O0, OptLevel::O2] {
        let exe = build("alloc_chain.lode", &text, opt);
        let bound = exe.stack.bound().expect("a bounded stack");
        assert!(bound.bytes < 4096, "{opt:?}: {}", exe.stack);
    }
}

/// A scratch directory for this test process.
fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("lode-alloc-{}-{name}", std::process::id()));
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

/// Build `source` at `opt` and run it under `strace`: its `mmap`,
/// `munmap` and `mremap` calls, each shortened to its name and length
/// (`mmap 65536`, `munmap 8192`).
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
        .args(["-e", "trace=mmap,munmap,mremap", "-o"])
        .arg(&trace)
        .arg(&exe)
        .output()
        .expect("strace runs");
    assert!(run.status.success(), "{name} {opt}: {run:?}");
    let trace = std::fs::read_to_string(&trace).expect("the trace");
    trace
        .lines()
        .filter_map(|l| {
            let (call, args) = l.split_once('(')?;
            let args: Vec<&str> = args.split(", ").collect();
            let len = match call {
                "mmap" | "munmap" => args.get(1)?,
                "mremap" => args.get(2)?,
                _ => return None,
            };
            let len: String = len.chars().take_while(char::is_ascii_digit).collect();
            Some(format!("{call} {len}"))
        })
        .collect()
}

#[test]
fn the_heap_maps_chunks_and_large_blocks() {
    if !strace_works() {
        eprintln!("skipped: strace can't trace here");
        return;
    }
    // Small boxes come from one 64 KiB chunk, used again after they're
    // freed; a large one is a mapping of its own, unmapped when it's
    // freed.
    let source = "package main\n\nimport \"std/alloc\"\n\n\
        fn run() uses alloc throws(AllocError) {\n\
        \tfor i in 0..10000 {\n\t\tlet b = try alloc.Box.new(u64(i))\n\t}\n\
        \tlet big = try alloc.Box[[10000]u8].new([0; 10000])\n\
        \tlet small = try alloc.Box.new(u32(1))\n}\n\n\
        fn main() uses alloc -> u8 {\n\trun() catch _ {\n\t\treturn 1\n\t}\n\treturn 0\n}\n";
    let dir = scratch("heap");
    for opt in ["-O0", "-O2"] {
        let found = calls(&dir, "heap", source, opt);
        assert_eq!(found, ["mmap 65536", "mmap 10000", "munmap 10000"], "{opt}");
    }
    let _ = std::fs::remove_dir_all(&dir);
}
