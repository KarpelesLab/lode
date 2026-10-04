//! Only code the program reaches is generated, but all of it is checked.

use latticefoundry::transform::pipeline::OptLevel;
use lode::BuildOptions;
use lode::source::{SourceFile, SourceMap};

fn source(name: &str, text: &str) -> (SourceMap, lode::source::FileId) {
    let mut files = SourceMap::new();
    let root = files.add(SourceFile::new(name, text.to_owned()));
    (files, root)
}

fn ir(name: &str, text: &str) -> String {
    let (mut files, root) = source(name, text);
    match lode::ir_text(&mut files, root, OptLevel::O0) {
        Ok(ir) => ir,
        Err(e) => panic!("{name} failed to compile: {e:?}"),
    }
}

const UNUSED: &str = "\
package main

import \"std/io\"

fn unused() {
	io.print(\"never printed\\n\")
}

fn main() -> u8 {
	io.print(\"hi\\n\")
	return 3
}
";

#[test]
fn only_reached_functions_and_strings_are_lowered() {
    let ir = ir("unused.lode", UNUSED);
    for name in ["@main.main", "@\"std/io.print\"", "@\"std/os.write_all\""] {
        assert!(ir.contains(name), "{name} missing:\n{ir}");
    }
    for name in ["@main.unused", "@\"std/io.eprint\"", "@\"std/os.write\""] {
        assert!(!ir.contains(name), "{name} lowered:\n{ir}");
    }

    let (mut files, root) = source("unused.lode", UNUSED);
    let lowered = lode::compile_ir(&mut files, root, OptLevel::O0).expect("compiles");
    let strings: Vec<&[u8]> = lowered.strings.iter().map(|(_, s)| s.as_slice()).collect();
    assert_eq!(strings, [b"hi\n".as_slice()]);
}

#[test]
fn main_is_the_entry() {
    let ir = ir("unused.lode", UNUSED);
    // `main` returns its exit status as an `i64`; everything else is
    // internal.
    assert!(ir.contains("func @main.main() -> i64 {"), "{ir}");
    assert!(ir.contains("func internal @\"std/io.print\""), "{ir}");
    assert!(!ir.contains("func @main()"), "{ir}");

    let (mut files, root) = source("unused.lode", UNUSED);
    let lowered = lode::compile_ir(&mut files, root, OptLevel::O0).expect("compiles");
    assert_eq!(lowered.entry.as_deref(), Some("main.main"));
}

#[test]
fn a_library_is_lowered_whole() {
    let lib = "\
package lib

fn twice(x: u32) -> u32 {
	return x *% 2
}

pub fn quad(x: u32) -> u32 {
	return twice(twice(x))
}

fn unused(s: str) -> u64 {
	return s.len
}
";
    let ir = ir("lib.lode", lib);
    for name in ["@lib.twice", "@lib.quad", "@lib.unused"] {
        assert!(ir.contains(name), "{name} missing:\n{ir}");
    }
}

#[test]
fn unreached_code_is_still_checked() {
    let text = "\
package main

fn unused(a: u32, b: u32) -> u32 {
	return a + b
}

fn main() -> u8 {
	return 0
}
";
    let (mut files, root) = source("unchecked.lode", text);
    match lode::build(&mut files, root, &BuildOptions::default()) {
        Err(lode::Error::Source(diags)) => {
            let messages: Vec<&str> = diags.iter().map(|d| d.message.as_str()).collect();
            assert!(
                messages
                    .iter()
                    .any(|m| m.contains("cannot prove that this addition does not overflow")),
                "{messages:?}"
            );
        }
        Err(e) => panic!("expected a proof error, got {e:?}"),
        Ok(_) => panic!("built a program with a proof error"),
    }
}

#[test]
fn only_reached_array_constants_are_emitted() {
    let src = "\
package main

const USED: [3]u16 = [1, 2, 0x0304]
const UNUSED: [2]u8 = [9, 9]

fn unused() -> u8 {
	return UNUSED[0]
}

fn main() -> u16 {
	return USED[2]
}
";
    let (mut files, root) = source("tables.lode", src);
    let lowered = lode::compile_ir(&mut files, root, OptLevel::O0).expect("compiles");
    let tables: Vec<(&[u8], u64)> = lowered
        .tables
        .iter()
        .map(|(_, bytes, align)| (bytes.as_slice(), *align))
        .collect();
    // Little-endian, each `u16` at its size, aligned for it.
    assert_eq!(tables, [([1, 0, 2, 0, 4, 3].as_slice(), 2)]);
}
