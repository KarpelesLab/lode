//! Stack usage reports from `lode::build`. These check the shape of the
//! report, not byte counts, which change with code generation.

use latticefoundry::transform::pipeline::OptLevel;
use lode::source::{SourceFile, SourceMap};
use lode::stack::{StackBoundError, StackReport, describe_unbounded};
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

fn hello_world(opt: OptLevel) -> StackReport {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/programs/hello_world.lode"
    );
    let text = std::fs::read_to_string(path).expect("hello_world.lode");
    build("hello_world.lode", &text, opt).stack
}

#[test]
fn a_program_without_recursion_has_a_bound() {
    for opt in [OptLevel::O0, OptLevel::O2] {
        let stack = hello_world(opt);
        let bound = stack.bound().expect("hello world has a stack bound");
        let entry = stack
            .function(stack.entry())
            .expect("the entry is in the report");
        assert!(bound.bytes > 0);
        assert!(bound.bytes >= entry.frame_size, "{stack}");
        assert_eq!(bound.path.first().map(String::as_str), Some(stack.entry()));
        // The deepest path's frames add up to the bound.
        let sum: u64 = bound
            .path
            .iter()
            .map(|f| {
                stack
                    .function(f)
                    .expect("a function on the path")
                    .frame_size
            })
            .sum();
        assert_eq!(sum, bound.bytes, "{stack}");
    }
}

#[test]
fn the_report_uses_lode_names() {
    let stack = hello_world(OptLevel::O0);
    let names: Vec<&str> = stack.functions().iter().map(|f| f.name.as_str()).collect();
    // The entry is the program's `main`, under its Lode name.
    assert_eq!(stack.entry(), "main.main");
    assert_eq!(names.first(), Some(&stack.entry()));
    for name in ["main.main", "std/os.write_all"] {
        assert!(names.contains(&name), "{name} missing from {names:?}");
    }
    let text = stack.to_string();
    assert!(text.contains("std/os.write_all"), "{text}");
    assert!(text.contains("worst-case stack depth: "), "{text}");
}

const RECURSIVE: &str = "\
package main

fn fib(n: u32) -> u32 {
	if n < 2 {
		return n
	}
	return fib(n -% 1) +% fib(n -% 2)
}

fn main() -> u8 {
	return u8(fib(10) & 255)
}
";

#[test]
fn recursion_has_no_bound() {
    for opt in [OptLevel::O0, OptLevel::O2] {
        let stack = build("fib.lode", RECURSIVE, opt).stack;
        let err = stack.bound().expect_err("fib has no stack bound");
        let StackBoundError::Recursion { cycle } = &err else {
            panic!("expected recursion, got {err:?}");
        };
        assert!(cycle.iter().any(|f| f == "main.fib"), "{cycle:?}");
        assert!(describe_unbounded(&err).contains("main.fib"));
        let text = stack.to_string();
        assert!(
            text.contains("no bound") && text.contains("main.fib"),
            "{text}"
        );
    }
}
