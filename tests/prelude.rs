//! The prelude (docs/packages.md, The prelude): which programs load its
//! packages, and how its names resolve.

use lode::source::{SourceFile, SourceMap};

/// The packages loading `text` (the root file) loads, in order.
fn loaded(text: &str) -> Vec<String> {
    let mut files = SourceMap::new();
    let root = files.add(SourceFile::new("main.lode", text.to_owned()));
    let (packages, diags) = lode::load::load(&mut files, root, &lode::std_root());
    assert!(diags.is_empty(), "{diags:?}");
    packages.into_iter().map(|p| p.path).collect()
}

fn loads_alloc(text: &str) -> bool {
    loaded(text).iter().any(|p| p == "std/alloc")
}

/// The error messages checking `text`, with the standard library.
fn errors(text: &str) -> Vec<String> {
    let mut files = SourceMap::new();
    let root = files.add(SourceFile::new("main.lode", text.to_owned()));
    match lode::check(&mut files, root) {
        Ok(_) => Vec::new(),
        Err(lode::Error::Source(diags)) => diags.into_iter().map(|d| d.message).collect(),
        Err(e) => panic!("{e:?}"),
    }
}

const HELLO: &str =
    "package main\n\nimport \"std/io\"\n\nfn main() {\n\tio.print(\"hello world\\n\")\n}\n";

#[test]
fn a_program_without_prelude_names_loads_nothing_more() {
    assert_eq!(loaded("package main\n\nfn main() {\n}\n"), ["main"]);
    assert!(!loads_alloc(HELLO));
}

#[test]
fn using_box_loads_std_alloc_first() {
    let paths = loaded(
        "package main\n\nfn f(b: Box[u32]) -> u32 {\n\treturn b.value\n}\n\nfn main() {\n}\n",
    );
    let alloc = paths.iter().position(|p| p == "std/alloc").expect("loaded");
    assert!(paths.iter().any(|p| p == "std/os"), "{paths:?}");
    assert_eq!(paths.last().map(String::as_str), Some("main"));
    assert!(alloc < paths.len() - 1);
}

#[test]
fn what_doesnt_use_the_prelude() {
    // Its own item, in any position.
    assert!(!loads_alloc(
        "package main\n\nfn make() -> Box {\n\treturn Box{}\n}\n\nstruct Box {\n}\n\nfn main() {\n}\n"
    ));
    // A package imported under the name.
    assert!(!loads_alloc(
        "package main\n\nimport Box \"std/io\"\n\nfn main() {\n\tBox.print(\"hi\\n\")\n}\n"
    ));
    // A member, a comment, a string.
    assert!(!loads_alloc(
        "package main\n\n// Box\nfn main() {\n\tlet s = \"Box\"\n\tlet n = s.Box\n}\n"
    ));
}

#[test]
fn the_scan_is_conservative() {
    // A local named `Box` hides the prelude's, but the scan doesn't know
    // locals; nor which `if comptime` branch a target takes.
    assert!(loads_alloc(
        "package main\n\nfn main() -> u32 {\n\tlet Box = u32(1)\n\treturn Box\n}\n"
    ));
    assert!(loads_alloc(
        "package main\n\nfn main() {\n\tif comptime target.pointer_bits == 16 {\n\t\tlet b: ?Box[u8] = none\n\t}\n}\n"
    ));
}

#[test]
fn names_hide_the_prelude() {
    // A local, then an item, then an import, before the prelude.
    assert_eq!(
        errors("package main\n\nfn main() -> u32 {\n\tlet Box = u32(1)\n\treturn Box\n}\n"),
        Vec::<String>::new()
    );
    assert_eq!(
        errors(
            "package main\n\nimport \"std/alloc\"\n\nstruct Box {\n\tv: u32\n}\n\n\
             fn main() -> u32 {\n\tlet b = Box{v: 2}\n\treturn b.v\n}\n"
        ),
        Vec::<String>::new()
    );
    // The prelude isn't part of a package's items: `alloc.Box` is, but
    // `io.Box` isn't.
    let found = errors(
        "package main\n\nimport \"std/io\"\n\nfn f(b: io.Box[u32]) {\n}\n\nfn g(b: Box[u32]) {\n}\n\nfn main() {\n}\n",
    );
    assert_eq!(found, ["package `std/io` has no `Box`"]);
}

#[test]
fn box_is_alloc_box() {
    let found = errors(
        "package main\n\nimport \"std/alloc\"\n\nfn same(sink b: Box[u32]) -> alloc.Box[u32] {\n\treturn b\n}\n\n\
         fn shown(sink b: Box[u32]) -> u32 {\n\treturn b\n}\n\nfn main() {\n}\n",
    );
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(found[0].contains("`Box[u32]`"), "{found:?}");
}
