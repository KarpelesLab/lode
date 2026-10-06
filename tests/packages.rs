//! Structs, enums and methods across packages, with a package of the
//! test's own as the standard library.

use std::path::{Path, PathBuf};

use latticefoundry::codegen::CodegenOptions;
use latticefoundry::link::{self, ImageOptions};
use latticefoundry::target::x86_64;
use latticefoundry::transform::pipeline::{self, OptLevel};
use lode::source::{SourceFile, SourceMap};

const GEO: &str = "\
package geo

pub struct Point {
	pub x: i32
	pub y: i32
}

/// A public struct with a private field.
pub struct Counter {
	pub step: u8
	count: u32
}

pub fn Counter.new(step: u8) -> Counter {
	return Counter{step: step, count: 0}
}

pub fn Counter.bump(inout self) {
	self.count +%= u32(self.step)
}

pub fn Counter.total(self) -> u32 {
	return self.count
}

struct Secret {
	v: u8
}

pub fn origin() -> Point {
	return Point{x: 0, y: 0}
}

pub fn shift(p: Point, dx: i32) -> Point {
	return Point{x: p.x +% dx, y: p.y}
}

pub enum Shape {
	circle(center: Point, radius: u8)
	dot
}

pub enum Level: u8 {
	low = 1
	high = 9
}

enum Hidden {
	a
}

pub fn unit() -> Shape {
	return Shape.circle(origin(), 1)
}

pub fn Point.new(x: i32, y: i32) -> Point {
	return Point{x: x, y: y}
}

pub fn Point.sum(self) -> i32 {
	return self.x +% self.y
}

pub fn Point.flip(inout self) {
	self.x = 0 -% self.x
}

fn Point.secret(self) -> i32 {
	return 0
}

fn Point.hidden() -> Point {
	return origin()
}

pub fn Shape.radius(self) -> u8 {
	match self {
		circle(_, r) => return r
		dot => return 0
	}
}
";

/// A standard library root holding `std/geo` and the packages `more`
/// (name and source), unique to `name`.
fn std_root(name: &str, more: &[(&str, &str)]) -> PathBuf {
    let root = std::env::temp_dir().join(format!("lode-packages-{}-{name}", std::process::id()));
    for (pkg, src) in std::iter::once(("geo", GEO)).chain(more.iter().copied()) {
        let dir = root.join(pkg);
        std::fs::create_dir_all(&dir).expect("create the package directory");
        std::fs::write(dir.join(format!("{pkg}.lode")), src).expect("write the package");
    }
    root
}

/// Load and check `main` against the test library: the program, or the
/// error messages.
fn check(name: &str, main: &str) -> Result<lode::sema::Program, Vec<String>> {
    check_with(name, main, &[])
}

/// [`check`], with the packages `more` in the library too.
fn check_with(
    name: &str,
    main: &str,
    more: &[(&str, &str)],
) -> Result<lode::sema::Program, Vec<String>> {
    let root_dir = std_root(name, more);
    let mut files = SourceMap::new();
    let root = files.add(SourceFile::new(format!("{name}.lode"), main.to_owned()));
    let (packages, mut diags) = lode::load::load(&mut files, root, &root_dir);
    let _ = std::fs::remove_dir_all(&root_dir);
    if diags.is_empty() {
        let (program, sema_diags) = lode::sema::check(&packages, lode::target::Target::host());
        if sema_diags.is_empty() {
            return Ok(program);
        }
        diags = sema_diags;
    }
    Err(diags.into_iter().map(|d| d.message).collect())
}

/// Build and run a checked program; its exit status.
fn run(program: &lode::sema::Program, name: &str) -> i32 {
    let mut lowered = lode::lower::lower(program, name);
    pipeline::optimize(&mut lowered.module, OptLevel::O2);
    let compiled =
        x86_64::compile_module_with(&lowered.module, &lowered.syms, &CodegenOptions::default());
    assert!(
        lowered.strings.is_empty(),
        "the test has no strings to emit"
    );
    let options = ImageOptions {
        entry: lowered.entry.clone().expect("an entry"),
        ..ImageOptions::default()
    };
    let image = link::link_executable(vec![compiled.object], &options).expect("links");
    let path =
        std::env::temp_dir().join(format!("lode-packages-{}-{name}.exe", std::process::id()));
    let path_str = path.to_str().expect("utf-8 temp path");
    link::write_executable(path_str, &image).expect("write executable");
    // A freshly written executable can briefly be busy (ETXTBSY) while
    // another test thread forks; retry a few times, as tests/programs.rs does.
    let status = (0..50)
        .find_map(
            |_| match std::process::Command::new(Path::new(&path)).status() {
                Ok(s) => Some(s),
                Err(e) if e.raw_os_error() == Some(26) => {
                    std::thread::sleep(std::time::Duration::from_millis(5));
                    None
                }
                Err(e) => panic!("running {name}: {e}"),
            },
        )
        .expect("executable stayed busy");
    let _ = std::fs::remove_file(&path);
    status.code().expect("exited normally")
}

#[test]
fn a_public_struct_is_used_from_another_package() {
    let main = "\
package main

import \"std/geo\"

// The same name and fields, but another type.
struct Point {
	x: i32
	y: i32
}

fn main() -> i32 {
	let p = geo.shift(geo.Point{x: 1, y: 2}, 4)
	var q: geo.Point = geo.origin()
	q.y = p.x
	let mine = Point{x: q.y, y: p.y}
	return mine.x +% mine.y
}
";
    let program = check("public", main).expect("checks");
    if cfg!(all(target_arch = "x86_64", target_os = "linux")) {
        assert_eq!(run(&program, "public"), 7);
    }
}

#[test]
fn a_public_enum_is_used_from_another_package() {
    let main = "\
package main

import \"std/geo\"

fn radius(s: geo.Shape) -> u8 {
	match s {
		circle(_, r) => return r
		dot => return 0
	}
}

// `_` on another package's enum is not linted: it handles the variants
// that package may add.
fn is_dot(s: geo.Shape) -> bool {
	match s {
		dot => return true
		_ => return false
	}
}

fn main() -> u8 {
	let big = geo.Shape.circle(geo.Point{x: 0, y: 0}, 5)
	let level = geo.Level(9) ?? geo.Level.low
	if is_dot(big) || !is_dot(geo.Shape.dot) || level != geo.Level.high {
		return 100
	}
	return radius(big) +% radius(geo.unit()) +% u8(level)
}
";
    // `check` fails on any diagnostic, warnings too.
    let program = check("enums", main).expect("checks");
    if cfg!(all(target_arch = "x86_64", target_os = "linux")) {
        assert_eq!(run(&program, "enums"), 15);
    }
    let errors = check(
        "private-enum",
        "package main\n\nimport \"std/geo\"\n\nfn main() {\n\tlet h = geo.Hidden.a\n}\n",
    )
    .expect_err("fails to check");
    assert_eq!(errors, ["`Hidden` is private to package `std/geo`"]);
}

#[test]
fn private_structs_and_other_packages_types() {
    let main = "\
package main

import \"std/geo\"

struct Point {
	x: i32
	y: i32
}

fn main() {
	let s = geo.Secret{v: 1}
	let t: geo.Secret = s
	let p: Point = geo.origin()
	let q: geo.Nope = p
	let r = geo.origin{x: 1}
}
";
    let errors = check("private", main).expect_err("fails to check");
    let expected = [
        "`Secret` is private to package `std/geo`",
        "`Secret` is private to package `std/geo`",
        "expected `Point`, found `geo.Point`",
        "package `std/geo` has no `Nope`",
        "`geo.origin` is not a type",
    ];
    assert_eq!(errors, expected);
}

#[test]
fn methods_of_another_packages_types() {
    let main = "\
package main

import \"std/geo\"

fn main() -> i32 {
	var p = geo.Point.new(3, 4)
	p.flip()
	let s = geo.Shape.circle(p, 5)
	return p.sum() +% i32(s.radius()) +% i32(geo.unit().radius())
}
";
    let program = check("methods", main).expect("checks");
    if cfg!(all(target_arch = "x86_64", target_os = "linux")) {
        assert_eq!(run(&program, "methods"), 7);
    }
    let errors = check(
        "private-methods",
        "package main\n\nimport \"std/geo\"\n\nfn geo.Point.mine(self) {\n}\n\n\
         fn main() -> i32 {\n\tlet p = geo.origin()\n\tlet q = geo.Point.hidden()\n\treturn p.secret()\n}\n",
    )
    .expect_err("fails to check");
    let expected = [
        "the methods of `geo.Point` can only be declared in package `std/geo`, which declares it",
        "`geo.Point.hidden` is private to package `std/geo`",
        "`geo.Point.secret` is private to package `std/geo`",
    ];
    assert_eq!(errors, expected);
}

const SHAPES: &str = "\
package shapes

import \"std/geo\"

/// A trait of this package, implemented here for another package's type.
pub trait Area {
	fn area(self) -> i32

	fn double(self) -> i32 {
		return self.area() *| 2
	}
}

trait Secret {
	fn s(self)
}

impl Secret for geo.Point {
	fn s(self) {
	}
}

impl Area for geo.Point {
	fn area(self) -> i32 {
		return self.x *| self.y
	}
}

pub fn total[T: Area](a: T, b: T) -> i32 {
	return a.area() +| b.area()
}
";

#[test]
fn traits_across_packages() {
    let main = "\
package main

import \"std/geo\"
import \"std/shapes\"

struct Square {
	side: i32
}

// The type's package implements another package's trait.
impl shapes.Area for Square {
	fn area(self) -> i32 {
		return self.side *| self.side
	}
}

fn sum[T: shapes.Area](x: T) -> i32 {
	return x.double()
}

fn main() -> i32 {
	let p = geo.Point.new(2, 3)
	let s = Square{side: 2}
	return p.area() +| sum(s) +| shapes.total(s, s) +| shapes.Area.area(p)
}
";
    let program = check_with("traits", main, &[("shapes", SHAPES)]).expect("checks");
    if cfg!(all(target_arch = "x86_64", target_os = "linux")) {
        assert_eq!(run(&program, "traits"), 6 + 8 + 8 + 6);
    }
    let errors = check_with(
        "traits-coherence",
        "package main\n\nimport \"std/geo\"\nimport \"std/shapes\"\n\n\
         impl shapes.Area for geo.Shape {\n\tfn area(self) -> i32 {\n\t\treturn 0\n\t}\n}\n\n\
         fn f[T: shapes.Secret](x: T) {\n}\n\n\
         impl shapes.Area for geo.Point {\n\tfn area(self) -> i32 {\n\t\treturn 0\n\t}\n}\n\n\
         fn main() {\n\tgeo.origin().s()\n}\n",
        &[("shapes", SHAPES)],
    )
    .expect_err("fails to check");
    let expected = [
        "`impl shapes.Area for geo.Shape` must be in the package of `shapes.Area` (`std/shapes`) or of `geo.Shape` (`std/geo`)",
        "`impl shapes.Area for geo.Point` must be in the package of `shapes.Area` (`std/shapes`) or of `geo.Point` (`std/geo`)",
        "`Secret` is private to package `std/shapes`",
        "`geo.Point` has no method `s`",
    ];
    assert_eq!(errors, expected);
}

#[test]
fn private_fields() {
    let main = "\
package main

import \"std/geo\"

fn main() -> u32 {
	var c = geo.Counter.new(3)
	c.bump()
	c.step = 4
	c.bump()
	// `==` compares the private fields too, without showing them.
	if c == geo.Counter.new(4) {
		return 100
	}
	return c.total() +% u32(c.step)
}
";
    let program = check("private-fields", main).expect("checks");
    if cfg!(all(target_arch = "x86_64", target_os = "linux")) {
        assert_eq!(run(&program, "private-fields"), 11);
    }
    let errors = check(
        "private-fields-errors",
        "package main\n\nimport \"std/geo\"\n\n\
         fn main() -> u32 {\n\tvar c = geo.Counter{step: 1, count: 2}\n\
         \tvar d = geo.Counter.new(1)\n\td.count = 5\n\td.count += 1\n\
         \tbump(&d.count)\n\treturn d.count\n}\n\n\
         fn bump(inout n: u32) {\n}\n",
    )
    .expect_err("fails to check");
    let expected = [
        "`geo.Counter` has private fields, so it can only be built in package `std/geo`",
        "`count` is a private field of `geo.Counter`",
        "`count` is a private field of `geo.Counter`",
        "`count` is a private field of `geo.Counter`",
        "`count` is a private field of `geo.Counter`",
    ];
    assert_eq!(errors, expected);
}

const STORE: &str = "\
package store

/// Up to 8 bytes, of which only the first `n` are ever written.
pub struct Bytes {
	@uninit b: [8]u8
	n: usize
}

pub fn Bytes.new() -> Bytes {
	unsafe {
		return Bytes{n: 0}
	}
}

pub fn Bytes.push(inout self, x: u8) {
	if self.n < 8 {
		self.b[self.n] = x
		self.n += 1
	}
}

pub fn Bytes.sum(self) -> u8 {
	var s: u8 = 0
	for i in 0..self.n {
		if i < 8 {
			s +%= self.b[i]
		}
	}
	return s
}

pub fn Bytes.safe() -> Bytes {
	return Bytes{n: 0}
}

pub struct Wrong {
	pub @uninit a: [4]u8
	@uninit b: u8
}

/// Computed while compiling: the bytes left out are zeros there.
pub const START: Bytes = make()

fn make() -> Bytes {
	var b = Bytes.new()
	b.push(7)
	return b
}
";

#[test]
fn uninit_fields() {
    let main = "\
package main

import \"std/store\"

fn main() -> u8 {
	var b = store.Bytes.new()
	b.push(30)
	b.push(12)
	let copy = b
	var c = store.START
	c.push(1)
	return copy.sum() +% c.sum()
}
";
    let errors = check_with("uninit", main, &[("store", STORE)]).expect_err("fails to check");
    let expected = [
        "an `@uninit` field can't be `pub`",
        "an `@uninit` field must be an array of integers, not `u8`",
        "missing field `b` in this `store.Bytes`",
    ];
    assert_eq!(errors, expected);
    let store = STORE
        .split("pub fn Bytes.safe")
        .next()
        .expect("text")
        .to_owned()
        + &STORE[STORE.find("/// Computed").expect("text")..];
    let program = check_with("uninit-ok", main, &[("store", &store)]).expect("checks");
    if cfg!(all(target_arch = "x86_64", target_os = "linux")) {
        assert_eq!(run(&program, "uninit"), 50);
    }
    let errors = check_with(
        "uninit-eq",
        "package main\n\nimport \"std/store\"\n\n\
         fn main() {\n\tlet same = store.Bytes.new() == store.Bytes.new()\n}\n",
        &[("store", &store)],
    )
    .expect_err("fails to check");
    assert_eq!(errors, ["`==` can't compare values of type `store.Bytes`"]);
}
