//! The prelude: the standard library's items every package names without
//! an import (docs/packages.md, The prelude).
//!
//! **Resolution.** A prelude name is the last place an unqualified name is
//! looked up: a local, a type parameter, an item of the package (in any of
//! its files) or a built-in name (`Ordering`, `AllocError`, the built-in
//! traits) comes first, and a file that imports a package under the name
//! doesn't see the prelude's item either. `alloc.Box` and the prelude's
//! `Box` are the same type. The prelude isn't part of any package's
//! items: `pkg.Box` is only `Box` if package `pkg` declares it.
//!
//! **Laziness.** A program pays for the prelude's packages only when it
//! uses them: [`crate::load`] loads an entry's package only if some loaded
//! file may use its name, decided before checking, from the file's tokens
//! ([`uses`]). A file may use a prelude name when the name is one of its
//! identifiers that doesn't follow a `.` (which makes it a member, as in
//! `alloc.Box` or `p.Box`), unless the file imports a package under that
//! name or its package declares an item of that name outside `if comptime`
//! (so it never reaches the prelude). Every other occurrence counts, even a
//! local variable's or a field's name or one in an `if comptime` branch
//! that isn't taken: the scan may load a package a program doesn't need,
//! never miss one it needs, and gives the same answer for every target.
//!
//! **Adding a name** is one line in [`PRELUDE`]: its package is then
//! loaded by the programs that use the name, and the checker finds the
//! item there.

use crate::ast;
use crate::lex::{P, Tok, Token};
use crate::source::Span;

/// One name of the prelude: the public item `item` of the standard
/// package `package`.
#[derive(Debug)]
pub struct Entry {
    pub name: &'static str,
    pub package: &'static str,
    pub item: &'static str,
}

/// The prelude. (`AllocError`, `Ordering` and the built-in traits are
/// built into the compiler, so they need no package.)
pub const PRELUDE: &[Entry] = &[
    Entry {
        name: "Box",
        package: "std/alloc",
        item: "Box",
    },
    Entry {
        name: "List",
        package: "std/list",
        item: "List",
    },
    Entry {
        name: "String",
        package: "std/string",
        item: "String",
    },
];

/// The prelude entry named `name`.
pub fn entry(name: &str) -> Option<&'static Entry> {
    PRELUDE.iter().find(|e| e.name == name)
}

/// The prelude entries a file's `tokens` may use (see the module's
/// documentation), each with its first use, in the order of [`PRELUDE`];
/// before the file's imports and its package's items are taken out
/// ([`hidden`]).
pub fn uses(tokens: &[Token]) -> Vec<(&'static Entry, Span)> {
    let mut found: Vec<(&'static Entry, Span)> = Vec::new();
    let mut after_dot = false;
    for t in tokens {
        if let Tok::Ident(name) = &t.tok
            && !after_dot
            && let Some(e) = entry(name)
            && !found.iter().any(|(f, _)| std::ptr::eq(*f, e))
        {
            found.push((e, t.span));
        }
        after_dot = matches!(t.tok, Tok::P(P::Dot));
    }
    found.sort_by_key(|(e, _)| PRELUDE.iter().position(|p| std::ptr::eq(p, *e)));
    found
}

/// Whether `name` is hidden from the prelude in `file`: the file imports a
/// package under that name, or `declared` (the package's items, from
/// [`declared`]) has it.
pub fn hidden(file: &ast::File, declared: &[&str], name: &str) -> bool {
    declared.contains(&name) || file.imports.iter().any(|i| import_name(i) == name)
}

/// The name a file uses for an import: its alias, or its path's last part.
pub fn import_name(import: &ast::Import) -> &str {
    import.alias.as_ref().map_or_else(
        || import.path.rsplit('/').next().unwrap_or_default(),
        |a| a.name.as_str(),
    )
}

/// The names of the items `items` declares for every target (not those in
/// an `if comptime` branch), methods aside.
pub fn declared(items: &[ast::Item]) -> Vec<&str> {
    items
        .iter()
        .filter_map(|item| match item {
            ast::Item::Fn(f) if f.owner.is_none() => Some(f.name.name.as_str()),
            ast::Item::Const(c) => Some(c.name.name.as_str()),
            ast::Item::Struct(s) => Some(s.name.name.as_str()),
            ast::Item::Enum(e) => Some(e.name.name.as_str()),
            ast::Item::Trait(t) => Some(t.name.name.as_str()),
            ast::Item::Type(t) => Some(t.name.name.as_str()),
            ast::Item::Static(s) => Some(s.name.name.as_str()),
            ast::Item::Fn(_)
            | ast::Item::If(_)
            | ast::Item::CompileError(_)
            | ast::Item::Impl(_)
            | ast::Item::Oom(_) => None,
        })
        .collect()
}
