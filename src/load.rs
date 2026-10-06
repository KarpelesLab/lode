//! Loading a program: the root file and every package it imports.
//!
//! A package is a directory of `.lode` files that all declare the same
//! `package` name (docs/packages.md). The only packages that can be imported
//! so far are the standard library's (`std/...`), found under the standard
//! library root.
//!
//! A package that may use a name of the prelude (`Box`) also loads the
//! package the name comes from, before itself: see [`crate::prelude`] for
//! when it may.

use std::collections::HashMap;
use std::path::Path;

use crate::ast;
use crate::diag::Diagnostic;
use crate::lex::lex;
use crate::parse::parse;
use crate::prelude::{self, Entry};
use crate::source::{FileId, SourceFile, SourceMap, Span};

/// One loaded package.
#[derive(Debug)]
pub struct Package {
    /// The import path (`std/io`), or for the root package its name (`main`).
    /// It prefixes the package's linker symbols.
    pub path: String,
    pub files: Vec<ast::File>,
}

/// Load the root file and its imports. Packages come back with every
/// dependency before the packages that import it; the root package is last.
pub fn load(map: &mut SourceMap, root: FileId, std_root: &Path) -> (Vec<Package>, Vec<Diagnostic>) {
    let mut loader = Loader {
        map,
        std_root,
        state: HashMap::new(),
        packages: Vec::new(),
        diags: Vec::new(),
    };
    let (file, uses) = loader.parse_file(root);
    let path = file
        .package
        .as_ref()
        .map_or_else(|| "main".to_owned(), |p| p.name.clone());
    loader.imports_of(&file);
    let parsed = [(file, uses)];
    loader.prelude_of(&parsed);
    let [(file, _)] = parsed;
    loader.packages.push(Package {
        path,
        files: vec![file],
    });
    (loader.packages, loader.diags)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum State {
    Loading,
    Done,
}

struct Loader<'a> {
    map: &'a mut SourceMap,
    std_root: &'a Path,
    state: HashMap<String, State>,
    packages: Vec<Package>,
    diags: Vec<Diagnostic>,
}

impl Loader<'_> {
    /// Parse a file; with the prelude names it may use
    /// ([`prelude::uses`]).
    fn parse_file(&mut self, id: FileId) -> (ast::File, Vec<(&'static Entry, Span)>) {
        let (tokens, diags) = lex(&self.map.get(id).text, id);
        self.diags.extend(diags);
        let uses = prelude::uses(&tokens);
        let (mut file, diags) = parse(tokens, id);
        self.diags.extend(diags);
        file.source = self.map.get(id).text.clone();
        (file, uses)
    }

    /// Load the packages of the prelude names a package's files (with
    /// their [`prelude::uses`]) use: those its items and the files'
    /// imports don't hide.
    fn prelude_of(&mut self, files: &[(ast::File, Vec<(&'static Entry, Span)>)]) {
        let declared: Vec<&str> = files
            .iter()
            .flat_map(|(f, _)| prelude::declared(&f.items))
            .collect();
        let mut needed: Vec<(&'static Entry, Span)> = Vec::new();
        for (file, uses) in files {
            for &(entry, span) in uses {
                if !prelude::hidden(file, &declared, entry.name)
                    && !needed.iter().any(|(e, _)| std::ptr::eq(*e, entry))
                {
                    needed.push((entry, span));
                }
            }
        }
        for (entry, span) in needed {
            if self.state.get(entry.package) == Some(&State::Loading) {
                self.diags.push(
                    Diagnostic::error(
                        span,
                        format!(
                            "the prelude's `{}` is in package `{}`, which this package is part of or a dependency of",
                            entry.name, entry.package
                        ),
                    )
                    .with_help("that would be an import cycle: the prelude isn't available here"),
                );
                continue;
            }
            self.require(entry.package, span);
        }
    }

    fn imports_of(&mut self, file: &ast::File) {
        for import in &file.imports {
            self.require(&import.path, import.span);
        }
    }

    /// Make sure the package at `path` is loaded, reporting problems at `span`
    /// (the import that asked for it).
    fn require(&mut self, path: &str, span: Span) {
        match self.state.get(path) {
            Some(State::Done) => return,
            Some(State::Loading) => {
                self.diags.push(Diagnostic::error(
                    span,
                    format!("import cycle: `{path}` imports itself, directly or indirectly"),
                ));
                return;
            }
            None => {}
        }
        let Some(rest) = path.strip_prefix("std/") else {
            self.diags.push(Diagnostic::error(
                span,
                "importing packages outside the standard library is not supported yet",
            ));
            return;
        };
        let dir = self.std_root.join(rest);
        let mut names: Vec<_> = match std::fs::read_dir(&dir) {
            Ok(entries) => entries
                .filter_map(Result::ok)
                .map(|e| e.path())
                .filter(|p| p.extension().is_some_and(|e| e == "lode"))
                .collect(),
            Err(_) => {
                self.diags.push(Diagnostic::error(
                    span,
                    format!("cannot find package `{path}` (looked in {})", dir.display()),
                ));
                return;
            }
        };
        names.sort();
        if names.is_empty() {
            self.diags.push(Diagnostic::error(
                span,
                format!("package `{path}` has no .lode files ({})", dir.display()),
            ));
            return;
        }

        self.state.insert(path.to_owned(), State::Loading);
        let expected = path.rsplit('/').next().unwrap_or(path);
        let mut parsed = Vec::new();
        for name in names {
            let text = match std::fs::read_to_string(&name) {
                Ok(text) => text,
                Err(e) => {
                    self.diags.push(Diagnostic::error(
                        span,
                        format!("cannot read {}: {e}", name.display()),
                    ));
                    continue;
                }
            };
            let id = self
                .map
                .add(SourceFile::new(name.display().to_string(), text));
            let (file, uses) = self.parse_file(id);
            match &file.package {
                Some(p) if p.name == expected => {}
                Some(p) => self.diags.push(Diagnostic::error(
                    p.span,
                    format!(
                        "this file is in package `{expected}`, but declares `package {}`",
                        p.name
                    ),
                )),
                None => self.diags.push(Diagnostic::error(
                    Span::new(id, 0, 0),
                    format!("this file must start with `package {expected}`"),
                )),
            }
            self.imports_of(&file);
            parsed.push((file, uses));
        }
        self.prelude_of(&parsed);
        let files = parsed.into_iter().map(|(f, _)| f).collect();
        self.state.insert(path.to_owned(), State::Done);
        self.packages.push(Package {
            path: path.to_owned(),
            files,
        });
    }
}
