//! Diagnostics and their rendering.

use std::fmt::Write;

use crate::source::{SourceMap, Span};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Level {
    Error,
    Warning,
}

/// One message about the source, with a primary span and optional help lines.
#[derive(Clone, Debug)]
pub struct Diagnostic {
    pub level: Level,
    pub message: String,
    pub span: Span,
    pub help: Vec<String>,
}

impl Diagnostic {
    pub fn error(span: Span, message: impl Into<String>) -> Diagnostic {
        Diagnostic {
            level: Level::Error,
            message: message.into(),
            span,
            help: Vec::new(),
        }
    }

    pub fn warning(span: Span, message: impl Into<String>) -> Diagnostic {
        Diagnostic {
            level: Level::Warning,
            ..Diagnostic::error(span, message)
        }
    }

    pub fn with_help(mut self, help: impl Into<String>) -> Diagnostic {
        self.help.push(help.into());
        self
    }

    pub fn is_error(&self) -> bool {
        self.level == Level::Error
    }

    /// Render for a terminal:
    ///
    /// ```text
    /// error: cannot prove that this addition does not overflow u32
    ///  --> add.lode:3:9
    ///   |
    /// 3 |     return a + b
    ///   |            ^^^^^
    ///   = help: ...
    /// ```
    pub fn render(&self, files: &SourceMap) -> String {
        let file = files.get(self.span.file);
        let level = match self.level {
            Level::Error => "error",
            Level::Warning => "warning",
        };
        let (line, col) = file.line_col(self.span.start);
        let text = file.line_text(line);
        let gutter = line.to_string().len();
        let pad = " ".repeat(gutter);

        let mut out = String::new();
        let _ = writeln!(out, "{level}: {}", self.message);
        let _ = writeln!(out, "{pad}--> {}:{line}:{col}", file.name);
        let _ = writeln!(out, "{pad} |");
        let _ = writeln!(out, "{line} | {text}");

        // Underline, keeping tabs so the carets line up with the source.
        let line_start =
            self.span.start as usize - (col as usize - 1).min(self.span.start as usize);
        let prefix: String = file.text[line_start..self.span.start as usize]
            .chars()
            .map(|c| if c == '\t' { '\t' } else { ' ' })
            .collect();
        let (end_line, _) = file.line_col(self.span.end.max(self.span.start + 1) - 1);
        let width = if end_line == line {
            file.text[self.span.start as usize..self.span.end as usize]
                .chars()
                .count()
                .max(1)
        } else {
            text.chars()
                .count()
                .saturating_sub(prefix.chars().count())
                .max(1)
        };
        let _ = writeln!(out, "{pad} | {prefix}{}", "^".repeat(width));
        for h in &self.help {
            let _ = writeln!(out, "{pad} = help: {h}");
        }
        out
    }
}

/// A list of diagnostics collected by one compiler stage.
pub type Diagnostics = Vec<Diagnostic>;

pub fn has_errors(diags: &[Diagnostic]) -> bool {
    diags.iter().any(Diagnostic::is_error)
}
