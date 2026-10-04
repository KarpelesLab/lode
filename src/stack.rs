//! Stack usage of a compiled program (docs/safety.md, "Stack bounds").
//!
//! LatticeFoundry measures each function's frame from the same layout its
//! prologue uses, and computes the worst-case depth of the call graph. This
//! module keeps that report with the program's entry point, and renders it
//! with Lode's names (`std/os.write_all`).
//!
//! The report is computed on every build. `lode build --stack-usage` prints
//! it; a profile that requires a bound, or sizing a green thread's stack, will
//! query it with [`StackReport::bound_from`] and [`StackAssumptions`].

use std::fmt;

use latticefoundry::codegen;
pub use latticefoundry::codegen::{
    StackAssumptions, StackBound, StackBoundError, StackUsage as FunctionStack,
};

/// The stack usage of every function of a program, and its entry point.
#[derive(Clone, Debug)]
pub struct StackReport {
    report: codegen::StackReport,
    entry: String,
}

impl StackReport {
    /// A report for `report`'s functions, whose bound is computed from `entry`.
    pub fn new(report: codegen::StackReport, entry: impl Into<String>) -> StackReport {
        StackReport {
            report,
            entry: entry.into(),
        }
    }

    /// The symbol the bound is computed from: the entry `_start` calls, which
    /// calls the program's `main`.
    pub fn entry(&self) -> &str {
        &self.entry
    }

    /// The backend's report, with every field it measures.
    pub fn backend(&self) -> &codegen::StackReport {
        &self.report
    }

    /// Every function, the entry first, then by name (so each package's
    /// functions are together).
    pub fn functions(&self) -> Vec<&FunctionStack> {
        let mut functions: Vec<&FunctionStack> = self.report.functions().iter().collect();
        functions.sort_by_key(|f| (f.name != self.entry, f.name.as_str()));
        functions
    }

    /// The usage of the function whose symbol is `name` (`main.main`,
    /// `std/os.write_all`).
    pub fn function(&self, name: &str) -> Option<&FunctionStack> {
        self.report.get(name)
    }

    /// The worst-case stack depth of the whole program, in bytes, counted from
    /// `_start`'s stack pointer just before it calls the entry. Fails when
    /// there is no bound, saying why.
    pub fn bound(&self) -> Result<StackBound, StackBoundError> {
        self.bound_from(&self.entry, &StackAssumptions::new())
    }

    /// The worst-case stack depth of a call to `root`, with `assume` bounding
    /// what the report can't see (indirect calls, runtime-sized allocations,
    /// functions outside the program).
    pub fn bound_from(
        &self,
        root: &str,
        assume: &StackAssumptions,
    ) -> Result<StackBound, StackBoundError> {
        self.report.worst_case_depth(root, assume)
    }
}

/// Why a call graph has no stack bound, in Lode's terms.
pub fn describe_unbounded(err: &StackBoundError) -> String {
    match err {
        StackBoundError::Recursion { cycle } if cycle.len() == 2 => {
            format!("`{}` calls itself", cycle[0])
        }
        StackBoundError::Recursion { cycle } => {
            format!("recursion: {}", cycle.join(" -> "))
        }
        StackBoundError::IndirectCall { function } => {
            format!("`{function}` calls through a function pointer")
        }
        StackBoundError::DynamicAlloca { function } => {
            format!("`{function}` allocates a runtime-sized amount of stack")
        }
        StackBoundError::UnknownCallee { caller, callee } => {
            format!("`{caller}` calls `{callee}`, whose stack usage is unknown")
        }
        other => other.to_string(),
    }
}

impl fmt::Display for StackReport {
    /// One line per function (its frame in bytes, including the return
    /// address, and what it calls), then the worst-case depth from the entry.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let functions = self.functions();
        let w = functions
            .iter()
            .map(|u| u.name.len())
            .max()
            .unwrap_or(0)
            .max("function".len());
        writeln!(f, "{:<w$}  {:>6}  calls", "function", "frame")?;
        for u in functions {
            let mut calls = u.direct_callees.clone();
            if u.indirect_calls {
                calls.push(StackBound::INDIRECT.to_owned());
            }
            if u.syscalls {
                calls.push("<syscall>".to_owned());
            }
            let frame = if u.dynamic_alloca {
                format!("{}+", u.frame_size)
            } else {
                u.frame_size.to_string()
            };
            writeln!(f, "{:<w$}  {frame:>6}  {}", u.name, calls.join(", "))?;
        }
        match self.bound() {
            Ok(bound) => writeln!(
                f,
                "worst-case stack depth: {} bytes ({})",
                bound.bytes,
                bound.path.join(" -> ")
            ),
            Err(why) => writeln!(
                f,
                "worst-case stack depth: no bound: {}",
                describe_unbounded(&why)
            ),
        }
    }
}
