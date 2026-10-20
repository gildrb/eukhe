//! What the session's tools run on the machine (bend/runners.bend, the law
//! `gate_covers_every_runner`). A tool that runs code declares a
//! [`Runner`] in its registration's `extra`: the effects the code it runs
//! may have (its caps) and how the approval gate covers that code. A tool
//! that declares none runs no code of its own: its effects are the session's
//! own (documents, goals, children).
//!
//! Every way to declare a runner is gated: a tool that runs code and is
//! not gated cannot be written as a [`Runner`]. The registry bridge test
//! (`runner/tests.rs`) dumps every tool of a session's registry with its
//! runner and requires the dump to be the model's registry, byte for byte.

#[cfg(test)]
mod tests;

use eukhe_types::shell::ShellEffects;

/// A tool that runs code: what the code may do, and how the gate covers it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Runner {
    /// Every effect the code the tool runs may have.
    pub(crate) caps: ShellEffects,
    /// How the approval gate covers the code.
    pub(crate) gate: Gate,
}

/// How the approval gate covers a runner's code.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Gate {
    /// Each step asks unless its effects are within the auto set (the
    /// `bash` tool, through `eukhe_shell`).
    EachStep,
    /// Each call asks unless the tool's caps are within the auto set,
    /// before any of its code runs (the `ipython` tool).
    EachCall,
}
