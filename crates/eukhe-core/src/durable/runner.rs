//! What the session's tools run on the machine (bend/runners.bend, the law
//! `gate_covers_every_runner`). A tool that runs code declares a
//! [`Runner`] in its registration's `extra`: the effects the code it runs
//! may have (its caps) and how its effects are judged: by step or by call. A tool
//! that declares none runs no code of its own: its effects are the session's
//! own (documents, directors, children).
//!
//! Every way to declare a runner names how it is judged: a tool that runs
//! code without one cannot be written as a [`Runner`]. The registry test
//! (`runner/tests.rs`) requires every tool of a session's registry, with
//! its runner, to be the compiled core's registry
//! (`eukhe_bend::rules::runners::registry`).

#[cfg(test)]
mod tests;

use eukhe_types::shell::ShellEffects;

/// A tool that runs code: what the code may do, and how it is judged.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Runner {
    /// Every effect the code the tool runs may have.
    pub(crate) caps: ShellEffects,
    /// How the code's effects are judged.
    pub(crate) gate: Gate,
}

/// How a runner's effects are judged (irreversible or not, own writes).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Gate {
    /// Each step on its own (the `bash` tool, through `eukhe_shell`).
    EachStep,
    /// The call as a whole, by the tool's caps, before any of its code
    /// runs (the `python` tool).
    EachCall,
}
