//! In-process bash for the `bash` tool (docs/tools.md, S7).
//!
//! A script is a list of steps: simple commands, joined by `;`, newlines,
//! `&&`, `||` and `|`. [`Shell::run`] expands each step (variables, `~`,
//! pathname patterns), classifies its effect
//! ([`eukhe_types::shell::ShellEffect`]; a command the table does not know
//! is `Exec`), and runs it only when its effect is in the [`AutoSet`] or
//! the [`Approver`] approves it. A denial, or no answer, stops the script
//! at that step: the steps before it ran and their effects stand, it and
//! every later step did not run.
//!
//! The common commands run in process with their common options (`cat`,
//! `ls`, `head`, `tail`, `wc`, `echo`, `pwd`, `mkdir`, `rm`, `rmdir`,
//! `touch`, `cp`, `mv`, `true`, `false`, and `grep` on ripgrep's engine);
//! other commands, and these with options the shell does not implement,
//! run as external processes. Shell state (`cd`, `export`, `unset`,
//! assignments) lives in the [`Shell`]. A script that uses syntax outside
//! this grammar (control flow, functions, subshells, command substitution,
//! here-documents, background jobs) runs whole in the external shell as
//! one `Exec` step.
//!
//! A pipeline's commands run together, joined by OS pipes; a command that
//! ends closes its input, so `yes | head` ends. The output streams to a
//! [`Sink`] as the steps write it; the shell keeps none of it.

mod coreutils;
mod effect;
mod expand;
mod parse;
mod run;
#[cfg(test)]
mod testing;

pub use run::{
    Answer, Approval, Approver, Ask, AutoSet, End, Ran, Refusal, Shell, Sink, StepRun, Stream,
};
