//! In-process bash for the `bash` tool.
//!
//! A script is a list of steps: simple commands, joined by `;`, newlines,
//! `&&`, `||` and `|`. [`Shell::run`] expands each step (variables, `~`,
//! pathname patterns), gathers the parts of each step (the command, each
//! redirection's target, each path it names, by class: a command the
//! table does not know is `Exec`), and runs it only when the compiled
//! core's gate (`eukhe_bend::rules::shell`: bend/tools.bend `join` and
//! `within`) finds every effect within the [`eukhe_types::shell::AutoSet`]
//! or the [`Approver`] approves it. A denial, or no answer, stops the
//! script at that step: the steps before it ran and their effects stand,
//! it and every later step did not run.
//!
//! The common commands run in process with their common options (`cat`,
//! `ls`, `head`, `tail`, `wc`, `echo`, `pwd`, `mkdir`, `rm`, `rmdir`,
//! `touch`, `cp`, `mv`, `true`, `false`, and `grep` on ripgrep's engine);
//! other commands, and these with options the shell does not implement,
//! run as external processes. Shell state (`cd`, `export`, `unset`,
//! assignments) lives in the [`Shell`]. A script that uses syntax outside
//! this grammar (control flow, functions, subshells, command substitution,
//! here-documents, background jobs) runs whole in the external shell as
//! one step: `Exec` and the effects of every command it holds.
//!
//! A pipeline's commands run together, joined by OS pipes; a command that
//! ends closes its input, so `yes | head` ends. The output streams to a
//! [`Sink`] as the steps write it; the shell keeps none of it.

mod coreutils;
mod effect;
mod expand;
mod parse;
pub mod paths;
mod run;
mod shown;

pub use effect::GIT_UNTRUSTED_REPO_ARGS;
pub use run::{Answer, Approval, Approver, Ask, End, Ran, Refusal, Shell, Sink, StepRun, Stream};
pub use shown::visible;
