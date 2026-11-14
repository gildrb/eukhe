//! The `git` row of the classification table: the effects of a `git` step
//! from its global options, subcommand and subcommand options.

use super::{long, operands, short, GIT_UNTRUSTED_REPO_ARGS};
use eukhe_types::shell::{ShellEffect, ShellEffects};

/// `git` options before the subcommand that set no configuration and no
/// program (`-C DIR` aside). Any other one (`-c`, `--config-env`,
/// `--exec-path`, `--git-dir`, `-p`, ...) makes the step `Exec`.
const GIT_GLOBAL: &[&str] = &[
    "--glob-pathspecs",
    "--icase-pathspecs",
    "--literal-pathspecs",
    "--no-optional-locks",
    "--no-pager",
    "--no-replace-objects",
    "--noglob-pathspecs",
    "-P",
];

/// `git` subcommands that, run with [`GIT_UNTRUSTED_REPO_ARGS`] and
/// without the options [`classify`] checks, read objects and refs only and run
/// no program a repository can name. `status`, `diff` of the work tree,
/// `blame`, `add` and the like hash work-tree files through the
/// repository's clean filters (programs no argument can switch off): they
/// are `Exec`.
const GIT_READ: &[&str] = &[
    "cat-file",
    "count-objects",
    "describe",
    "for-each-ref",
    "grep",
    "log",
    "ls-files",
    "ls-tree",
    "merge-base",
    "name-rev",
    "rev-list",
    "rev-parse",
    "shortlog",
    "show",
    "show-ref",
    "version",
];

/// `git` subcommands that show a diff: run with `--no-ext-diff
/// --no-textconv` after the subcommand, so no external diff or textconv
/// driver of the repository runs.
const GIT_DIFFING: &[&str] = &["diff", "log", "show"];

/// `git` subcommands that talk to a remote. A remote transport runs
/// programs the repository can name (`core.sshCommand`, credential
/// helpers, hooks): `Net` and `Exec`.
const GIT_NET: &[&str] = &["clone", "fetch", "ls-remote", "pull", "push", "submodule"];

/// `git branch` options that change a branch (`--edit-description` runs
/// an editor and is checked apart).
const GIT_BRANCH_CHANGE: &[&str] = &[
    "copy",
    "create-reflog",
    "delete",
    "force",
    "move",
    "no-track",
    "set-upstream-to",
    "track",
    "unset-upstream",
];

/// `git log --pretty`/`--format` names git defines; any other name without
/// a `%` is a `pretty.<name>` alias from the configuration.
const GIT_PRETTY: &[&str] = &[
    "email",
    "full",
    "fuller",
    "medium",
    "mboxrd",
    "oneline",
    "raw",
    "reference",
    "short",
];

/// The effects of the `git` step `words`. A step that is not `Exec` is
/// rewritten in place to run with [`GIT_UNTRUSTED_REPO_ARGS`] (and a
/// diffing subcommand with `--no-ext-diff --no-textconv`): its class holds
/// only with them.
pub(super) fn classify(words: &mut Vec<String>) -> ShellEffects {
    let Some(at) = subcommand_at(words) else {
        return ShellEffects::of(&[ShellEffect::Exec]);
    };
    let Some(sub) = words.get(at) else {
        return ShellEffects::of(&[ShellEffect::Read]);
    };
    let effects = subcommand_effects(sub, words.get(at + 1..).unwrap_or_default());
    let diffing = GIT_DIFFING.contains(&sub.as_str());
    if !effects.contains(ShellEffect::Exec) {
        if diffing {
            let after = at + 1;
            words.splice(
                after..after,
                ["--no-ext-diff", "--no-textconv"].map(String::from),
            );
        }
        words.splice(1..1, GIT_UNTRUSTED_REPO_ARGS.map(String::from));
    }
    effects
}

/// The place of the subcommand in `words`, past the global options (`-C`
/// takes a value); `None` when a global option can set configuration or a
/// program.
fn subcommand_at(words: &[String]) -> Option<usize> {
    let mut at = 1;
    loop {
        match words.get(at).map(String::as_str) {
            Some("-C") => at += 2,
            Some(arg) if GIT_GLOBAL.contains(&arg) => at += 1,
            Some(arg) if arg.starts_with('-') => return None,
            Some(_) | None => return Some(at),
        }
    }
}

/// The effects of the subcommand `sub` with `options`, the words after it.
fn subcommand_effects(sub: &str, options: &[String]) -> ShellEffects {
    let exec = ShellEffects::of(&[ShellEffect::Exec]);
    let any = |name: &str| options.iter().any(|arg| long(arg, name));
    let runs_driver = any("textconv") || any("ext-diff") || any("filters");
    let effects = if GIT_NET.contains(&sub) {
        ShellEffects::of(&[ShellEffect::Net]).union(exec)
    } else if checks_signature(options) || runs_driver {
        exec
    } else {
        local_effects(sub, options)
    };
    if any("output") {
        effects.with(ShellEffect::Write)
    } else {
        effects
    }
}

/// Whether `options` ask for a signature check, which runs `gpg.program`;
/// a `pretty.<name>` alias may ask for one (`%G`).
fn checks_signature(options: &[String]) -> bool {
    options.iter().any(|arg| {
        arg.starts_with('-')
            && (arg.contains("%G")
                || arg.contains("signature")
                || (long(arg, "format") || long(arg, "pretty"))
                    && arg.split_once('=').is_some_and(|(_, value)| {
                        !value.contains('%')
                            && !value.starts_with("format:")
                            && !value.starts_with("tformat:")
                            && !GIT_PRETTY.contains(&value)
                    }))
    })
}

/// The effects of a subcommand that talks to no remote and runs no
/// driver or signature program.
fn local_effects(sub: &str, options: &[String]) -> ShellEffects {
    let read = ShellEffects::of(&[ShellEffect::Read]);
    let write = ShellEffects::of(&[ShellEffect::Write]);
    let exec = ShellEffects::of(&[ShellEffect::Exec]);
    let any = |name: &str| options.iter().any(|arg| long(arg, name));
    let any_option = |letter: char, name: &str| {
        options
            .iter()
            .any(|arg| short(arg, letter) || long(arg, name))
    };
    match sub {
        "grep" if any_option('O', "open-files-in-pager") => exec,
        "describe" if any("dirty") || any("broken") => exec,
        "ls-files" if any_option('m', "modified") => exec,
        "diff" if any("cached") || any("staged") => read,
        "branch" if any("edit-description") => exec,
        "branch" if changes_branch(options) => write,
        "branch" => read,
        "symbolic-ref" if operands(options, &[]) < 2 => read,
        "symbolic-ref" | "update-ref" | "init" => write,
        sub if GIT_READ.contains(&sub) => read,
        _ => exec,
    }
}

/// Whether `git branch` with `options` changes a branch: an option that
/// does, or a branch name to create without `--list`.
fn changes_branch(options: &[String]) -> bool {
    options.iter().any(|arg| {
        ['c', 'C', 'd', 'D', 'f', 'm', 'M', 't', 'u']
            .into_iter()
            .any(|letter| short(arg, letter))
            || GIT_BRANCH_CHANGE.iter().any(|name| long(arg, name))
    }) || (operands(options, &[]) > 0
        && !options
            .iter()
            .any(|arg| short(arg, 'l') || long(arg, "list")))
}
