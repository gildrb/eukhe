//! The classification table: the effects of one step from its
//! assignments and expanded words. A command the table does not know is
//! `Exec`; the caller adds the effects of the step's redirections and of
//! the paths it names.

use eukhe_types::shell::{ShellEffect, ShellEffects};

/// Commands that only read files or shell state, with the options
/// [`classify`] checks first.
const READ: &[&str] = &[
    ":",
    "[",
    "b2sum",
    "basename",
    "cat",
    "cd",
    "cksum",
    "cmp",
    "column",
    "comm",
    "cut",
    "date",
    "df",
    "diff",
    "dirname",
    "du",
    "echo",
    "egrep",
    "exit",
    "false",
    "fgrep",
    "file",
    "grep",
    "head",
    "hexdump",
    "id",
    "jq",
    "less",
    "ls",
    "md5sum",
    "more",
    "nl",
    "od",
    "printenv",
    "printf",
    "pwd",
    "readlink",
    "realpath",
    "rg",
    "seq",
    "sha1sum",
    "sha256sum",
    "sha512sum",
    "sleep",
    "sort",
    "stat",
    "tail",
    "test",
    "tr",
    "true",
    "uname",
    "uniq",
    "unset",
    "wc",
    "which",
    "whoami",
    "xxd",
    "yes",
];

/// Commands that change files.
const WRITE: &[&str] = &[
    "chgrp", "chmod", "chown", "cp", "dd", "install", "ln", "mkdir", "mktemp", "mv", "rm", "rmdir",
    "shred", "tee", "touch", "truncate", "unlink",
];

/// Commands that talk to the network.
const NET: &[&str] = &[
    "aria2c",
    "curl",
    "dig",
    "ftp",
    "gh",
    "host",
    "http",
    "https",
    "mosh",
    "nc",
    "ncat",
    "netcat",
    "nslookup",
    "ping",
    "ping6",
    "rsync",
    "scp",
    "sftp",
    "socat",
    "ssh",
    "telnet",
    "traceroute",
    "wget",
];

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

/// The leading `git` arguments for a working tree the user may not trust
/// (a session cwd, a snapshot or gate target, a `bash` step): with them a
/// repository's own configuration cannot run a program through the
/// filesystem monitor, a hook, a pager, a signature check or a fetch of
/// missing objects. eukhe's own read-only probes use them, and the shell
/// runs every `git` step that is not `Exec` with them.
pub const GIT_UNTRUSTED_REPO_ARGS: [&str; 11] = [
    "-c",
    "core.fsmonitor=false",
    "-c",
    "core.hooksPath=/dev/null",
    "-c",
    "log.showSignature=false",
    "-c",
    "format.pretty=medium",
    "-c",
    "protocol.allow=never",
    "--no-pager",
];

/// `git` subcommands that, run with [`GIT_UNTRUSTED_REPO_ARGS`] and
/// without the options [`classify`] checks, read objects and refs only
/// and run no program a repository can name. `status`, `diff` of the
/// work tree, `blame`, `add` and the like hash work-tree files through
/// the repository's clean filters (programs no argument can switch off):
/// they are `Exec`.
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

/// `curl` long options that write a file.
const CURL_WRITING: &[&str] = &[
    "alt-svc",
    "config",
    "cookie-jar",
    "create-dirs",
    "dump-header",
    "etag-save",
    "hsts",
    "libcurl",
    "output",
    "output-dir",
    "remote-name",
    "remote-name-all",
    "stderr",
    "trace",
    "trace-ascii",
];

/// `sed` long options that only change how the script reads its input
/// (`--expression` and `--in-place` are checked apart).
const SED_LONG: &[&str] = &[
    "null-data",
    "posix",
    "quiet",
    "regexp-extended",
    "sandbox",
    "separate",
    "silent",
    "unbuffered",
    "zero-terminated",
];

/// `uniq` options whose value may be the next word.
const UNIQ_VALUED: &[&str] = &[
    "--check-chars",
    "--skip-chars",
    "--skip-fields",
    "-f",
    "-s",
    "-w",
];

/// `xxd` options whose value is the next word.
const XXD_VALUED: &[&str] = &[
    "-c",
    "-cols",
    "-g",
    "-groupsize",
    "-l",
    "-len",
    "-n",
    "-name",
    "-o",
    "-offset",
    "-s",
    "-seek",
];

/// Whether `arg` is the long option `--name` (with or without `=VALUE`)
/// or an abbreviation of it: GNU `getopt_long` takes any prefix.
fn long(arg: &str, name: &str) -> bool {
    arg.strip_prefix("--")
        .map(|rest| rest.split('=').next().unwrap_or(rest))
        .is_some_and(|given| !given.is_empty() && name.starts_with(given))
}

/// Whether `arg` is a cluster of short options (`-abc`) that holds
/// `letter`. An attached value that holds it counts too: the check errs
/// to the stronger effect.
fn short(arg: &str, letter: char) -> bool {
    arg.strip_prefix('-')
        .is_some_and(|flags| !flags.starts_with('-') && flags.contains(letter))
}

/// The number of operands in `args`: the words that are not options (`-`
/// is one), and every word after `--`. The word after an option in
/// `valued` is its value. Any other value (attached, abbreviated, of an
/// option not in `valued`) counts as an operand: the count is never lower
/// than the command's.
fn operands(args: &[String], valued: &[&str]) -> usize {
    let mut count = 0;
    let mut rest = args.iter();
    while let Some(arg) = rest.next() {
        if arg == "--" {
            return count + rest.count();
        }
        if arg == "-" || !arg.starts_with('-') {
            count += 1;
        } else if valued.contains(&arg.as_str()) {
            rest.next();
        }
    }
    count
}

/// The effects of a step with the assignments `assigns` and the expanded
/// words `words` (no words: only assignments or redirections, which change
/// shell state). A `git` step that is not `Exec` is rewritten in place to
/// run with [`GIT_UNTRUSTED_REPO_ARGS`] (and a diffing subcommand with
/// `--no-ext-diff --no-textconv`): its class holds only with them.
#[allow(clippy::too_many_lines)] // One arm per command of the table.
pub(crate) fn classify(assigns: &[(String, String)], words: &mut Vec<String>) -> ShellEffects {
    let read = ShellEffects::of(&[ShellEffect::Read]);
    let write = ShellEffects::of(&[ShellEffect::Write]);
    let exec = ShellEffects::of(&[ShellEffect::Exec]);
    let net = ShellEffects::of(&[ShellEffect::Net]);
    // An assignment changes the environment of the command, or alone of
    // every later command: `PATH`, `LD_PRELOAD`, `LESSOPEN` or `GIT_*`
    // make a reading command run another program.
    if !assigns.is_empty() {
        return exec;
    }
    let Some((program, args)) = words.split_first() else {
        return read;
    };
    match program.as_str() {
        "export" if args.is_empty() => read,
        // A word with `/` runs that file, whatever its name: the own
        // coreutils answer only a bare name. `export` with an operand
        // changes the environment, as an assignment does.
        name if name.contains('/') || name == "export" => exec,
        "git" => {
            // Options before the subcommand; `-C` takes a value. `at` is
            // the subcommand's place in `words`.
            let mut at = 1;
            loop {
                match words.get(at).map(String::as_str) {
                    Some("-C") => at += 2,
                    Some(arg) if GIT_GLOBAL.contains(&arg) => at += 1,
                    Some(arg) if arg.starts_with('-') => return exec,
                    Some(_) | None => break,
                }
            }
            let Some(sub) = words.get(at).map(String::as_str) else {
                return read;
            };
            let options = words.get(at + 1..).unwrap_or_default();
            let any = |name: &str| options.iter().any(|arg| long(arg, name));
            // A signature check runs `gpg.program`; a `pretty.<name>` alias
            // may ask for one (`%G`).
            let checks_signature = options.iter().any(|arg| {
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
            });
            let runs_driver = any("textconv") || any("ext-diff") || any("filters");
            let effects = if GIT_NET.contains(&sub) {
                net.union(exec)
            } else if checks_signature || runs_driver {
                exec
            } else {
                match sub {
                    "grep"
                        if options
                            .iter()
                            .any(|arg| short(arg, 'O') || long(arg, "open-files-in-pager")) =>
                    {
                        exec
                    }
                    "describe" if any("dirty") || any("broken") => exec,
                    "ls-files"
                        if options
                            .iter()
                            .any(|arg| short(arg, 'm') || long(arg, "modified")) =>
                    {
                        exec
                    }
                    "diff" if any("cached") || any("staged") => read,
                    "branch" if any("edit-description") => exec,
                    "branch"
                        if options.iter().any(|arg| {
                            ['c', 'C', 'd', 'D', 'f', 'm', 'M', 't', 'u']
                                .into_iter()
                                .any(|letter| short(arg, letter))
                                || GIT_BRANCH_CHANGE.iter().any(|name| long(arg, name))
                        }) || (operands(options, &[]) > 0
                            && !options
                                .iter()
                                .any(|arg| short(arg, 'l') || long(arg, "list"))) =>
                    {
                        write
                    }
                    "branch" => read,
                    "symbolic-ref" if operands(options, &[]) < 2 => read,
                    "symbolic-ref" | "update-ref" | "init" => write,
                    sub if GIT_READ.contains(&sub) => read,
                    _ => exec,
                }
            };
            let effects = if any("output") {
                effects.with(ShellEffect::Write)
            } else {
                effects
            };
            let diffing = GIT_DIFFING.contains(&sub);
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
        "sed" => {
            // Every script must be a known-safe form: no `e`, `r`, `w`
            // command and no `e` or `w` flag of `s`.
            let mut scripts: Vec<&str> = Vec::new();
            let mut first_operand: Option<&str> = None;
            let mut in_place = false;
            let mut options_end = false;
            let mut rest = args.iter();
            while let Some(arg) = rest.next() {
                if options_end || arg == "-" || !arg.starts_with('-') {
                    first_operand.get_or_insert(arg);
                } else if arg == "--" {
                    options_end = true;
                } else if arg.starts_with("--") {
                    if long(arg, "in-place") {
                        in_place = true;
                    } else if long(arg, "expression") {
                        match arg.split_once('=') {
                            Some((_, script)) => scripts.push(script),
                            None => match rest.next() {
                                Some(script) => scripts.push(script),
                                None => return exec,
                            },
                        }
                    } else if !SED_LONG.iter().any(|name| long(arg, name)) {
                        return exec;
                    }
                } else {
                    let flags = &arg[1..];
                    for (at, flag) in flags.char_indices() {
                        match flag {
                            'n' | 'E' | 'r' | 's' | 'u' | 'z' => {}
                            // The rest of the word is the backup suffix.
                            'i' => {
                                in_place = true;
                                break;
                            }
                            // The rest of the word, else the next word, is
                            // the script.
                            'e' => {
                                let attached = &flags[at + 1..];
                                if attached.is_empty() {
                                    match rest.next() {
                                        Some(script) => scripts.push(script),
                                        None => return exec,
                                    }
                                } else {
                                    scripts.push(attached);
                                }
                                break;
                            }
                            _ => return exec,
                        }
                    }
                }
            }
            // Without `-e`, the first operand is the script.
            if scripts.is_empty() {
                match first_operand {
                    Some(script) => scripts.push(script),
                    None => return read,
                }
            }
            let known = |script: &str| -> bool {
                let bytes = script.as_bytes();
                let mut at = 0;
                // Move `at` past the next `end` that no `\` escapes: false
                // when none follows.
                let past = |at: &mut usize, end: u8| -> bool {
                    while let Some(&byte) = bytes.get(*at) {
                        *at += 1;
                        if byte == b'\\' {
                            *at += 1;
                        } else if byte == end {
                            return true;
                        }
                    }
                    false
                };
                // Move `at` past an address (`N`, `$`, `/regex/`): false
                // when none is there.
                let address = |at: &mut usize| -> bool {
                    match bytes.get(*at) {
                        Some(byte) if byte.is_ascii_digit() => {
                            while bytes.get(*at).is_some_and(u8::is_ascii_digit) {
                                *at += 1;
                            }
                            true
                        }
                        Some(b'$') => {
                            *at += 1;
                            true
                        }
                        Some(b'/') => {
                            *at += 1;
                            past(at, b'/')
                        }
                        Some(_) | None => false,
                    }
                };
                let blank = |at: &mut usize| {
                    while bytes
                        .get(*at)
                        .is_some_and(|byte| matches!(byte, b' ' | b'\t'))
                    {
                        *at += 1;
                    }
                };
                loop {
                    while bytes
                        .get(at)
                        .is_some_and(|byte| matches!(byte, b' ' | b'\t' | b'\n' | b';'))
                    {
                        at += 1;
                    }
                    if at == bytes.len() {
                        return true;
                    }
                    if address(&mut at) && bytes.get(at) == Some(&b',') {
                        at += 1;
                        if !address(&mut at) {
                            return false;
                        }
                    }
                    blank(&mut at);
                    if bytes.get(at) == Some(&b'!') {
                        at += 1;
                        blank(&mut at);
                    }
                    let Some(&command) = bytes.get(at) else {
                        return false;
                    };
                    at += 1;
                    match command {
                        b'{' => continue,
                        b'=' | b'}' | b'd' | b'D' | b'g' | b'G' | b'h' | b'H' | b'n' | b'N'
                        | b'p' | b'P' | b'q' | b'Q' | b'x' => {}
                        b's' | b'y' => {
                            let Some(&delimiter) = bytes.get(at) else {
                                return false;
                            };
                            if matches!(delimiter, b'\\' | b'\n') {
                                return false;
                            }
                            at += 1;
                            if !(past(&mut at, delimiter) && past(&mut at, delimiter)) {
                                return false;
                            }
                            if command == b's' {
                                while bytes
                                    .get(at)
                                    .is_some_and(|flag| b"gimpIM0123456789".contains(flag))
                                {
                                    at += 1;
                                }
                            }
                        }
                        _ => return false,
                    }
                    // A command ends at a blank, `;`, a newline, `}` or the
                    // end of the script.
                    if !matches!(
                        bytes.get(at),
                        None | Some(b' ' | b'\t' | b'\n' | b';' | b'}')
                    ) {
                        return false;
                    }
                }
            };
            if !scripts.into_iter().all(known) {
                exec
            } else if in_place {
                write
            } else {
                read
            }
        }
        "find" => {
            if args
                .iter()
                .any(|arg| matches!(arg.as_str(), "-exec" | "-execdir" | "-ok" | "-okdir"))
            {
                exec
            } else if args.iter().any(|arg| {
                matches!(
                    arg.as_str(),
                    "-delete" | "-fls" | "-fprint" | "-fprint0" | "-fprintf"
                )
            }) {
                write
            } else {
                read
            }
        }
        "rg" if args
            .iter()
            .any(|arg| arg.starts_with("--pre") || arg.starts_with("--hostname-bin")) =>
        {
            exec
        }
        "sort" if args.iter().any(|arg| long(arg, "compress-program")) => exec,
        "sort"
            if args
                .iter()
                .any(|arg| short(arg, 'o') || long(arg, "output")) =>
        {
            write
        }
        // A second operand is the output file.
        "uniq" if operands(args, UNIQ_VALUED) >= 2 => write,
        "xxd" if operands(args, XXD_VALUED) >= 2 => write,
        "less"
            if args
                .iter()
                .any(|arg| arg.starts_with('+') && arg.contains(['!', '|'])) =>
        {
            exec
        }
        "less"
            if args.iter().any(|arg| {
                short(arg, 'o') || short(arg, 'O') || long(arg, "log-file") || long(arg, "LOG-FILE")
            }) =>
        {
            write
        }
        "file"
            if args
                .iter()
                .any(|arg| short(arg, 'C') || long(arg, "compile")) =>
        {
            write
        }
        // curl writes a file with these options (a config file may name
        // one too); wget writes the file it fetches.
        "curl"
            if args.iter().any(|arg| {
                ['o', 'O', 'D', 'c', 'K']
                    .into_iter()
                    .any(|letter| short(arg, letter))
                    || CURL_WRITING.iter().any(|name| long(arg, name))
            }) =>
        {
            net.union(write)
        }
        "wget" => net.union(write),
        "env" if args.is_empty() => read,
        name if READ.contains(&name) => read,
        name if WRITE.contains(&name) => write,
        name if NET.contains(&name) => net,
        _ => exec,
    }
}

/// The commands that read the working directory when they name no path
/// of their own, with the options whose value may be the next word (the
/// short letters, the long names) and the options that give the pattern
/// (so that no operand is one). Each lists (`ls`, `du`, `git ls-files`)
/// or searches (`rg`, `grep -r`, `git grep`) the directory; `find` has
/// its own form. Every other command of the table reads only what it
/// names, or its input; a command the table does not know is `Exec`.
struct Walker {
    short: &'static str,
    long: &'static [&'static str],
    patterns: Patterns,
}

/// Whether the first operand of a [`Walker`] is a pattern, not a path.
enum Patterns {
    /// Every operand is a path.
    Paths,
    /// The first operand is the pattern, unless one of these short
    /// letters or long names gives it (or `files` asks for the list of
    /// files).
    First {
        short: &'static str,
        long: &'static [&'static str],
        files: Option<&'static str>,
    },
}

/// The operands of a [`Walker`] command.
struct Operands {
    /// Before `--`.
    before: usize,
    /// After `--`.
    after: usize,
    /// An option gave the pattern.
    pattern_given: bool,
}

const LS: Walker = Walker {
    short: "ITw",
    long: &[
        "block-size",
        "format",
        "hide",
        "ignore",
        "indicator-style",
        "quoting-style",
        "sort",
        "tabsize",
        "time",
        "time-style",
        "width",
    ],
    patterns: Patterns::Paths,
};

const DU: Walker = Walker {
    short: "BdtX",
    long: &[
        "block-size",
        "exclude",
        "exclude-from",
        "files0-from",
        "max-depth",
        "threshold",
        "time-style",
    ],
    patterns: Patterns::Paths,
};

const RG: Walker = Walker {
    short: "ABCEMTdefgjmrt",
    long: &[
        "after-context",
        "before-context",
        "color",
        "colors",
        "context",
        "context-separator",
        "dfa-size-limit",
        "encoding",
        "engine",
        "field-context-separator",
        "field-match-separator",
        "file",
        "generate",
        "glob",
        "hostname-bin",
        "hyperlink-format",
        "iglob",
        "ignore-file",
        "max-columns",
        "max-count",
        "max-depth",
        "max-filesize",
        "path-separator",
        "pre",
        "pre-glob",
        "regex-size-limit",
        "regexp",
        "replace",
        "sort",
        "sortr",
        "threads",
        "type",
        "type-add",
        "type-clear",
        "type-not",
    ],
    patterns: Patterns::First {
        short: "ef",
        long: &["regexp", "file"],
        files: Some("--files"),
    },
};

const GREP: Walker = Walker {
    short: "ABCDdefm",
    long: &[
        "after-context",
        "before-context",
        "binary-files",
        "context",
        "devices",
        "directories",
        "exclude",
        "exclude-dir",
        "exclude-from",
        "file",
        "group-separator",
        "include",
        "label",
        "max-count",
        "regexp",
    ],
    patterns: Patterns::First {
        short: "ef",
        long: &["regexp", "file"],
        files: None,
    },
};

const GIT_GREP: Walker = Walker {
    short: "ABCefm",
    long: &[
        "after-context",
        "before-context",
        "context",
        "file",
        "max-count",
        "max-depth",
        "regexp",
        "threads",
    ],
    patterns: Patterns::First {
        short: "ef",
        long: &["regexp", "file"],
        files: None,
    },
};

const GIT_LS_FILES: Walker = Walker {
    short: "xX",
    long: &[
        "exclude",
        "exclude-from",
        "exclude-per-directory",
        "format",
        "with-tree",
    ],
    patterns: Patterns::Paths,
};

/// The operands of `args` (as [`Operands`]). An option of `walker` whose
/// value may be the next word takes it (a long one by any abbreviation:
/// the count errs low, to a read of the working directory).
fn walk_operands(walker: &Walker, args: &[String]) -> Operands {
    let (pattern_short, pattern_long, files) = match &walker.patterns {
        Patterns::Paths => ("", &[][..], None),
        Patterns::First { short, long, files } => (*short, *long, *files),
    };
    let mut operands = Operands {
        before: 0,
        after: 0,
        pattern_given: false,
    };
    let mut rest = args.iter();
    while let Some(arg) = rest.next() {
        if arg == "--" {
            operands.after = rest.count();
            return operands;
        }
        if let Some(name) = arg.strip_prefix("--") {
            operands.pattern_given |=
                Some(arg.as_str()) == files || pattern_long.iter().any(|full| long(arg, full));
            if !name.contains('=') && walker.long.iter().any(|full| long(arg, full)) {
                rest.next();
            }
        } else if let Some(flags) = arg.strip_prefix('-').filter(|flags| !flags.is_empty()) {
            for (at, flag) in flags.char_indices() {
                operands.pattern_given |= pattern_short.contains(flag);
                if walker.short.contains(flag) {
                    if at + flag.len_utf8() == flags.len() {
                        rest.next();
                    }
                    break;
                }
            }
        } else {
            operands.before += 1;
        }
    }
    operands
}

/// Whether the command of `words` reads the working directory because it
/// names no path of its own (the [`Walker`] commands; `find` with no
/// starting point; `git` without `-C`, whose directory is a word it
/// names). A pattern operand is no path; before `--`, an operand of `git
/// grep` may be a revision, whose whole tree it searches.
pub(crate) fn reads_cwd(words: &[String]) -> bool {
    let Some((program, args)) = words.split_first() else {
        return false;
    };
    let (walker, args) = match program.as_str() {
        "ls" => (&LS, args),
        "du" => (&DU, args),
        "rg" => (&RG, args),
        "grep" | "egrep" | "fgrep" => {
            let recursive = args.iter().any(|arg| {
                short(arg, 'r')
                    || short(arg, 'R')
                    || long(arg, "recursive")
                    || long(arg, "dereference-recursive")
            });
            if !recursive {
                return false;
            }
            (&GREP, args)
        }
        "find" => {
            // `find [-H] [-L] [-P] [-D opts] [-Olevel] [starting-point...]
            // [expression]`: no starting point is `.`.
            let mut rest = args.iter().peekable();
            while let Some(arg) = rest.next_if(|arg| {
                matches!(arg.as_str(), "-H" | "-L" | "-P" | "-D") || arg.starts_with("-O")
            }) {
                if arg == "-D" {
                    rest.next();
                }
            }
            return rest
                .next()
                .is_none_or(|arg| arg.starts_with('-') || matches!(arg.as_str(), "(" | "!"));
        }
        "git" => {
            let mut at = 0;
            loop {
                match args.get(at).map(String::as_str) {
                    Some("-C") => return false,
                    Some(arg) if arg.starts_with('-') => at += 1,
                    Some(_) | None => break,
                }
            }
            let rest = args.get(at + 1..).unwrap_or_default();
            match args.get(at).map(String::as_str) {
                Some("grep") => return walk_operands(&GIT_GREP, rest).after == 0,
                Some("ls-files") => (&GIT_LS_FILES, rest),
                Some(_) | None => return false,
            }
        }
        _ => return false,
    };
    let operands = walk_operands(walker, args);
    let patterns = match walker.patterns {
        Patterns::First { .. } if !operands.pattern_given => 1,
        Patterns::First { .. } | Patterns::Paths => 0,
    };
    operands.before + operands.after <= patterns
}

#[cfg(test)]
mod tests {
    use super::*;
    use ShellEffect::{Exec, Net, Read, Write};

    /// One step: its assignments and its words.
    type Case = (
        &'static [(&'static str, &'static str)],
        &'static [&'static str],
    );

    /// The effects of each step.
    fn effects(cases: &[Case]) -> Vec<ShellEffects> {
        cases
            .iter()
            .map(|(assigns, words)| {
                classify(
                    &assigns
                        .iter()
                        .map(|(name, value)| (name.to_string(), value.to_string()))
                        .collect::<Vec<_>>(),
                    &mut words.iter().map(ToString::to_string).collect::<Vec<_>>(),
                )
            })
            .collect()
    }

    /// The sets of `expected`.
    fn sets(expected: &[&[ShellEffect]]) -> Vec<ShellEffects> {
        expected
            .iter()
            .map(|effects| ShellEffects::of(effects))
            .collect()
    }

    #[test]
    fn commands_classify_by_name_subcommand_and_option() {
        let cases: &[Case] = &[
            (&[], &["cat", "a"]),
            (&[], &["rm", "-rf", "x"]),
            (&[], &["curl", "https://example.com"]),
            (&[], &["curl", "-sSfLo", "out", "https://example.com"]),
            (
                &[],
                &["curl", "--output-dir=d", "-O", "https://example.com"],
            ),
            (&[], &["wget", "https://example.com"]),
            (&[], &["python3", "x.py"]),
            (&[], &["sed", "-n", "1p", "f"]),
            (&[], &["sed", "-i", "s/a/b/", "f"]),
            (&[], &["find", ".", "-name", "x"]),
            (&[], &["find", ".", "-delete"]),
            (&[], &["find", ".", "-exec", "rm", "{}", ";"]),
            (&[], &["env"]),
            (&[], &["env", "X=1", "sh"]),
            (&[], &[]),
        ];
        assert_eq!(
            effects(cases),
            sets(&[
                &[Read],
                &[Write],
                &[Net],
                &[Write, Net],
                &[Write, Net],
                &[Write, Net],
                &[Exec],
                &[Read],
                &[Write],
                &[Read],
                &[Write],
                &[Exec],
                &[Read],
                &[Exec],
                &[Read],
            ])
        );
    }

    #[test]
    fn a_program_named_by_a_path_is_exec() {
        let cases: &[Case] = &[
            (&[], &["./cat", "x"]),
            (&[], &["bin/stat", "x"]),
            (&[], &["../x/sort"]),
            (&[], &["/usr/bin/rm", "-rf", "x"]),
            (&[], &["/usr/bin/curl", "https://example.com"]),
        ];
        assert_eq!(effects(cases), sets(&[&[Exec][..]; 5]));
    }

    #[test]
    fn an_assignment_or_an_export_is_exec() {
        let cases: &[Case] = &[
            (&[("PATH", "./bin:/usr/bin")], &["stat", "f"]),
            (&[("LD_PRELOAD", "./x.so")], &["wc", "f"]),
            (&[("LESSOPEN", "|sh -c x")], &["less", "f"]),
            (&[("GIT_EXTERNAL_DIFF", "./x")], &["git", "diff"]),
            (&[("X", "1")], &[]),
            (&[], &["export", "PATH=./bin"]),
            (&[], &["export", "X"]),
            (&[], &["export"]),
            (&[], &["unset", "X"]),
        ];
        assert_eq!(
            effects(cases),
            sets(&[
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Read],
                &[Read],
            ])
        );
    }

    /// Regression (audit H3): `git status`, `diff`, `show` and the like
    /// were `Read`, and every other subcommand `Write`, while a
    /// repository's configuration (fsmonitor, hooks, filters, diff and
    /// textconv drivers, signature programs, ssh commands) can make them
    /// run a program.
    #[test]
    fn a_git_step_that_can_run_a_repository_program_is_exec() {
        let cases: &[Case] = &[
            // Work-tree hashing runs the clean filters.
            (&[], &["git", "-C", "repo", "status"]),
            (&[], &["git", "diff"]),
            (&[], &["git", "blame", "f"]),
            (&[], &["git", "add", "f"]),
            (&[], &["git", "describe", "--dirty"]),
            (&[], &["git", "ls-files", "-m"]),
            // Hooks, editors, commands.
            (&[], &["git", "commit", "-m", "x"]),
            (&[], &["git", "bisect", "run", "make"]),
            (&[], &["git", "rebase", "-x", "make", "main"]),
            (&[], &["git", "config", "core.pager", "x"]),
            (&[], &["git", "st"]),
            (&[], &["git", "branch", "--edit-description"]),
            // Drivers and signature programs.
            (&[], &["git", "log", "-p", "--textconv"]),
            (&[], &["git", "show", "--ext-diff"]),
            (&[], &["git", "cat-file", "--filters", "HEAD:f"]),
            (&[], &["git", "log", "--show-signature"]),
            (&[], &["git", "log", "--format=%h %G?"]),
            (&[], &["git", "log", "--pretty=mine"]),
            (&[], &["git", "for-each-ref", "--format=%(signature)"]),
            // Configuration or a program before the subcommand.
            (&[], &["git", "-c", "core.fsmonitor=./x", "status"]),
            (&[], &["git", "-c", "diff.external=./x", "diff"]),
            (&[], &["git", "--config-env=core.sshCommand=X", "log"]),
            (&[], &["git", "--exec-path=./x", "log"]),
            (&[], &["git", "--git-dir=x", "log"]),
            (&[], &["git", "-p", "log"]),
            (&[], &["git", "grep", "-O", "x"]),
            (&[], &["git", "grep", "--open-files-in-pager=./x", "x"]),
            // A remote transport.
            (&[], &["git", "push"]),
            (&[], &["git", "ls-remote", "origin"]),
            // Reads of objects and refs, writes of refs.
            (&[], &["git", "--no-pager", "log", "--oneline"]),
            (
                &[],
                &["git", "log", "--format=%h %s", "--", "src/signature.rs"],
            ),
            (&[], &["git", "show", "HEAD"]),
            (&[], &["git", "diff", "--cached"]),
            (&[], &["git", "rev-parse", "HEAD"]),
            (&[], &["git", "grep", "-n", "x"]),
            (&[], &["git", "branch", "-a"]),
            (&[], &["git", "branch", "--list", "feat*"]),
            (&[], &["git", "branch", "topic"]),
            (&[], &["git", "branch", "-D", "topic"]),
            (&[], &["git", "symbolic-ref", "HEAD"]),
            (&[], &["git", "log", "--output=f"]),
            (&[], &["git"]),
        ];
        assert_eq!(
            effects(cases),
            sets(&[
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec],
                &[Exec, Net],
                &[Exec, Net],
                &[Read],
                &[Read],
                &[Read],
                &[Read],
                &[Read],
                &[Read],
                &[Read],
                &[Read],
                &[Write],
                &[Write],
                &[Read],
                &[Read, Write],
                &[Read],
            ])
        );
    }

    /// A `git` step that is not `Exec` runs with the untrusted-repository
    /// arguments (and a diffing one without external diff and textconv
    /// drivers); an `Exec` one runs as written.
    #[test]
    fn a_git_step_that_is_not_exec_runs_with_the_untrusted_repository_arguments() {
        let rewritten: Vec<Vec<String>> = [
            &["git", "-C", "r", "log", "-p"][..],
            &["git", "rev-parse", "HEAD"],
            &["git", "status"],
        ]
        .iter()
        .map(|words| {
            let mut words: Vec<String> = words.iter().map(ToString::to_string).collect();
            classify(&[], &mut words);
            words
        })
        .collect();
        let with = |rest: &[&str]| -> Vec<String> {
            std::iter::once("git")
                .chain(GIT_UNTRUSTED_REPO_ARGS)
                .chain(rest.iter().copied())
                .map(ToString::to_string)
                .collect()
        };
        assert_eq!(
            rewritten,
            vec![
                with(&["-C", "r", "log", "--no-ext-diff", "--no-textconv", "-p"]),
                with(&["rev-parse", "HEAD"]),
                vec!["git".to_string(), "status".to_string()],
            ]
        );
    }

    #[test]
    fn reading_commands_with_options_that_run_or_write_are_not_read() {
        let cases: &[Case] = &[
            // rg: a preprocessor or a hostname program.
            (&[], &["rg", "--pre=./x", "y"]),
            (&[], &["rg", "--pre-glob", "*", "y"]),
            (&[], &["rg", "--hostname-bin=./x", "y"]),
            (&[], &["rg", "-n", "y"]),
            // sort: a compressor or an output file.
            (&[], &["sort", "--compress-program=./x", "f"]),
            (&[], &["sort", "--compress=./x", "f"]),
            (&[], &["sort", "-o", "out", "f"]),
            (&[], &["sort", "-uo", "out", "f"]),
            (&[], &["sort", "--output=out", "f"]),
            (&[], &["sort", "--out", "out", "f"]),
            (&[], &["sort", "-n", "f"]),
            // uniq and xxd: a second operand is the output file.
            (&[], &["uniq", "in", "out"]),
            (&[], &["uniq", "-", "out"]),
            (&[], &["uniq", "-f", "2", "in"]),
            (&[], &["xxd", "-r", "in", "out"]),
            (&[], &["xxd", "in", "out"]),
            (&[], &["xxd", "-l", "64", "in"]),
            // find: every file-writing action.
            (&[], &["find", ".", "-fprint0", "out"]),
            // tree is not in the table.
            (&[], &["tree", "-o", "out"]),
            // less: a log file or a shell command.
            (&[], &["less", "-o", "out", "f"]),
            (&[], &["less", "--LOG-FILE=out", "f"]),
            (&[], &["less", "+!x", "f"]),
            // file: a compiled magic file.
            (&[], &["file", "-C", "-m", "m"]),
        ];
        assert_eq!(
            effects(cases),
            sets(&[
                &[Exec],
                &[Exec],
                &[Exec],
                &[Read],
                &[Exec],
                &[Exec],
                &[Write],
                &[Write],
                &[Write],
                &[Write],
                &[Read],
                &[Write],
                &[Write],
                &[Read],
                &[Write],
                &[Write],
                &[Read],
                &[Write],
                &[Exec],
                &[Write],
                &[Write],
                &[Exec],
                &[Write],
            ])
        );
    }

    #[test]
    fn only_known_safe_sed_scripts_are_read() {
        let cases: &[Case] = &[
            // Read: print, delete, quit, substitute, transliterate.
            (&[], &["sed", "-n", "1,5p", "f"]),
            (&[], &["sed", "-n", "$p", "f"]),
            (&[], &["sed", "-n", "/a\\/b/p", "f"]),
            (&[], &["sed", "s/a/b/g", "f"]),
            (&[], &["sed", "-E", "-e", "s|a;b|c|2", "-e", "3d", "f"]),
            (&[], &["sed", "--expression=y/ab/cd/", "f"]),
            (&[], &["sed", "-ne", "/x/{p;q}", "f"]),
            (&[], &["sed", "1!d; s/x/y/; $=", "f"]),
            // Exec: a command or a flag that runs a program or writes.
            (&[], &["sed", "s/x/y/e", "f"]),
            (&[], &["sed", "1e date", "f"]),
            (&[], &["sed", "-n", "w out", "f"]),
            (&[], &["sed", "s/x/y/w out", "f"]),
            (&[], &["sed", "-n", "1W out", "f"]),
            (&[], &["sed", "s/a/b/;w out", "f"]),
            (&[], &["sed", "-e", "p", "-e", "e date", "f"]),
            (&[], &["sed", "r /etc/passwd", "f"]),
            (&[], &["sed", "s/x/y/", "-f", "script", "f"]),
            (&[], &["sed", "-nf", "script", "f"]),
            (&[], &["sed", "s/x/y", "f"]),
            // Write: in place, with a safe script.
            (&[], &["sed", "-i.bak", "s/a/b/", "f"]),
            (&[], &["sed", "--in-place", "s/a/b/", "f"]),
            // Exec over Write: in place, with a script that runs.
            (&[], &["sed", "-i", "s/a/b/e", "f"]),
        ];
        let mut expected: Vec<&[ShellEffect]> = vec![&[Read]; 8];
        expected.extend([&[Exec][..]; 11]);
        expected.extend([&[Write][..], &[Write], &[Exec]]);
        assert_eq!(effects(cases), sets(&expected));
    }

    #[test]
    fn a_command_reads_the_working_directory_only_when_it_names_no_path() {
        let cases: &[&[&str]] = &[
            // Reads it: lists, walks or searches it.
            &["ls"],
            &["ls", "-la", "-w", "80"],
            &["du", "-sh"],
            &["find"],
            &["find", "-L", "-name", "x"],
            &["rg", "x"],
            &["rg", "-n", "-g", "*.rs", "x"],
            &["rg", "--files"],
            &["rg", "--max-count", "3", "x"],
            &["grep", "-r", "x"],
            &["grep", "-rn", "--include", "*.rs", "x"],
            &["grep", "-R", "-e", "x"],
            &["git", "grep", "x"],
            &["git", "grep", "x", "HEAD"],
            &["git", "--no-pager", "ls-files"],
            // Reads only what it names, or its input.
            &["ls", "src"],
            &["ls", "-w", "80", "src"],
            &["ls", "--", "-weird"],
            &["du", "-d", "1", "src"],
            &["find", ".", "-name", "x"],
            &["find", "-H", "src"],
            &["rg", "x", "src"],
            &["rg", "-e", "x", "src"],
            &["rg", "-ex", "src"],
            &["rg", "--files", "src"],
            &["grep", "-r", "x", "src"],
            &["grep", "x"],
            &["grep", "-n", "x", "f"],
            &["git", "grep", "x", "--", "src"],
            &["git", "-C", "repo", "grep", "x"],
            &["git", "ls-files", "src"],
            &["git", "log"],
            &["echo", "hi"],
            &["date"],
            &["cat"],
            &["tool"],
            &[],
        ];
        let got: Vec<bool> = cases
            .iter()
            .map(|words| reads_cwd(&words.iter().map(ToString::to_string).collect::<Vec<_>>()))
            .collect();
        let mut expected = vec![true; 15];
        expected.extend([false; 22]);
        assert_eq!(got, expected);
    }
}
