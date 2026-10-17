//! The classification table: the effect of one step from its assignments
//! and expanded words. A command the table does not know is `Exec`; a
//! redirection that writes a file makes a `Read` step `Write` (the caller
//! adds that).

use eukhe_types::shell::ShellEffect;

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
/// `--exec-path`, `--git-dir`, ...) makes the step `Exec`.
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

/// `git` subcommands that only read the repository.
const GIT_READ: &[&str] = &[
    "blame",
    "cat-file",
    "describe",
    "diff",
    "grep",
    "log",
    "ls-files",
    "ls-tree",
    "merge-base",
    "name-rev",
    "reflog",
    "rev-list",
    "rev-parse",
    "shortlog",
    "show",
    "status",
    "whatchanged",
];

/// `git` subcommands that talk to a remote.
const GIT_NET: &[&str] = &["clone", "fetch", "ls-remote", "pull", "push", "submodule"];

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

/// The effect of a step with the assignments `assigns` and the expanded
/// words `words` (no words: only assignments or redirections, which change
/// shell state).
#[allow(clippy::too_many_lines)] // One arm per command of the table.
pub(crate) fn classify(assigns: &[(String, String)], words: &[String]) -> ShellEffect {
    // An assignment changes the environment of the command, or alone of
    // every later command: `PATH`, `LD_PRELOAD`, `LESSOPEN` or `GIT_*`
    // make a reading command run another program.
    if !assigns.is_empty() {
        return ShellEffect::Exec;
    }
    let Some((program, args)) = words.split_first() else {
        return ShellEffect::Read;
    };
    match program.as_str() {
        "export" if args.is_empty() => ShellEffect::Read,
        // A word with `/` runs that file, whatever its name: the own
        // coreutils answer only a bare name. `export` with an operand
        // changes the environment, as an assignment does.
        name if name.contains('/') || name == "export" => ShellEffect::Exec,
        "git" => {
            // Options before the subcommand; `-C` takes a value.
            let mut rest = args.iter();
            let subcommand = loop {
                match rest.next() {
                    Some(arg) if arg == "-C" => {
                        rest.next();
                    }
                    Some(arg) if GIT_GLOBAL.contains(&arg.as_str()) => {}
                    Some(arg) if arg.starts_with('-') => return ShellEffect::Exec,
                    found => break found,
                }
            };
            let options = rest.as_slice();
            match subcommand {
                None => ShellEffect::Read,
                Some(sub)
                    if sub == "grep"
                        && options
                            .iter()
                            .any(|arg| short(arg, 'O') || long(arg, "open-files-in-pager")) =>
                {
                    ShellEffect::Exec
                }
                Some(sub) if GIT_READ.contains(&sub.as_str()) => {
                    if options.iter().any(|arg| long(arg, "output")) {
                        ShellEffect::Write
                    } else {
                        ShellEffect::Read
                    }
                }
                Some(sub) if GIT_NET.contains(&sub.as_str()) => ShellEffect::Net,
                Some(_) => ShellEffect::Write,
            }
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
                                None => return ShellEffect::Exec,
                            },
                        }
                    } else if !SED_LONG.iter().any(|name| long(arg, name)) {
                        return ShellEffect::Exec;
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
                                        None => return ShellEffect::Exec,
                                    }
                                } else {
                                    scripts.push(attached);
                                }
                                break;
                            }
                            _ => return ShellEffect::Exec,
                        }
                    }
                }
            }
            // Without `-e`, the first operand is the script.
            if scripts.is_empty() {
                match first_operand {
                    Some(script) => scripts.push(script),
                    None => return ShellEffect::Read,
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
                ShellEffect::Exec
            } else if in_place {
                ShellEffect::Write
            } else {
                ShellEffect::Read
            }
        }
        "find" => {
            if args
                .iter()
                .any(|arg| matches!(arg.as_str(), "-exec" | "-execdir" | "-ok" | "-okdir"))
            {
                ShellEffect::Exec
            } else if args.iter().any(|arg| {
                matches!(
                    arg.as_str(),
                    "-delete" | "-fls" | "-fprint" | "-fprint0" | "-fprintf"
                )
            }) {
                ShellEffect::Write
            } else {
                ShellEffect::Read
            }
        }
        "rg" if args
            .iter()
            .any(|arg| arg.starts_with("--pre") || arg.starts_with("--hostname-bin")) =>
        {
            ShellEffect::Exec
        }
        "sort" if args.iter().any(|arg| long(arg, "compress-program")) => ShellEffect::Exec,
        "sort"
            if args
                .iter()
                .any(|arg| short(arg, 'o') || long(arg, "output")) =>
        {
            ShellEffect::Write
        }
        // A second operand is the output file.
        "uniq" if operands(args, UNIQ_VALUED) >= 2 => ShellEffect::Write,
        "xxd" if operands(args, XXD_VALUED) >= 2 => ShellEffect::Write,
        "less"
            if args
                .iter()
                .any(|arg| arg.starts_with('+') && arg.contains(['!', '|'])) =>
        {
            ShellEffect::Exec
        }
        "less"
            if args.iter().any(|arg| {
                short(arg, 'o') || short(arg, 'O') || long(arg, "log-file") || long(arg, "LOG-FILE")
            }) =>
        {
            ShellEffect::Write
        }
        "file"
            if args
                .iter()
                .any(|arg| short(arg, 'C') || long(arg, "compile")) =>
        {
            ShellEffect::Write
        }
        "env" if args.is_empty() => ShellEffect::Read,
        name if READ.contains(&name) => ShellEffect::Read,
        name if WRITE.contains(&name) => ShellEffect::Write,
        name if NET.contains(&name) => ShellEffect::Net,
        _ => ShellEffect::Exec,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// One step: its assignments and its words.
    type Case = (
        &'static [(&'static str, &'static str)],
        &'static [&'static str],
    );

    /// The effect of each step.
    fn effects(cases: &[Case]) -> Vec<ShellEffect> {
        cases
            .iter()
            .map(|(assigns, words)| {
                classify(
                    &assigns
                        .iter()
                        .map(|(name, value)| (name.to_string(), value.to_string()))
                        .collect::<Vec<_>>(),
                    &words.iter().map(ToString::to_string).collect::<Vec<_>>(),
                )
            })
            .collect()
    }

    #[test]
    fn commands_classify_by_name_subcommand_and_option() {
        let cases: &[Case] = &[
            (&[], &["cat", "a"]),
            (&[], &["rm", "-rf", "x"]),
            (&[], &["curl", "https://example.com"]),
            (&[], &["python3", "x.py"]),
            (&[], &["git", "-C", "repo", "status"]),
            (&[], &["git", "commit", "-m", "x"]),
            (&[], &["git", "push"]),
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
            vec![
                ShellEffect::Read,
                ShellEffect::Write,
                ShellEffect::Net,
                ShellEffect::Exec,
                ShellEffect::Read,
                ShellEffect::Write,
                ShellEffect::Net,
                ShellEffect::Read,
                ShellEffect::Write,
                ShellEffect::Read,
                ShellEffect::Write,
                ShellEffect::Exec,
                ShellEffect::Read,
                ShellEffect::Exec,
                ShellEffect::Read,
            ]
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
        assert_eq!(effects(cases), vec![ShellEffect::Exec; 5]);
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
            vec![
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Read,
                ShellEffect::Read,
            ]
        );
    }

    #[test]
    fn reading_commands_with_options_that_run_or_write_are_not_read() {
        let cases: &[Case] = &[
            // git: configuration or a program before the subcommand.
            (&[], &["git", "-c", "core.fsmonitor=./x", "status"]),
            (&[], &["git", "-c", "diff.external=./x", "diff"]),
            (&[], &["git", "--config-env=core.sshCommand=X", "log"]),
            (&[], &["git", "--exec-path=./x", "status"]),
            (&[], &["git", "--git-dir=x", "status"]),
            (&[], &["git", "--no-pager", "log", "--oneline"]),
            (&[], &["git", "log", "--output=f"]),
            (&[], &["git", "diff", "--out", "f"]),
            (&[], &["git", "grep", "-O", "x"]),
            (&[], &["git", "grep", "--open-files-in-pager=./x", "x"]),
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
            vec![
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Read,
                ShellEffect::Write,
                ShellEffect::Write,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Read,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Write,
                ShellEffect::Write,
                ShellEffect::Write,
                ShellEffect::Write,
                ShellEffect::Read,
                ShellEffect::Write,
                ShellEffect::Write,
                ShellEffect::Read,
                ShellEffect::Write,
                ShellEffect::Write,
                ShellEffect::Read,
                ShellEffect::Write,
                ShellEffect::Exec,
                ShellEffect::Write,
                ShellEffect::Write,
                ShellEffect::Exec,
                ShellEffect::Write,
            ]
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
        assert_eq!(
            effects(cases),
            vec![
                ShellEffect::Read,
                ShellEffect::Read,
                ShellEffect::Read,
                ShellEffect::Read,
                ShellEffect::Read,
                ShellEffect::Read,
                ShellEffect::Read,
                ShellEffect::Read,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Exec,
                ShellEffect::Write,
                ShellEffect::Write,
                ShellEffect::Exec,
            ]
        );
    }
}
