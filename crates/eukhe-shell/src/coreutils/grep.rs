//! `grep` on ripgrep's engine (`grep-regex`, `grep-searcher`), with
//! `-i -v -n -c -l -q -s -r -R -F -E -w -x -h -H` and `-e PATTERN`.
//! Without `-E` or `-F` the pattern is a basic regular expression.

use std::io::Write as _;
use std::path::{Path, PathBuf};

use grep_regex::RegexMatcherBuilder;
use grep_searcher::sinks::Lossy;
use grep_searcher::SearcherBuilder;

use super::{broken, message, reason, Io};

/// A basic regular expression as the engine's syntax: `\(`, `\)`, `\{`,
/// `\}`, `\|`, `\+`, `\?` are the operators, their bare forms literals;
/// `\<` and `\>` are word boundaries; a leading `*` is literal.
fn basic(pattern: &str) -> String {
    let mut out = String::with_capacity(pattern.len());
    let mut chars = pattern.chars().peekable();
    let mut start = true;
    while let Some(c) = chars.next() {
        match c {
            '\\' => match chars.next() {
                Some(op @ ('(' | ')' | '{' | '}' | '|' | '+' | '?')) => out.push(op),
                Some('<' | '>') => out.push_str("\\b"),
                Some(other) => {
                    out.push('\\');
                    out.push(other);
                }
                None => out.push_str("\\\\"),
            },
            '(' | ')' | '{' | '}' | '|' | '+' | '?' => {
                out.push('\\');
                out.push(c);
            }
            '*' if start => out.push_str("\\*"),
            c => out.push(c),
        }
        start = c == '^' && out.len() == 1;
    }
    out
}

/// Every file under `path`, in name order.
fn walk(path: &Path, files: &mut Vec<PathBuf>) {
    if path.is_dir() {
        let Ok(entries) = std::fs::read_dir(path) else {
            files.push(path.to_path_buf());
            return;
        };
        let mut children: Vec<PathBuf> = entries.filter_map(Result::ok).map(|e| e.path()).collect();
        children.sort();
        for child in children {
            walk(&child, files);
        }
    } else {
        files.push(path.to_path_buf());
    }
}

#[allow(clippy::too_many_lines)] // Option parsing, matching and the output modes of one command.
pub(super) fn grep(args: &[String], cwd: &Path, io: &mut Io) -> Option<i32> {
    let mut set = String::new();
    let mut patterns = Vec::new();
    let mut operands = Vec::new();
    let mut rest = args.iter();
    let mut ended = false;
    while let Some(arg) = rest.next() {
        if ended || arg == "-" || !arg.starts_with('-') {
            operands.push(arg.as_str());
        } else if arg == "--" {
            ended = true;
        } else if arg.starts_with("--color") {
        } else if arg == "-e" {
            patterns.push(rest.next()?.clone());
        } else {
            for flag in arg[1..].chars() {
                if !"ivnclqsrRFEwxhH".contains(flag) {
                    return None;
                }
                set.push(flag);
            }
        }
    }
    if patterns.is_empty() {
        if operands.is_empty() {
            return None;
        }
        patterns.push(operands.remove(0).to_string());
    }
    let Io {
        stdin,
        stdout,
        stderr,
    } = io;
    let has = |flag: char| set.contains(flag);
    let recursive = has('r') || has('R');
    let pattern = if has('F') || has('E') {
        patterns.join("\n")
    } else {
        patterns
            .iter()
            .map(|p| basic(p))
            .collect::<Vec<_>>()
            .join("\n")
    };
    let matcher = match RegexMatcherBuilder::new()
        .case_insensitive(has('i'))
        .word(has('w'))
        .whole_line(has('x'))
        .fixed_strings(has('F'))
        .build(&pattern)
    {
        Ok(matcher) => matcher,
        Err(error) => {
            message(*stderr, "grep", &error.to_string());
            return Some(2);
        }
    };
    // The `Lossy` sink needs line numbers; `-n` decides whether they show.
    let mut searcher = SearcherBuilder::new()
        .line_number(true)
        .invert_match(has('v'))
        .build();
    // The inputs: `None` is stdin.
    let mut inputs: Vec<(String, Option<PathBuf>)> = Vec::new();
    if operands.is_empty() && recursive {
        operands.push(".");
    }
    if operands.is_empty() {
        inputs.push(("(standard input)".to_string(), None));
    }
    let mut failed = false;
    for operand in &operands {
        let path = cwd.join(operand);
        if *operand == "-" {
            inputs.push(("(standard input)".to_string(), None));
        } else if recursive && path.is_dir() {
            let mut files = Vec::new();
            walk(&path, &mut files);
            for file in files {
                let shown = file.strip_prefix(cwd).map_or_else(
                    |_| file.display().to_string(),
                    |relative| {
                        let relative = relative.display().to_string();
                        if operand.starts_with("./") || *operand == "." {
                            format!("./{}", relative.trim_start_matches("./"))
                        } else {
                            relative
                        }
                    },
                );
                inputs.push((shown, Some(file)));
            }
        } else if path.is_dir() {
            failed = true;
            if !has('s') {
                message(*stderr, "grep", &format!("{operand}: Is a directory"));
            }
        } else {
            inputs.push(((*operand).to_string(), Some(path)));
        }
    }
    let named = has('H') || (!has('h') && (operands.len() > 1 || recursive));
    let stop_at_first = has('l') || has('q');
    let mut found = false;
    for (name, path) in inputs {
        let mut count = 0u64;
        // A line that could not be written ends the search.
        let mut unwritten: Option<std::io::Error> = None;
        let sink = Lossy(|number, line| {
            count += 1;
            if !stop_at_first && !has('c') {
                let mut text = String::new();
                if named {
                    text.push_str(&name);
                    text.push(':');
                }
                if has('n') {
                    text.push_str(&number.to_string());
                    text.push(':');
                }
                text.push_str(line);
                if !line.ends_with('\n') {
                    text.push('\n');
                }
                if let Err(error) = stdout.write_all(text.as_bytes()) {
                    let kind = error.kind();
                    unwritten = Some(error);
                    return Err(kind.into());
                }
            }
            Ok(!stop_at_first)
        });
        let outcome = match &path {
            Some(path) => searcher.search_path(&matcher, path, sink),
            None => searcher.search_reader(&matcher, &mut **stdin, sink),
        };
        if let Some(error) = unwritten {
            return Some(broken("grep", &error, *stderr));
        }
        if let Err(error) = outcome {
            failed = true;
            if !has('s') {
                message(*stderr, "grep", &format!("{name}: {}", reason(&error)));
            }
            continue;
        }
        found |= count > 0;
        let summary = if has('q') {
            if found {
                break;
            }
            None
        } else if has('l') {
            (count > 0).then(|| format!("{name}\n"))
        } else if has('c') {
            Some(if named {
                format!("{name}:{count}\n")
            } else {
                format!("{count}\n")
            })
        } else {
            None
        };
        if let Some(summary) = summary {
            if let Err(error) = stdout.write_all(summary.as_bytes()) {
                return Some(broken("grep", &error, *stderr));
            }
        }
    }
    Some(if has('q') && found {
        0
    } else if failed {
        2
    } else {
        i32::from(!found)
    })
}

#[cfg(test)]
mod tests {
    use super::super::{captured, Output};

    fn argv(words: &[&str]) -> Vec<String> {
        words.iter().map(ToString::to_string).collect()
    }

    #[test]
    fn grep_matches_like_gnu_grep() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::create_dir(dir.path().join("d")).unwrap();
        std::fs::write(dir.path().join("d/a"), "foo(1)\nbar\nFoo\n").unwrap();
        std::fs::write(dir.path().join("d/b"), "nothing\n").unwrap();
        let cases: Vec<(&[&str], &[u8])> = vec![
            (&["grep", "-n", "foo(1)", "d/a"], b""),
            (&["grep", "-ic", "foo", "d/a", "d/b"], b""),
            (&["grep", "-r", "-l", "o", "d"], b""),
            (&["grep", "-v", "\\(ba\\)\\+"], b"bar\nbaz\nqux\n"),
            (&["grep", "-E", "-x", "ba(r|z)"], b"bar\nbaz\nqux\n"),
            (&["grep", "zzz", "d/a", "d/missing"], b""),
            (&["grep", "-o", "x"], b""),
        ];
        let got: Vec<Option<Output>> = cases
            .iter()
            .map(|(words, stdin)| captured(&argv(words), dir.path(), stdin))
            .collect();
        let ok = |text: &str| {
            Some(Output {
                stdout: text.as_bytes().to_vec(),
                ..Output::default()
            })
        };
        assert_eq!(
            got,
            vec![
                ok("1:foo(1)\n"),
                ok("d/a:2\nd/b:0\n"),
                ok("d/a\nd/b\n"),
                ok("qux\n"),
                ok("bar\nbaz\n"),
                Some(Output {
                    stderr: b"grep: d/missing: No such file or directory\n".to_vec(),
                    status: 2,
                    ..Output::default()
                }),
                None,
            ]
        );
    }
}
