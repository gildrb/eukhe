//! Word expansion: parameters (`$NAME`, `${NAME}`, `$?`), a leading `~`,
//! field splitting of unquoted parameters on blanks, and pathname
//! expansion of unquoted `*`, `?`, `[`. A pattern that matches nothing
//! stays as written, as in bash.

use std::collections::BTreeMap;
use std::path::Path;

use crate::parse::{Part, Quoting, Word};

/// What expansion reads: the shell's variables, the last status, the
/// directory patterns are relative to.
pub(crate) struct Scope<'a> {
    pub vars: &'a BTreeMap<String, String>,
    pub status: i32,
    pub cwd: &'a Path,
}

/// One field being built: its text, the same text as a glob pattern
/// (quoted characters escaped), and whether an unquoted pattern character
/// is in it.
#[derive(Default)]
struct Field {
    text: String,
    pattern: String,
    glob: bool,
}

impl Field {
    fn push(&mut self, c: char, quoting: Quoting) {
        self.text.push(c);
        match quoting {
            Quoting::Bare => match c {
                '*' | '?' | '[' => {
                    self.glob = true;
                    self.pattern.push(c);
                }
                '{' | '}' | '\\' | ',' => {
                    self.pattern.push('\\');
                    self.pattern.push(c);
                }
                c => self.pattern.push(c),
            },
            Quoting::Quoted => {
                if matches!(c, '*' | '?' | '[' | ']' | '{' | '}' | '\\' | '!' | ',') {
                    self.pattern.push('\\');
                }
                self.pattern.push(c);
            }
        }
    }
}

impl Scope<'_> {
    fn value(&self, part: &Part) -> String {
        match part {
            Part::Lit { text, .. } => text.clone(),
            Part::Var { name, .. } => self.vars.get(name).cloned().unwrap_or_default(),
            Part::Status { .. } => self.status.to_string(),
            Part::Tilde => self
                .vars
                .get("HOME")
                .cloned()
                .unwrap_or_else(|| "~".to_string()),
        }
    }

    /// The word as one string: no splitting, no pathname expansion
    /// (assignment values, redirection targets).
    pub(crate) fn text(&self, word: &Word) -> String {
        word.parts.iter().map(|part| self.value(part)).collect()
    }

    /// The word's fields after splitting and pathname expansion.
    pub(crate) fn fields(&self, word: &Word) -> Vec<String> {
        let mut done = Vec::new();
        let mut field: Option<Field> = None;
        for part in &word.parts {
            match part {
                Part::Lit { text, quoting } => {
                    let current = field.get_or_insert_with(Field::default);
                    for c in text.chars() {
                        current.push(c, *quoting);
                    }
                }
                Part::Var {
                    quoting: Quoting::Quoted,
                    ..
                }
                | Part::Status {
                    quoting: Quoting::Quoted,
                }
                | Part::Tilde => {
                    let current = field.get_or_insert_with(Field::default);
                    for c in self.value(part).chars() {
                        current.push(c, Quoting::Quoted);
                    }
                }
                Part::Var {
                    quoting: Quoting::Bare,
                    ..
                }
                | Part::Status {
                    quoting: Quoting::Bare,
                } => {
                    let value = self.value(part);
                    for (at, piece) in value.split([' ', '\t', '\n']).enumerate() {
                        if at > 0 {
                            done.extend(field.take());
                        }
                        for c in piece.chars() {
                            field
                                .get_or_insert_with(Field::default)
                                .push(c, Quoting::Bare);
                        }
                    }
                }
            }
        }
        done.extend(field);
        done.into_iter()
            .flat_map(|field| {
                let matches = if field.glob {
                    glob(self.cwd, &field.text, &field.pattern)
                } else {
                    Vec::new()
                };
                if matches.is_empty() {
                    vec![field.text]
                } else {
                    matches
                }
            })
            .collect()
    }
}

/// The segment holds an unescaped pattern character.
fn has_meta(pattern: &str) -> bool {
    let mut escaped = false;
    for c in pattern.chars() {
        match (escaped, c) {
            (true, _) => escaped = false,
            (false, '\\') => escaped = true,
            (false, '*' | '?' | '[') => return true,
            (false, _) => {}
        }
    }
    false
}

/// Join a path prefix and a name.
fn join(base: &str, name: &str) -> String {
    if base.is_empty() {
        name.to_string()
    } else if base.ends_with('/') {
        format!("{base}{name}")
    } else {
        format!("{base}/{name}")
    }
}

/// The paths under `cwd` the pattern matches, sorted; one segment at a
/// time, hidden names only for a segment that starts with `.`.
fn glob(cwd: &Path, text: &str, pattern: &str) -> Vec<String> {
    let mut bases = vec![String::new()];
    for (at, (literal, segment)) in text.split('/').zip(pattern.split('/')).enumerate() {
        if at == 0 && literal.is_empty() {
            bases = vec!["/".to_string()];
            continue;
        }
        if !has_meta(segment) {
            for base in &mut bases {
                *base = join(base, literal);
            }
            continue;
        }
        let Ok(matcher) = globset::GlobBuilder::new(segment)
            .literal_separator(true)
            .backslash_escape(true)
            .build()
            .map(|glob| glob.compile_matcher())
        else {
            return Vec::new();
        };
        let mut next = Vec::new();
        for base in &bases {
            let dir = cwd.join(if base.is_empty() { "." } else { base });
            let Ok(entries) = std::fs::read_dir(dir) else {
                continue;
            };
            let mut names: Vec<String> = entries
                .filter_map(Result::ok)
                .map(|entry| entry.file_name().to_string_lossy().into_owned())
                .filter(|name| !name.starts_with('.') || literal.starts_with('.'))
                .filter(|name| matcher.is_match(name))
                .collect();
            names.sort();
            next.extend(names.iter().map(|name| join(base, name)));
        }
        bases = next;
    }
    bases.retain(|path| cwd.join(path).symlink_metadata().is_ok());
    bases.sort();
    bases
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse;

    /// The fields of every word of the script's first command.
    fn expand(script: &str, scope: &Scope<'_>) -> Vec<String> {
        let list = parse(script).unwrap();
        list[0].first.commands[0]
            .words
            .iter()
            .flat_map(|word| scope.fields(word))
            .collect()
    }

    #[test]
    fn parameters_split_and_patterns_expand() {
        let dir = tempfile::tempdir().unwrap();
        for path in ["a.rs", "b.rs", ".hidden.rs", "src/c.rs", "src/d.txt"] {
            let path = dir.path().join(path);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, "").unwrap();
        }
        let vars = BTreeMap::from([
            ("HOME".to_string(), "/home/u".to_string()),
            ("TWO".to_string(), " x  y ".to_string()),
            ("EMPTY".to_string(), String::new()),
        ]);
        let scope = Scope {
            vars: &vars,
            status: 3,
            cwd: dir.path(),
        };
        assert_eq!(
            expand(
                "echo *.rs src/*.rs '*.rs' *.none a$TWO\"$TWO\" $EMPTY \"\" ~/k $? */c.rs",
                &scope
            ),
            vec![
                "echo",
                "a.rs",
                "b.rs",
                "src/c.rs",
                "*.rs",
                "*.none",
                "a",
                "x",
                "y",
                " x  y ",
                "",
                "/home/u/k",
                "3",
                "src/c.rs",
            ]
        );
    }
}
