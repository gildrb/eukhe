//! Deliberate breaks of one changed line (mutants): a flipped comparison,
//! a swapped boolean operator or literal, a number off by one, a dropped
//! negation, a dropped statement. The operators know the language of the
//! file where that is cheap (Rust, TypeScript and JavaScript, Python,
//! Bend: the Bend skill's token and call operators); any other text file
//! gets the operators that need no grammar and a dropped line. Strings
//! and comments are never touched.

/// The language of a file, by its extension.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Lang {
    Rust,
    Script,
    Python,
    Bend,
    Other,
}

impl Lang {
    pub(crate) fn of(path: &str) -> Self {
        match path.rsplit_once('.').map(|(_, ext)| ext) {
            Some("rs") => Self::Rust,
            Some("ts" | "tsx" | "js" | "jsx" | "mjs" | "cjs" | "mts" | "cts") => Self::Script,
            Some("py") => Self::Python,
            Some("bend") => Self::Bend,
            _ => Self::Other,
        }
    }

    /// What opens a line comment.
    fn comment(self) -> &'static str {
        match self {
            Self::Rust | Self::Script => "//",
            Self::Python | Self::Bend | Self::Other => "#",
        }
    }
}

/// One break of one line: the line's new text and what changed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Mutant {
    pub(crate) path: String,
    /// From 1.
    pub(crate) line: u32,
    pub(crate) text: String,
    pub(crate) change: String,
}

/// Which bytes of `line` are code (not in a string literal or a comment).
fn code_mask(lang: Lang, line: &str) -> Vec<bool> {
    let bytes = line.as_bytes();
    let comment = lang.comment().as_bytes();
    let mut mask = vec![true; bytes.len()];
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i..].starts_with(comment) {
            mask[i..].fill(false);
            break;
        }
        let quote = bytes[i];
        let opens = match quote {
            b'"' => true,
            b'\'' => match lang {
                // A char literal ('x', '\n'); a lifetime ('a) is code.
                Lang::Rust => bytes.get(i + 1) == Some(&b'\\') || bytes.get(i + 2) == Some(&b'\''),
                Lang::Script | Lang::Python | Lang::Other => true,
                Lang::Bend => false,
            },
            b'`' => lang == Lang::Script,
            _ => false,
        };
        if !opens {
            i += 1;
            continue;
        }
        let start = i;
        i += 1;
        while i < bytes.len() && bytes[i] != quote {
            i += if bytes[i] == b'\\' { 2 } else { 1 };
        }
        let end = (i + 1).min(bytes.len());
        mask[start..end].fill(false);
        i = end;
    }
    mask
}

/// A word character.
fn word(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

/// Every place `token` stands in the code of `line` as its own token:
/// spaced (`a < b`) for an operator, word-bounded for a word.
fn places(line: &str, mask: &[bool], token: &str) -> Vec<usize> {
    let bytes = line.as_bytes();
    // An operator stands spaced; a word or a constructor stands alone.
    let spaced = !word(token.as_bytes()[0]);
    line.match_indices(token)
        .map(|(at, _)| at)
        .filter(|&at| mask[at..at + token.len()].iter().all(|code| *code))
        .filter(|&at| {
            let before = at.checked_sub(1).map(|i| bytes[i]);
            let after = bytes.get(at + token.len()).copied();
            if spaced {
                before == Some(b' ') && after == Some(b' ')
            } else {
                !before.is_some_and(|b| word(b) || b == b'.')
                    && !after.is_some_and(|b| word(b) || (token.ends_with('}') && b == b'{'))
            }
        })
        .collect()
}

/// The token swaps of a language: (from, to).
fn swaps(lang: Lang) -> Vec<(&'static str, &'static str)> {
    let mut ops = vec![
        ("<", "<="),
        ("<=", "<"),
        (">", ">="),
        (">=", ">"),
        ("+", "-"),
        ("-", "+"),
        ("*", "+"),
    ];
    match lang {
        Lang::Rust | Lang::Script => ops.extend([
            ("==", "!="),
            ("!=", "=="),
            ("&&", "||"),
            ("||", "&&"),
            ("true", "false"),
            ("false", "true"),
        ]),
        Lang::Python => ops.extend([
            ("==", "!="),
            ("!=", "=="),
            ("and", "or"),
            ("or", "and"),
            ("True", "False"),
            ("False", "True"),
        ]),
        Lang::Bend => ops.extend([
            ("True{}", "False{}"),
            ("False{}", "True{}"),
            ("&&", "||"),
            ("||", "&&"),
        ]),
        Lang::Other => ops.extend([("==", "!="), ("!=", "=="), ("&&", "||"), ("||", "&&")]),
    }
    if lang == Lang::Script {
        ops.extend([("===", "!=="), ("!==", "===")]);
    }
    ops
}

/// The Bend skill's call operators: `Type.verb(` to its mutants.
const BEND_VERBS: &[(&str, &[&str])] = &[
    ("is_lt", &["is_le", "is_gt"]),
    ("is_le", &["is_lt"]),
    ("is_gt", &["is_ge", "is_lt"]),
    ("is_ge", &["is_gt"]),
    ("is_eq", &["is_ne"]),
    ("is_ne", &["is_eq"]),
    ("add", &["sub"]),
    ("sub", &["add"]),
    ("mul", &["add"]),
    ("and", &["or"]),
    ("or", &["and"]),
    ("min", &["max"]),
    ("max", &["min"]),
];

/// `line` with `len` bytes at `at` replaced by `new`.
fn splice(line: &str, at: usize, len: usize, new: &str) -> String {
    format!("{}{new}{}", &line[..at], &line[at + len..])
}

/// The integer literals of the code of `line`: (start, digits).
fn numbers(lang: Lang, line: &str, mask: &[bool]) -> Vec<(usize, usize)> {
    let bytes = line.as_bytes();
    let mut found = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        if !bytes[i].is_ascii_digit() || !mask[i] {
            i += 1;
            continue;
        }
        let start = i;
        while i < bytes.len() && bytes[i].is_ascii_digit() {
            i += 1;
        }
        let before = start.checked_sub(1).map(|j| bytes[j]);
        let after = bytes.get(i).copied();
        // Not part of a name, a float, a version or a Bend quantity (`&2`).
        let alone = !before.is_some_and(|b| word(b) || b == b'.' || b == b'&')
            && match after {
                Some(b'n') => lang == Lang::Bend && !bytes.get(i + 1).copied().is_some_and(word),
                Some(b) => !word(b) && b != b'.',
                None => true,
            };
        if alone && i - start <= 9 {
            found.push((start, i - start));
        }
    }
    found
}

/// A line that is one statement the program can lose: it ends with `;`
/// (Rust, scripts) or is a plain Python statement, and declares nothing.
fn droppable(lang: Lang, trimmed: &str) -> bool {
    const DECLARES: &[&str] = &[
        "let ",
        "const ",
        "use ",
        "import ",
        "export ",
        "pub ",
        "fn ",
        "mod ",
        "type ",
        "struct ",
        "enum ",
        "impl ",
        "return",
        "#[",
        "@",
        "def ",
        "class ",
        "from ",
        "var ",
        "function ",
        "interface ",
    ];
    let declares = DECLARES.iter().any(|word| trimmed.starts_with(word));
    match lang {
        Lang::Rust | Lang::Script => trimmed.ends_with(';') && !declares,
        Lang::Python => {
            const BLOCKS: &[&str] = &[
                "if ", "elif ", "else", "for ", "while ", "try", "except", "finally", "with ",
                "pass", "break", "continue", "raise",
            ];
            !declares
                && !trimmed.ends_with(':')
                && !trimmed.ends_with(['(', '[', '{', ',', '\\'])
                && !BLOCKS.iter().any(|word| trimmed.starts_with(word))
        }
        Lang::Other => !declares,
        Lang::Bend => false,
    }
}

/// Every break of line `number` (text `line`) of the file at `path`.
pub(crate) fn of_line(path: &str, number: u32, line: &str) -> Vec<Mutant> {
    let lang = Lang::of(path);
    let trimmed = line.trim_start();
    if trimmed.is_empty()
        || trimmed.starts_with(lang.comment())
        || trimmed.starts_with("/*")
        || trimmed.starts_with('*')
    {
        return Vec::new();
    }
    let mask = code_mask(lang, line);
    let mut found: Vec<(String, String)> = Vec::new();
    for (from, to) in swaps(lang) {
        for at in places(line, &mask, from) {
            found.push((
                splice(line, at, from.len(), to),
                format!("`{from}` to `{to}`"),
            ));
        }
    }
    if lang == Lang::Bend {
        for (verb, others) in BEND_VERBS {
            let call = format!(".{verb}(");
            for (at, _) in line.match_indices(&call) {
                if !mask[at] {
                    continue;
                }
                for other in *others {
                    found.push((
                        splice(line, at + 1, verb.len(), other),
                        format!("`{verb}` to `{other}`"),
                    ));
                }
            }
        }
    }
    for (at, len) in numbers(lang, line, &mask) {
        let old = &line[at..at + len];
        if let Ok(value) = old.parse::<u64>() {
            let new = value.saturating_add(1).to_string();
            found.push((splice(line, at, len, &new), format!("`{old}` to `{new}`")));
        }
    }
    match lang {
        Lang::Rust | Lang::Script => {
            for (at, _) in line.match_indices('!') {
                let next = line.as_bytes().get(at + 1).copied();
                if mask[at] && next.is_some_and(|b| word(b) || b == b'(') {
                    found.push((splice(line, at, 1, ""), "`!` dropped".to_owned()));
                }
            }
        }
        Lang::Python => {
            for at in places(line, &mask, "not") {
                found.push((splice(line, at, 4, ""), "`not` dropped".to_owned()));
            }
        }
        Lang::Bend | Lang::Other => {}
    }
    if droppable(lang, trimmed) {
        let indent = &line[..line.len() - trimmed.len()];
        let text = match lang {
            // An empty block is no Python: the statement becomes `pass`.
            Lang::Python => format!("{indent}pass"),
            Lang::Rust | Lang::Script | Lang::Bend | Lang::Other => String::new(),
        };
        found.push((text, "line dropped".to_owned()));
    }
    found
        .into_iter()
        .filter(|(text, _)| text != line)
        .map(|(text, change)| Mutant {
            path: path.to_owned(),
            line: number,
            text,
            change,
        })
        .collect()
}

/// At most `max` of `mutants`, spread over the lines: one break of each
/// line in turn (the `seed`-th of that line's breaks first), so a large
/// change is sampled across its lines rather than at its start.
pub(crate) fn sample(mutants: Vec<Mutant>, max: usize, seed: u64) -> Vec<Mutant> {
    let mut lines: Vec<Vec<Mutant>> = Vec::new();
    for mutant in mutants {
        match lines.last_mut() {
            Some(last) if last[0].path == mutant.path && last[0].line == mutant.line => {
                last.push(mutant);
            }
            Some(_) | None => lines.push(vec![mutant]),
        }
    }
    for breaks in &mut lines {
        let turn = usize::try_from(seed % u64::try_from(breaks.len()).unwrap_or(1)).unwrap_or(0);
        breaks.rotate_left(turn);
        breaks.reverse();
    }
    let mut picked = Vec::with_capacity(max);
    while picked.len() < max && lines.iter().any(|breaks| !breaks.is_empty()) {
        for breaks in &mut lines {
            if picked.len() == max {
                break;
            }
            if let Some(mutant) = breaks.pop() {
                picked.push(mutant);
            }
        }
    }
    picked
}

#[cfg(test)]
mod tests {
    use super::*;

    fn changes(path: &str, line: &str) -> Vec<String> {
        of_line(path, 1, line)
            .into_iter()
            .map(|mutant| format!("{} => {}", mutant.change, mutant.text))
            .collect()
    }

    #[test]
    fn each_language_breaks_its_code_and_never_its_strings_or_comments() {
        assert_eq!(
            changes(
                "src/lib.rs",
                "    if a < b && !done { total += 1; } // a < b"
            ),
            [
                "`<` to `<=` =>     if a <= b && !done { total += 1; } // a < b",
                "`&&` to `||` =>     if a < b || !done { total += 1; } // a < b",
                "`1` to `2` =>     if a < b && !done { total += 2; } // a < b",
                "`!` dropped =>     if a < b && done { total += 1; } // a < b",
            ]
        );
        assert_eq!(
            changes("app.py", "    return n > 0 and not seen  # n > 0"),
            [
                "`>` to `>=` =>     return n >= 0 and not seen  # n > 0",
                "`and` to `or` =>     return n > 0 or not seen  # n > 0",
                "`0` to `1` =>     return n > 1 and not seen  # n > 0",
                "`not` dropped =>     return n > 0 and seen  # n > 0",
            ]
        );
        assert_eq!(
            changes("app.py", "    total = total + price"),
            [
                "`+` to `-` =>     total = total - price",
                "line dropped =>     pass",
            ]
        );
        assert_eq!(
            changes("x.ts", "  log(\"a < b\", a === b);"),
            [
                "`===` to `!==` =>   log(\"a < b\", a !== b);",
                "line dropped => ",
            ]
        );
        assert_eq!(
            changes("bend/f.bend", "      Nat.is_le(a, 3n) => True{}"),
            [
                "`True{}` to `False{}` =>       Nat.is_le(a, 3n) => False{}",
                "`is_le` to `is_lt` =>       Nat.is_lt(a, 3n) => True{}",
                "`3` to `4` =>       Nat.is_le(a, 4n) => True{}",
            ]
        );
        assert!(changes("src/lib.rs", "// a < b").is_empty());
        assert!(changes("src/lib.rs", "fn f<'a>(x: &'a str) -> Vec<u8> {").is_empty());
    }

    #[test]
    fn a_sample_takes_one_break_of_each_line_in_turn() {
        let line = |line, change: &str| Mutant {
            path: "a.py".to_owned(),
            line,
            text: String::new(),
            change: change.to_owned(),
        };
        let all = vec![
            line(1, "a"),
            line(1, "b"),
            line(2, "c"),
            line(3, "d"),
            line(3, "e"),
        ];
        assert_eq!(
            sample(all.clone(), 4, 0),
            vec![line(1, "a"), line(2, "c"), line(3, "d"), line(1, "b")]
        );
        assert_eq!(
            sample(all, 3, 1),
            vec![line(1, "b"), line(2, "c"), line(3, "e")]
        );
    }
}
