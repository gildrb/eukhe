//! Glob patterns (`bend/glob.bend`, entry `bend/ffi_glob.bend`;
//! `laws/glob.bend`): the patterns of the `globset` crate 0.4.20 as eukhe
//! used it (`\` escapes, `{a,b}` alternates, `[..]` classes, `**`
//! segments; `empty_alternates` and `allow_unclosed_class` off), matched
//! against the UTF-8 bytes of the whole text. The compiled core parses
//! each pattern (or refuses it with globset's error), and decides every
//! match; Rust sends the patterns and texts and reads the answers.

use std::fmt;

use crate::wire::{Reader, WireError, Writer};
use crate::{call, Entry, Error};

/// The builder options a caller sets (globset's `GlobBuilder`).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct GlobOptions {
    /// `*` and `?` never match `/` (globset `literal_separator`).
    pub literal_separator: bool,
    /// ASCII letters match either case (globset `case_insensitive`).
    pub case_insensitive: bool,
}

/// Why globset refuses a pattern (globset `ErrorKind`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GlobErrorKind {
    /// A `[` with no `]`.
    UnclosedClass,
    /// A class range whose end is below its start.
    InvalidRange(char, char),
    /// A `}` outside any group.
    UnopenedAlternates,
    /// A `{` with no `}`.
    UnclosedAlternates,
    /// A `\` at the end of the pattern.
    DanglingEscape,
}

impl fmt::Display for GlobErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnclosedClass => f.write_str("unclosed character class; missing ']'"),
            Self::InvalidRange(lo, hi) => write!(f, "invalid range; '{lo}' > '{hi}'"),
            Self::UnopenedAlternates => {
                f.write_str("unopened alternate group; missing '{' (maybe escape '}' with '[}]'?)")
            }
            Self::UnclosedAlternates => {
                f.write_str("unclosed alternate group; missing '}' (maybe escape '{' with '[{]'?)")
            }
            Self::DanglingEscape => f.write_str("dangling '\\'"),
        }
    }
}

/// A pattern globset refuses, written as globset writes its error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GlobError {
    /// The refused pattern.
    pub glob: String,
    /// Why it is refused.
    pub kind: GlobErrorKind,
}

impl fmt::Display for GlobError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error parsing glob '{}': {}", self.glob, self.kind)
    }
}

impl std::error::Error for GlobError {}

fn read_char(reader: &mut Reader<'_>) -> Result<char, Error> {
    let code = reader.u32()?;
    char::from_u32(code).ok_or(Error::Wire(WireError::Malformed {
        at: 0,
        expected: "a char code",
    }))
}

/// Whether globset accepts `pattern`, else its error.
///
/// # Errors
///
/// A pattern past the wire's string bound, or a compiled-core failure.
pub fn check(pattern: &str) -> Result<Result<(), GlobError>, Error> {
    let reply = call(Entry::Glob, &Writer::new().tag(0).str(pattern).finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let verdict = if reader.maybe()? {
        let kind = match reader.tag_of(5, "a glob error")? {
            0 => GlobErrorKind::UnclosedClass,
            1 => {
                let lo = read_char(&mut reader)?;
                let hi = read_char(&mut reader)?;
                GlobErrorKind::InvalidRange(lo, hi)
            }
            2 => GlobErrorKind::UnopenedAlternates,
            3 => GlobErrorKind::UnclosedAlternates,
            // `tag_of` answers a tag below 5: this is 4.
            _ => GlobErrorKind::DanglingEscape,
        };
        Err(GlobError {
            glob: pattern.to_owned(),
            kind,
        })
    } else {
        Ok(())
    };
    reader.end()?;
    Ok(verdict)
}

/// For each group of texts, whether one of `patterns` matches one of its
/// texts whole. A pattern globset refuses matches nothing.
///
/// # Errors
///
/// A pattern or text past the wire's bounds, or a compiled-core failure.
pub fn match_groups<P: AsRef<str>, T: AsRef<str>>(
    options: GlobOptions,
    patterns: &[P],
    groups: &[Vec<T>],
) -> Result<Vec<bool>, Error> {
    let texts: Vec<&str> = groups.iter().flatten().map(AsRef::as_ref).collect();
    let sizes: Vec<usize> = groups.iter().map(Vec::len).collect();
    lists_query(1, options, patterns, &texts, &sizes)
}

/// For each rule (a list of patterns), whether one of its patterns
/// matches one of `texts` whole. A pattern globset refuses matches
/// nothing.
///
/// # Errors
///
/// A pattern or text past the wire's bounds, or a compiled-core failure.
pub fn match_rules<P: AsRef<str>, T: AsRef<str>>(
    options: GlobOptions,
    rules: &[Vec<P>],
    texts: &[T],
) -> Result<Vec<bool>, Error> {
    let patterns: Vec<&str> = rules.iter().flatten().map(AsRef::as_ref).collect();
    let sizes: Vec<usize> = rules.iter().map(Vec::len).collect();
    lists_query(3, options, &patterns, texts, &sizes)
}

/// The group query (tag 1: `sizes` group the texts) and the rules query
/// (tag 3: `sizes` group the patterns): the same fields on the wire.
fn lists_query<P: AsRef<str>, T: AsRef<str>>(
    tag: u32,
    options: GlobOptions,
    patterns: &[P],
    texts: &[T],
    sizes: &[usize],
) -> Result<Vec<bool>, Error> {
    let mut writer = Writer::new();
    writer
        .tag(tag)
        .bool(options.literal_separator)
        .bool(options.case_insensitive)
        .count(patterns.len());
    for pattern in patterns {
        writer.str(pattern.as_ref());
    }
    writer.count(texts.len());
    for text in texts {
        writer.str(text.as_ref());
    }
    writer.count(sizes.len());
    for size in sizes {
        writer.count(*size);
    }
    read_answers(&call(Entry::Glob, &writer.finish()?)?)
}

fn read_answers(reply: &str) -> Result<Vec<bool>, Error> {
    let mut reader = Reader::reply(reply)?;
    let count = reader.count()?;
    let mut answers = Vec::with_capacity(count);
    for _ in 0..count {
        answers.push(reader.bool()?);
    }
    reader.end()?;
    Ok(answers)
}

/// One gitignore-style rule, in the order its ignore file gives it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IgnoreRule {
    /// A glob (literal separators) that globset accepts: matched against
    /// the whole path (`anchored`) or any of its `/`-suffixes; a match
    /// keeps the path when `negated`; applied to directories only when
    /// `dir_only`.
    Glob {
        pattern: String,
        anchored: bool,
        negated: bool,
        dir_only: bool,
    },
    /// Every path that starts with `prefix` is ignored.
    Everything { prefix: String },
}

/// An entry of [`ignored`]: a root-relative path, and whether it is a
/// directory.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IgnoreEntry<'a> {
    pub path: &'a str,
    pub is_dir: bool,
}

/// For each entry, whether the ignore `rules` ignore it: the last rule
/// that decides it decides (a directory-only rule skips a file; a glob
/// rule decides when it matches: ignored unless negated; a prefix rule
/// decides, ignored, when the path starts with its prefix); no rule
/// deciding: not ignored.
///
/// # Errors
///
/// A rule or path past the wire's bounds, or a compiled-core failure.
pub fn ignored(rules: &[IgnoreRule], entries: &[IgnoreEntry<'_>]) -> Result<Vec<bool>, Error> {
    let mut writer = Writer::new();
    writer.tag(4).count(rules.len());
    for rule in rules {
        match rule {
            IgnoreRule::Glob { pattern, .. } => writer.str(pattern),
            IgnoreRule::Everything { prefix } => writer.str(prefix),
        };
    }
    writer.count(rules.len());
    for rule in rules {
        let code = match rule {
            IgnoreRule::Glob {
                anchored,
                negated,
                dir_only,
                ..
            } => u64::from(*anchored) + 2 * u64::from(*negated) + 4 * u64::from(*dir_only),
            IgnoreRule::Everything { .. } => 8,
        };
        writer.nat(code);
    }
    writer.count(entries.len());
    for entry in entries {
        let path = entry.path.strip_suffix('/').unwrap_or(entry.path);
        if entry.is_dir {
            writer.str(&format!("{path}/"));
        } else {
            writer.str(path);
        }
    }
    read_answers(&call(Entry::Glob, &writer.finish()?)?)
}

/// Whether one of `patterns` matches one of `texts` whole.
///
/// # Errors
///
/// A pattern or text past the wire's bounds, or a compiled-core failure.
pub fn matches_any<P: AsRef<str>, T: AsRef<str>>(
    options: GlobOptions,
    patterns: &[P],
    texts: &[T],
) -> Result<bool, Error> {
    let group: Vec<&str> = texts.iter().map(AsRef::as_ref).collect();
    Ok(match_groups(options, patterns, &[group])?.contains(&true))
}

/// Whether the daemon model allowlist `patterns` allows the model
/// `selector` (`provider/model-id`). The caller lowercases both (Rust
/// `to_lowercase`); the core decides: a pattern is trimmed, a blank one
/// never matches; one with `*`, `?` or `[` is a glob (globset defaults:
/// `*` crosses `/`; a refused glob matches nothing) of the whole selector
/// or its bare id (the text after its first `/`); any other must equal
/// one of them. An empty list allows nothing.
///
/// # Errors
///
/// A pattern or selector past the wire's bounds, or a compiled-core
/// failure.
pub fn model_allowed<P: AsRef<str>>(selector: &str, patterns: &[P]) -> Result<bool, Error> {
    let mut writer = Writer::new();
    writer.tag(2).str(selector).count(patterns.len());
    for pattern in patterns {
        writer.str(pattern.as_ref());
    }
    let reply = call(Entry::Glob, &writer.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let allowed = reader.bool()?;
    reader.end()?;
    Ok(allowed)
}

#[cfg(test)]
mod tests {
    use super::*;

    const SEP: GlobOptions = GlobOptions {
        literal_separator: true,
        case_insensitive: false,
    };

    /// The answers come from the compiled core: `*` stays in one segment
    /// with literal separators, `**/` spans them, a class takes one byte,
    /// case folds only when asked, and a refused pattern matches nothing.
    #[test]
    fn the_core_matches_globs() {
        let groups = vec![
            vec!["src/main.rs"],
            vec!["main.rs"],
            vec!["a/b/c.md"],
            vec!["é"],
            vec!["README.MD", "x"],
        ];
        let answers =
            match_groups(SEP, &["*.rs", "**/*.md", "??", "[a"], &groups).expect("the core answers");
        assert_eq!(answers, [false, true, true, true, false]);
        let folded = GlobOptions {
            literal_separator: true,
            case_insensitive: true,
        };
        assert!(matches_any(folded, &["*.md"], &["README.MD"]).expect("the core answers"));
    }

    /// Refused patterns carry globset's error kind and text.
    #[test]
    fn the_core_refuses_patterns_as_globset() {
        let errors = ["a[", "[z-a]", "a}", "{a", "a\\", "a/**/*.rs"]
            .map(|pattern| check(pattern).expect("the core answers").err());
        assert_eq!(
            errors.clone().map(|error| error.map(|error| error.kind)),
            [
                Some(GlobErrorKind::UnclosedClass),
                Some(GlobErrorKind::InvalidRange('z', 'a')),
                Some(GlobErrorKind::UnopenedAlternates),
                Some(GlobErrorKind::UnclosedAlternates),
                Some(GlobErrorKind::DanglingEscape),
                None,
            ]
        );
        assert_eq!(
            errors[1].as_ref().map(ToString::to_string).as_deref(),
            Some("error parsing glob '[z-a]': invalid range; 'z' > 'a'")
        );
    }

    /// The allowlist: exact selector or bare id, case as sent, globs whose
    /// `*` crosses `/`, blank and refused patterns never match.
    #[test]
    fn the_core_decides_the_model_allowlist() {
        let selector = "prime-inference/internal/glm-5.3-fast";
        let verdicts = [
            &["internal/glm-5.3-fast"][..],
            &["glm-5.3-fast"],
            &["prime-inference/*"],
            &["  internal/*  "],
            &["  "],
            &["["],
            &[],
        ]
        .map(|patterns| model_allowed(selector, patterns).expect("the core answers"));
        assert_eq!(verdicts, [true, false, true, true, false, false, false]);
    }

    /// Rules answer per rule; ignore rules: the last deciding rule wins,
    /// a directory-only rule skips files, a negated rule keeps a path.
    #[test]
    fn the_core_decides_rules_and_ignore_rules() {
        let folded = GlobOptions {
            literal_separator: true,
            case_insensitive: true,
        };
        let rules = [vec!["gpt-*", "x"], vec!["claude-*"]];
        assert_eq!(
            match_rules(folded, &rules, &["openai/GPT-5", "GPT-5"]).expect("the core answers"),
            [true, false]
        );
        let glob = |pattern: &str, anchored, negated, dir_only| IgnoreRule::Glob {
            pattern: pattern.to_owned(),
            anchored,
            negated,
            dir_only,
        };
        let rules = [
            glob("venv", false, false, false),
            glob("build", false, false, true),
            glob("keep", false, true, false),
            IgnoreRule::Everything {
                prefix: "sub/".to_owned(),
            },
        ];
        let entry = |path, is_dir| IgnoreEntry { path, is_dir };
        let entries = [
            entry("a/venv", true),
            entry("build", false),
            entry("build", true),
            entry("keep", false),
            entry("sub/x", false),
        ];
        assert_eq!(
            ignored(&rules, &entries).expect("the core answers"),
            [true, false, true, false, true]
        );
    }
}
