//! The doc guard of a Rust file: an edit keeps each outer doc comment
//! (`///`, `/** */`) and outer attribute (`#[...]`) above the item it
//! belonged to. Rust only: there an outer doc and the attributes attach to
//! the next item by the language's grammar, so a line put between them, or
//! an item written again without its doc, changes what the doc describes.
//! Other languages keep docs inside the item (Python) or by convention
//! only (`JSDoc`); their own scanners would be needed.
//!
//! The guard compares the text before and after a staged section through
//! the origin of each new line ([`super::types::ApplyResult::origins`]):
//! - a kept doc or attribute line must still sit above its own item (the
//!   same line, or a rewritten line of the same item), unless that item is
//!   gone (renamed or removed with its doc);
//! - an item (`fn`, `struct`, `enum`, …; fields excluded) whose doc lines
//!   and header the edit removed, and which the new lines define again,
//!   keeps a doc.

use std::collections::BTreeMap;

use crate::error::EditError;

/// What a line of Rust source is, for the guard.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Class {
    /// A line of an outer doc comment (`///`, `/** */`).
    Doc,
    /// A line of an outer attribute (`#[...]`, continuation lines included).
    Attr,
    /// A blank line, a line comment or a plain block comment line: part of
    /// no item.
    Gap,
    /// Anything else: an item, a field, a statement, a line in a string.
    Code,
}

/// What the scanner is inside at a point of a line.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mode {
    Code,
    /// A string literal (`"…"`, `b"…"`).
    Str,
    /// A raw string closed by `"` and this many `#`.
    Raw(usize),
    /// Block comments nested `depth` deep; `doc` when the outer one is `/**`.
    Block {
        depth: u32,
        doc: bool,
    },
}

/// The scanner's state at the start of a line: its mode, and the bracket
/// depth of the attribute it is in, if any.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Lex {
    mode: Mode,
    attr: Option<u32>,
}

const START: Lex = Lex {
    mode: Mode::Code,
    attr: None,
};

fn is_ident(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

/// Whether `rest` opens a doc block comment (`/**`, not `/***` or `/**/`).
fn opens_doc_block(rest: &[u8]) -> bool {
    rest.starts_with(b"/**") && !rest.starts_with(b"/***") && !rest.starts_with(b"/**/")
}

/// The UTF-8 width of the char whose first byte is `lead`.
const fn utf8_width(lead: u8) -> usize {
    match lead {
        0xF0..=0xFF => 4,
        0xE0..=0xEF => 3,
        0xC0..=0xDF => 2,
        0x00..=0xBF => 1,
    }
}

/// The bytes a char literal at the start of `rest` (its opening `'`)
/// spans, or `None` for a lifetime.
fn char_literal(rest: &[u8]) -> Option<usize> {
    let lead = *rest.get(1)?;
    if lead == b'\\' {
        let close = rest.get(3..)?.iter().position(|byte| *byte == b'\'')?;
        return Some(close + 4);
    }
    let width = utf8_width(lead);
    (rest.get(1 + width) == Some(&b'\'')).then_some(width + 2)
}

/// The prefix length of a raw string opener at the start of `rest`
/// (`r"`, `r#"`, `br##"`, …) and its `#` count.
fn raw_opener(rest: &[u8]) -> Option<(usize, usize)> {
    let after = rest
        .strip_prefix(b"br")
        .or_else(|| rest.strip_prefix(b"r"))?;
    let hashes = after.iter().take_while(|byte| **byte == b'#').count();
    (after.get(hashes) == Some(&b'"')).then_some((rest.len() - after.len() + hashes + 1, hashes))
}

/// The state after `line`, from `lex` at its start, and the byte offset
/// where an attribute open on the line closes (none: it stays open or
/// there is none).
fn scan(line: &str, lex: Lex) -> (Lex, Option<usize>) {
    let bytes = line.as_bytes();
    let (mut mode, mut attr) = (lex.mode, lex.attr);
    let mut closed = None;
    let mut at = 0;
    while at < bytes.len() {
        let rest = &bytes[at..];
        match mode {
            Mode::Code => {
                if rest.starts_with(b"//") {
                    break;
                }
                if rest.starts_with(b"/*") {
                    mode = Mode::Block {
                        depth: 1,
                        doc: opens_doc_block(rest),
                    };
                    at += 2;
                    continue;
                }
                let after_ident = at > 0 && is_ident(bytes[at - 1]);
                if let Some((width, hashes)) = raw_opener(rest).filter(|_| !after_ident) {
                    mode = Mode::Raw(hashes);
                    at += width;
                    continue;
                }
                match rest[0] {
                    b'"' => mode = Mode::Str,
                    b'\'' => {
                        if let Some(width) = char_literal(rest) {
                            at += width;
                            continue;
                        }
                    }
                    b'[' => attr = attr.map(|depth| depth + 1),
                    b']' => {
                        attr = attr.map(|depth| depth.saturating_sub(1));
                        if attr == Some(0) {
                            attr = None;
                            closed = Some(at + 1);
                        }
                    }
                    _ => {}
                }
                at += 1;
            }
            Mode::Str => {
                match rest[0] {
                    b'\\' => at += 1,
                    b'"' => mode = Mode::Code,
                    _ => {}
                }
                at += 1;
            }
            Mode::Raw(hashes) => {
                let ends = rest[0] == b'"'
                    && rest[1..].iter().take_while(|byte| **byte == b'#').count() >= hashes;
                if ends {
                    mode = Mode::Code;
                    at += 1 + hashes;
                } else {
                    at += 1;
                }
            }
            Mode::Block { depth, doc } => {
                if rest.starts_with(b"/*") {
                    mode = Mode::Block {
                        depth: depth + 1,
                        doc,
                    };
                    at += 2;
                } else if rest.starts_with(b"*/") {
                    mode = match depth {
                        1 => Mode::Code,
                        _ => Mode::Block {
                            depth: depth - 1,
                            doc,
                        },
                    };
                    at += 2;
                } else {
                    at += 1;
                }
            }
        }
    }
    (Lex { mode, attr }, closed)
}

/// Whether the text after an attribute's closing bracket holds code.
fn code_after(line: &str, closed: Option<usize>) -> bool {
    closed.is_some_and(|at| {
        let rest = line[at..].trim_start();
        !rest.is_empty() && !rest.starts_with("//")
    })
}

/// The class of `line` given the state at its start, and the state after it.
fn classify_line(line: &str, lex: Lex) -> (Class, Lex) {
    match lex.mode {
        Mode::Str | Mode::Raw(_) => (Class::Code, scan(line, lex).0),
        Mode::Block { doc, .. } => {
            let class = if doc { Class::Doc } else { Class::Gap };
            (class, scan(line, lex).0)
        }
        Mode::Code if lex.attr.is_some() => {
            let (after, closed) = scan(line, lex);
            let class = if code_after(line, closed) {
                Class::Code
            } else {
                Class::Attr
            };
            (class, after)
        }
        Mode::Code => {
            let text = line.trim_start();
            if text.starts_with("#[") {
                let (after, closed) = scan(
                    line,
                    Lex {
                        mode: Mode::Code,
                        attr: Some(0),
                    },
                );
                let class = if code_after(line, closed) {
                    Class::Code
                } else {
                    Class::Attr
                };
                return (class, after);
            }
            let class = if text.is_empty() || text.starts_with("//") && !is_outer_doc(text) {
                Class::Gap
            } else if is_outer_doc(text) || opens_doc_block(text.as_bytes()) {
                Class::Doc
            } else if text.starts_with("/*") {
                Class::Gap
            } else {
                Class::Code
            };
            (class, scan(line, lex).0)
        }
    }
}

fn is_outer_doc(text: &str) -> bool {
    text.starts_with("///") && !text.starts_with("////")
}

fn classify(lines: &[&str]) -> Vec<Class> {
    let mut lex = START;
    lines
        .iter()
        .map(|line| {
            let (class, after) = classify_line(line, lex);
            lex = after;
            class
        })
        .collect()
}

/// For each line, the first code line at or below it.
fn code_from(classes: &[Class]) -> Vec<Option<usize>> {
    let mut below = None;
    let mut out = vec![None; classes.len()];
    for (index, class) in classes.iter().enumerate().rev() {
        if *class == Class::Code {
            below = Some(index);
        }
        out[index] = below;
    }
    out
}

/// The line a head line (doc or attribute) at `index` belongs to: the
/// first code line below it.
fn target(code_from: &[Option<usize>], index: usize) -> Option<usize> {
    code_from.get(index + 1).copied().flatten()
}

/// The doc and attribute lines above the code line `item` (first and last,
/// 0-based) and whether any is a doc line.
fn head(classes: &[Class], item: usize) -> Option<(usize, usize, bool)> {
    let mut span: Option<(usize, usize, bool)> = None;
    for index in (0..item).rev() {
        match classes[index] {
            Class::Code => break,
            Class::Gap => {}
            class @ (Class::Doc | Class::Attr) => {
                let doc = class == Class::Doc;
                span = Some(span.map_or((index, index, doc), |(_, last, any)| {
                    (index, last, any || doc)
                }));
            }
        }
    }
    span
}

/// The doc and attribute lines above the code line `item`, top first.
fn head_text<'a>(classes: &[Class], lines: &[&'a str], item: usize) -> Vec<&'a str> {
    head(classes, item).map_or_else(Vec::new, |(first, last, _)| {
        (first..=last)
            .filter(|line| matches!(classes[*line], Class::Doc | Class::Attr))
            .map(|line| lines[line])
            .collect()
    })
}

/// What a code line defines: an item's kind and name, or a field's or
/// variant's name (empty kind).
#[derive(Debug, Clone, PartialEq, Eq)]
struct Key {
    kind: &'static str,
    name: String,
}

const KINDS: [&str; 12] = [
    "fn",
    "struct",
    "enum",
    "union",
    "type",
    "trait",
    "mod",
    "const",
    "static",
    "macro_rules",
    "impl",
    "use",
];

const QUALIFIERS: [&str; 9] = [
    "pub", "crate", "super", "self", "in", "async", "unsafe", "extern", "default",
];

fn key(line: &str) -> Option<Key> {
    let words: Vec<&str> = line
        .split(|ch: char| !(ch.is_alphanumeric() || ch == '_'))
        .filter(|word| !word.is_empty())
        .collect();
    let mut at = 0;
    while let Some(word) = words.get(at) {
        let next = words.get(at + 1).copied();
        let skip = QUALIFIERS.contains(word)
            || *word == "C" && at > 0 && words[at - 1] == "extern"
            || *word == "const" && matches!(next, Some("fn" | "unsafe" | "async" | "extern"));
        if !skip {
            break;
        }
        at += 1;
    }
    let word = *words.get(at)?;
    let Some(kind) = KINDS.iter().find(|kind| **kind == word) else {
        return Some(Key {
            kind: "",
            name: word.to_owned(),
        });
    };
    if *kind == "impl" {
        let text = line.split_once("impl")?.1;
        let text = text.split('{').next().unwrap_or(text);
        return Some(Key {
            kind,
            name: text.split_whitespace().collect::<Vec<_>>().join(" "),
        });
    }
    let name = words[at + 1..]
        .iter()
        .find(|word| **word != "mut")
        .copied()
        .unwrap_or_default();
    Some(Key {
        kind,
        name: name.to_owned(),
    })
}

/// Kinds one item may change between and stay the same item.
fn family(kind: &str) -> &str {
    match kind {
        "struct" | "enum" | "union" | "type" | "trait" => "type",
        "const" | "static" => "value",
        other => other,
    }
}

fn same(left: Option<&Key>, right: Option<&Key>) -> bool {
    match (left, right) {
        (Some(left), Some(right)) => {
            left.name == right.name && family(left.kind) == family(right.kind)
        }
        (None, _) | (_, None) => false,
    }
}

fn label(line: &str) -> String {
    match key(line) {
        Some(Key { kind: "", name }) => format!("`{name}`"),
        Some(Key { kind, name }) => format!("`{kind} {name}`"),
        None => format!("`{}`", line.trim()),
    }
}

/// How an edit breaks the doc of one item; lines are 1-based in the text
/// before the edit.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Breach {
    /// The item's label (`fn ensure`).
    item: String,
    /// The item's doc and attribute lines.
    first: usize,
    last: usize,
    /// "doc" or "attributes": what those lines are.
    head: &'static str,
    fault: Fault,
}

/// How an edit breaks an item's head; `at` is the first of its lines
/// that the edit keeps but moves off the item.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Fault {
    /// The item stays, but line `at` of its head now sits above `now`
    /// (none: above nothing).
    Split { at: usize, now: Option<String> },
    /// The edit removes the item; line `at` of its head stays above `now`.
    Orphaned { at: usize, now: Option<String> },
    /// The edit removes the item with its doc and writes it again without
    /// a doc.
    Dropped,
}

/// `line N` or `lines N-M`.
fn span(first: usize, last: usize) -> String {
    if first == last {
        format!("line {first}")
    } else {
        format!("lines {first}-{last}")
    }
}

impl Breach {
    fn line(&self) -> String {
        let Self {
            item,
            first,
            last,
            head,
            fault,
        } = self;
        let lines = span(*first, *last);
        match fault {
            Fault::Split { at, now } => format!(
                "- the {head} of {item} ({lines}): after this edit line {at} sits above {} \
                 instead. Insert before line {first}, above the {head} of {item}, or below the \
                 end of {item}.",
                now.as_deref().unwrap_or("nothing")
            ),
            Fault::Orphaned { at, now } => format!(
                "- the {head} of {item} ({lines}): this edit removes {item} but keeps line {at}, \
                 which now sits above {}. Remove {lines} with {item}, or write its replacement \
                 right below the {head}.",
                now.as_deref().unwrap_or("nothing")
            ),
            Fault::Dropped => format!(
                "- the doc of {item} ({lines}): this edit removes it and writes {item} again \
                 without a doc. Keep the doc above {item} in the body, or start the range below \
                 line {last}."
            ),
        }
    }
}

/// The breaches of an edit from `old` to `new`, one per item, by line.
fn breaches(old: &str, new: &str, origins: &[Option<usize>]) -> Vec<Breach> {
    let old_lines: Vec<&str> = old.split('\n').collect();
    let new_lines: Vec<&str> = new.split('\n').collect();
    let (old_classes, new_classes) = (classify(&old_lines), classify(&new_lines));
    let (old_code, new_code) = (code_from(&old_classes), code_from(&new_classes));
    let mut place = vec![None; old_lines.len()];
    for (index, origin) in origins.iter().enumerate() {
        if let Some(slot) = origin.and_then(|origin| place.get_mut(origin)) {
            *slot = Some(index);
        }
    }
    let kept: Vec<bool> = place.iter().map(Option::is_some).collect();
    // The new code lines that define the item at old line `line` again.
    let written = |line: usize| {
        let wanted = key(old_lines[line]);
        (0..new_lines.len())
            .filter(|index| origins.get(*index).copied().flatten().is_none())
            .filter(|index| new_classes[*index] == Class::Code)
            .filter(|index| same(key(new_lines[*index]).as_ref(), wanted.as_ref()))
            .collect::<Vec<_>>()
    };
    let mut found = BTreeMap::new();
    for (index, origin) in origins.iter().enumerate() {
        let Some(origin) = *origin else { continue };
        if !matches!(old_classes.get(origin), Some(Class::Doc | Class::Attr)) {
            continue;
        }
        let Some(item) = target(&old_code, origin) else {
            continue;
        };
        let Some((first, last, doc)) = head(&old_classes, item) else {
            continue;
        };
        let now = target(&new_code, index);
        let new_line = |line: usize| origins.get(line).copied().flatten();
        let holds = now.is_some_and(|line| match new_line(line) {
            Some(from) => from == item,
            None => same(key(new_lines[line]).as_ref(), key(old_lines[item]).as_ref()),
        });
        let survives = kept[item] || !written(item).is_empty();
        let renamed = !survives && now.is_some_and(|line| new_line(line).is_none());
        // The origins of a line diff (a rebased section) may pair a head
        // line with an equal line of another head: a line whose text the
        // item's new head holds, or (the item gone) the old head of the
        // line now below it held, stayed where it was.
        let text = old_lines[origin];
        let echoed = place[item]
            .into_iter()
            .chain(written(item))
            .any(|line| head_text(&new_classes, &new_lines, line).contains(&text));
        let paired = now.and_then(new_line).is_some_and(|from| {
            from != item && head_text(&old_classes, &old_lines, from).contains(&text)
        });
        if holds || renamed || (survives && echoed) || (!survives && paired) {
            continue;
        }
        let now = now.map(|line| label(new_lines[line]));
        let at = origin + 1;
        found.entry(item).or_insert(Breach {
            item: label(old_lines[item]),
            first: first + 1,
            last: last + 1,
            head: if doc { "doc" } else { "attributes" },
            fault: if survives {
                Fault::Split { at, now }
            } else {
                Fault::Orphaned { at, now }
            },
        });
    }
    // Items only: a field shares its key with each `name: value` of a
    // struct literal.
    for (item, class) in old_classes.iter().enumerate() {
        if *class != Class::Code || kept[item] || found.contains_key(&item) {
            continue;
        }
        if key(old_lines[item]).is_none_or(|key| key.kind.is_empty()) {
            continue;
        }
        let Some((first, last, true)) = head(&old_classes, item) else {
            continue;
        };
        let doc_gone = (first..=last).all(|line| old_classes[line] != Class::Doc || !kept[line]);
        let again = written(item);
        let undocumented = again
            .iter()
            .all(|line| head(&new_classes, *line).is_none_or(|(_, _, doc)| !doc));
        if doc_gone && !again.is_empty() && undocumented {
            found.insert(
                item,
                Breach {
                    item: label(old_lines[item]),
                    first: first + 1,
                    last: last + 1,
                    head: "doc",
                    fault: Fault::Dropped,
                },
            );
        }
    }
    found.into_values().collect()
}

/// Refuse an edit of the Rust file `display` that moves a doc comment or
/// attribute off its item or drops the doc of an item it writes again.
pub(super) fn check(
    display: &str,
    old: &str,
    new: &str,
    origins: &[Option<usize>],
) -> Result<(), EditError> {
    let found = breaches(old, new, origins);
    if found.is_empty() {
        return Ok(());
    }
    let lines = found
        .iter()
        .map(Breach::line)
        .collect::<Vec<_>>()
        .join("\n");
    Err(EditError::apply(format!(
        "Edit to {display} not applied: a doc comment or attribute belongs to the item right \
         below it.\n{lines}\nNothing was written."
    )))
}

#[cfg(test)]
mod tests {
    use super::{classify, key, Class, Key};

    #[test]
    fn classifies_docs_attributes_comments_and_strings() {
        let lines = [
            "/// a doc",
            "#[derive(",
            "    Debug,",
            ")]",
            "// a comment",
            "",
            "fn a() {",
            "    let s = \"",
            "/// in a string",
            "\";",
            "    let r = r#\"",
            "#[not an attribute]",
            "\"#;",
            "}",
            "/**",
            " * a block doc",
            " */",
            "/* plain",
            "   still plain */",
            "#[test] fn b() {}",
            "    let c = '\"';",
        ];
        assert_eq!(
            classify(&lines),
            vec![
                Class::Doc,
                Class::Attr,
                Class::Attr,
                Class::Attr,
                Class::Gap,
                Class::Gap,
                Class::Code,
                Class::Code,
                Class::Code,
                Class::Code,
                Class::Code,
                Class::Code,
                Class::Code,
                Class::Code,
                Class::Doc,
                Class::Doc,
                Class::Doc,
                Class::Gap,
                Class::Gap,
                Class::Code,
                Class::Code,
            ]
        );
    }

    #[test]
    fn keys_name_items_fields_and_impls() {
        let keys = [
            "pub(crate) async fn ensure(",
            "pub const fn new() -> Self {",
            "const MAX: u32 = 1;",
            "static mut COUNT: u32 = 0;",
            "    pub tag: String,",
            "    Busy { requests: u32 },",
            "impl<T> Shared for Arc<T> {",
            "extern \"C\" fn hook() {}",
        ]
        .map(key);
        let expected = [
            ("fn", "ensure"),
            ("fn", "new"),
            ("const", "MAX"),
            ("static", "COUNT"),
            ("", "tag"),
            ("", "Busy"),
            ("impl", "<T> Shared for Arc<T>"),
            ("fn", "hook"),
        ]
        .map(|(kind, name)| {
            Some(Key {
                kind,
                name: name.to_owned(),
            })
        });
        assert_eq!(keys, expected);
    }
}
