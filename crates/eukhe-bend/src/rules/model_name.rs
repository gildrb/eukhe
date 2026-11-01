//! Rules over a model's name (`bend/model_name.bend`, entry
//! `bend/ffi_model_name.bend`; `laws/model_name.bend`): the explicit
//! name rules of the quirks rulebook (families, 1h cache-write prices)
//! and the separator rule of its match candidates.

use crate::wire::{Reader, Writer, STR_MAX};
use crate::{call, expect_core, Entry, Error};

/// One rule over a name. Each rule is stated in plain words; a rule set
/// holds for a name when one of its rules does.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NameRule {
    /// The name holds one of these as a part.
    Contains(Vec<String>),
    /// The name is one of these.
    Is(Vec<String>),
    /// The name begins with one of these.
    Starts(Vec<String>),
    /// The name holds the first, and after it, on the same line (no line
    /// feed between), the second.
    Then(String, String),
    /// The name begins with one of `after`, then a run of ASCII digits
    /// that, after its leading zeros, has two or more digits or one digit
    /// not below `at_least` (for `at_least` 1-9: a number at least
    /// `at_least`); with `whole`, the run ends the name or a `-` follows it.
    Number {
        after: Vec<String>,
        at_least: u8,
        whole: bool,
    },
    /// The part of the name after its last `/` (the whole name when it has
    /// none) begins with one of these.
    SegmentStarts(Vec<String>),
}

/// Per group of names (in order), per rule set (in order): whether one
/// rule of the set holds for one name of the group.
#[must_use]
pub fn holds(sets: &[&[NameRule]], groups: &[&[String]]) -> Vec<bool> {
    expect_core(Entry::ModelName, holds_call(sets, groups))
}

fn holds_call(sets: &[&[NameRule]], groups: &[&[String]]) -> Result<Vec<bool>, Error> {
    let mut request = Writer::new();
    request.tag(0).count(sets.len());
    for set in sets {
        request.count(set.len());
        for rule in *set {
            put_rule(&mut request, rule);
        }
    }
    request.count(groups.len());
    for group in groups {
        put_strs(&mut request, group);
    }
    let reply = call(Entry::ModelName, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let n = reader.count()?;
    let verdicts = (0..n)
        .map(|_| reader.bool())
        .collect::<Result<Vec<_>, _>>()?;
    reader.end()?;
    Ok(verdicts)
}

fn put_rule(request: &mut Writer, rule: &NameRule) {
    match rule {
        NameRule::Contains(parts) => {
            request.tag(0);
            put_strs(request, parts);
        }
        NameRule::Is(names) => {
            request.tag(1);
            put_strs(request, names);
        }
        NameRule::Starts(heads) => {
            request.tag(2);
            put_strs(request, heads);
        }
        NameRule::Then(first, second) => {
            request.tag(3).str(wire_text(first)).str(wire_text(second));
        }
        NameRule::Number {
            after,
            at_least,
            whole,
        } => {
            request.tag(4);
            put_strs(request, after);
            request.nat(u64::from(*at_least)).bool(*whole);
        }
        NameRule::SegmentStarts(heads) => {
            request.tag(5);
            put_strs(request, heads);
        }
    }
}

fn put_strs(request: &mut Writer, texts: &[String]) {
    request.count(texts.len());
    for text in texts {
        request.str(wire_text(text));
    }
}

/// Each text with every maximal run of separators (a Unicode `White_Space`
/// char, `_`, `.` or `:`) replaced by one `-`.
#[must_use]
pub fn dash(texts: &[&str]) -> Vec<String> {
    expect_core(Entry::ModelName, dash_call(texts))
}

fn dash_call(texts: &[&str]) -> Result<Vec<String>, Error> {
    let mut request = Writer::new();
    request.tag(1).count(texts.len());
    for text in texts {
        request.str(wire_text(text));
    }
    let reply = call(Entry::ModelName, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let n = reader.count()?;
    let dashed = (0..n)
        .map(|_| reader.str().map(str::to_owned))
        .collect::<Result<Vec<_>, _>>()?;
    reader.end()?;
    Ok(dashed)
}

/// A text as the wire carries it: its first [`STR_MAX`] chars.
fn wire_text(text: &str) -> &str {
    text.char_indices()
        .nth(STR_MAX)
        .map_or(text, |(end, _)| &text[..end])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strs(xs: &[&str]) -> Vec<String> {
        xs.iter().map(|x| (*x).to_owned()).collect()
    }

    /// The verdicts come from the compiled core, group-major: every rule
    /// kind on a hit and a miss.
    #[test]
    fn the_core_reads_the_name_rules() {
        let sets: [&[NameRule]; 6] = [
            &[NameRule::Contains(strs(&["opus-4-6"]))],
            &[NameRule::Is(strs(&["gpt-5.4", "gpt-5.5"]))],
            &[NameRule::Then("claude".into(), "-4-".into())],
            &[NameRule::Number {
                after: strs(&["gpt-5."]),
                at_least: 6,
                whole: true,
            }],
            &[NameRule::SegmentStarts(strs(&["qwen", "qwq"]))],
            &[NameRule::Starts(strs(&["gemini-2"]))],
        ];
        let hit = strs(&["x/claude-opus-4-6", "gpt-5.5"]);
        let miss = strs(&["gpt-5.10.1", "qwen/llama-4-claude"]);
        assert_eq!(
            holds(&sets, &[&hit, &miss]),
            [
                true, true, true, false, false, false, //
                false, false, false, false, false, false,
            ]
        );
        let more = strs(&["vendor/qwq-32b", "gpt-5.010-mini", "gemini-2.5"]);
        assert_eq!(
            holds(&sets, &[&more]),
            [false, false, false, true, true, true]
        );
    }

    #[test]
    fn the_core_dashes_separator_runs() {
        assert_eq!(
            dash(&["claude 3.5:_sonnet", "a\u{3000}b", "plain"]),
            ["claude-3-5-sonnet", "a-b", "plain"]
        );
    }
}
