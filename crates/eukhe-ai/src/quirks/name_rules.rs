//! The explicit name rules of the rulebook (`families[].match` and
//! `except`, `cache_write_1h_prices[].match`): each a JSON object with one
//! key, run by the compiled core ([`eukhe_bend::rules::model_name`], whose
//! laws state each rule in plain words). A list of rules holds for a name
//! when one of them does.
//!
//! - `{"contains": [..]}`: the name holds one of these as a part;
//! - `{"is": [..]}`: the name is one of these;
//! - `{"starts": [..]}`: the name begins with one of these;
//! - `{"then": [a, b]}`: the name holds `a`, and after it, on the same line,
//!   `b`;
//! - `{"number": {"after": [..], "at_least": n, "whole": w}}`: the name
//!   begins with one of `after`, then a number of ASCII digits at least `n`
//!   (a digit 1-9; leading zeros do not count); with `whole` (default
//!   false), the number ends the name or a `-` follows it;
//! - `{"segment_starts": [..]}`: the part after the name's last `/` (the
//!   whole name without one) begins with one of these.

use eukhe_bend::rules::model_name::NameRule;
use serde::Deserialize;

/// One rule as the rulebook writes it.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum NameRuleEntry {
    Contains(Vec<String>),
    Is(Vec<String>),
    Starts(Vec<String>),
    Then(String, String),
    Number(NumberEntry),
    SegmentStarts(Vec<String>),
}

/// The `number` rule as the rulebook writes it.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct NumberEntry {
    after: Vec<String>,
    at_least: u8,
    #[serde(default)]
    whole: bool,
}

/// The rules of `entries`; `Err` says why one is not a rule (a `number`
/// whose `at_least` is not a digit from 1 to 9).
pub(super) fn rules(entries: Vec<NameRuleEntry>) -> Result<Vec<NameRule>, String> {
    entries
        .into_iter()
        .map(|entry| match entry {
            NameRuleEntry::Contains(parts) => Ok(NameRule::Contains(parts)),
            NameRuleEntry::Is(names) => Ok(NameRule::Is(names)),
            NameRuleEntry::Starts(heads) => Ok(NameRule::Starts(heads)),
            NameRuleEntry::Then(first, second) => Ok(NameRule::Then(first, second)),
            NameRuleEntry::Number(NumberEntry {
                after,
                at_least,
                whole,
            }) => {
                if (1..=9).contains(&at_least) {
                    Ok(NameRule::Number {
                        after,
                        at_least,
                        whole,
                    })
                } else {
                    Err(format!(
                        "a `number` rule needs `at_least` from 1 to 9, not {at_least}"
                    ))
                }
            }
            NameRuleEntry::SegmentStarts(heads) => Ok(NameRule::SegmentStarts(heads)),
        })
        .collect()
}
