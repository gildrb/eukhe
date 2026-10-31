//! The model facts a wire API decides from the quirks rulebook's answers
//! (`bend/facts.bend` sections 1, 3 and 4, entry
//! `bend/ffi_model_facts.bend`; `laws/model_facts.bend`): a flag
//! directive's decision, adaptive thinking, the Bedrock
//! effort of a level, the Bedrock reasoning fields and the service tier
//! row that prices a request. The caller gathers the facts (the
//! rulebook's answers, the model's compat flag and thinking-level map, the
//! price rows); the compiled core decides.

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Error};

/// The decision of a flag directive: the rulebook's `answer` (`Some(true)`
/// only for a rule that says yes), else `default` where no rule applies.
#[must_use]
pub fn flag(answer: Option<bool>, default: bool) -> bool {
    expect_core(Entry::ModelFacts, flag_call(answer, default))
}

fn put_answer(request: &mut Writer, answer: Option<bool>) {
    match answer {
        Some(value) => request.tag(0).nat(u64::from(value)),
        None => request.tag(1),
    };
}

fn flag_call(answer: Option<bool>, default: bool) -> Result<bool, Error> {
    let mut request = Writer::new();
    request.tag(0);
    put_answer(&mut request, answer);
    request.bool(default);
    bool_of(&call(Entry::ModelFacts, &request.finish()?)?)
}

/// Adaptive thinking: the model's explicit `compat` flag, else the
/// rulebook's `answer`, else off.
#[must_use]
pub fn adaptive(compat: Option<bool>, answer: Option<bool>) -> bool {
    expect_core(Entry::ModelFacts, adaptive_call(compat, answer))
}

fn adaptive_call(compat: Option<bool>, answer: Option<bool>) -> Result<bool, Error> {
    let mut request = Writer::new();
    request.tag(1);
    match compat {
        None => request.tag(0),
        Some(flag) => request.tag(1).bool(flag),
    };
    put_answer(&mut request, answer);
    bool_of(&call(Entry::ModelFacts, &request.finish()?)?)
}

fn bool_of(reply: &str) -> Result<bool, Error> {
    let mut reader = Reader::reply(reply)?;
    let value = reader.bool()?;
    reader.end()?;
    Ok(value)
}

/// One entry of a model's thinking-level map.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MapEntry {
    /// The map has no entry for the level.
    Missing,
    /// The entry is null.
    Null,
    /// The entry is a wire string (the caller keeps it).
    Wire,
}

/// A request's thinking level, minimal to max.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Level {
    Minimal,
    Low,
    Medium,
    High,
    Xhigh,
    Max,
}

/// The Bedrock effort a level sends.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Effort {
    /// The map's own wire string for the level.
    Mapped,
    Low,
    Medium,
    High,
}

/// The Bedrock effort of `level` for a model whose thinking-level map has
/// `map` (its entries for minimal, low, medium, high, xhigh and max).
#[must_use]
pub fn effort(map: [MapEntry; 6], level: Level) -> Effort {
    expect_core(Entry::ModelFacts, effort_call(map, level))
}

/// A map entry as the entry reads it: the map's string is the code 0 (the
/// defaults are 2 and up).
fn put_entry(request: &mut Writer, entry: MapEntry) {
    match entry {
        MapEntry::Missing => request.tag(0),
        MapEntry::Null => request.tag(1).tag(0),
        MapEntry::Wire => request.tag(1).tag(1).nat(0),
    };
}

const fn level_tag(level: Level) -> u32 {
    match level {
        Level::Minimal => 0,
        Level::Low => 1,
        Level::Medium => 2,
        Level::High => 3,
        Level::Xhigh => 4,
        Level::Max => 5,
    }
}

fn effort_call(map: [MapEntry; 6], level: Level) -> Result<Effort, Error> {
    let mut request = Writer::new();
    request.tag(2);
    for entry in map {
        put_entry(&mut request, entry);
    }
    request.tag(level_tag(level));
    let reply = call(Entry::ModelFacts, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let effort = match reader.nat()? {
        0 => Effort::Mapped,
        2 => Effort::Low,
        3 => Effort::Medium,
        4 => Effort::High,
        _ => {
            return Err(WireError::Malformed {
                at: 0,
                expected: "a Bedrock effort",
            }
            .into())
        }
    };
    reader.end()?;
    Ok(effort)
}

/// The Bedrock request shape the rulebook's `bedrock_reasoning` names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Shape {
    /// Claude's thinking fields (adaptive or budget thinking).
    Claude,
    /// `OpenAI` GPT: a nested `reasoning.effort`.
    Gpt,
    /// gpt-oss: a flat `reasoning_effort` of low, medium or high.
    GptOss,
}

/// An effort the GPT reasoning fields send.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GptEffort {
    /// The map's own wire string for the level.
    Mapped,
    Low,
    Medium,
    High,
    Xhigh,
    Max,
}

/// The reasoning fields of a Bedrock request.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReasoningFields {
    /// No reasoning field.
    None,
    /// Claude's thinking fields (the caller builds them).
    Claude,
    /// `reasoning: { effort }`.
    Nested(GptEffort),
    /// `reasoning_effort`.
    Flat(GptEffort),
}

/// The reasoning fields of a Bedrock request at `level` for a model of
/// rulebook shape `shape` (`None`: no rule applies) whose thinking-level
/// map has `entry` at the level.
#[must_use]
pub fn reasoning(shape: Option<Shape>, entry: MapEntry, level: Level) -> ReasoningFields {
    expect_core(Entry::ModelFacts, reasoning_call(shape, entry, level))
}

fn reasoning_call(
    shape: Option<Shape>,
    entry: MapEntry,
    level: Level,
) -> Result<ReasoningFields, Error> {
    let mut request = Writer::new();
    request.tag(4).tag(match shape {
        None => 0,
        Some(Shape::Claude) => 1,
        Some(Shape::Gpt) => 2,
        Some(Shape::GptOss) => 3,
    });
    put_entry(&mut request, entry);
    request.tag(level_tag(level));
    let reply = call(Entry::ModelFacts, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let fields = match reader.nat()? {
        0 => ReasoningFields::None,
        1 => ReasoningFields::Claude,
        2 => ReasoningFields::Nested(gpt_effort(reader.nat()?)?),
        3 => ReasoningFields::Flat(gpt_effort(reader.nat()?)?),
        _ => {
            return Err(WireError::Malformed {
                at: 0,
                expected: "Bedrock reasoning fields",
            }
            .into())
        }
    };
    reader.end()?;
    Ok(fields)
}

fn gpt_effort(code: u64) -> Result<GptEffort, Error> {
    Ok(match code {
        0 => GptEffort::Mapped,
        2 => GptEffort::Low,
        3 => GptEffort::Medium,
        4 => GptEffort::High,
        5 => GptEffort::Xhigh,
        6 => GptEffort::Max,
        _ => {
            return Err(WireError::Malformed {
                at: 0,
                expected: "a GPT effort",
            }
            .into())
        }
    })
}

/// One service tier price row of the model's provider and wire API, as
/// the rule reads it (the caller keeps the multiplier).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TierRow {
    /// The row names a model: `Some(true)` this request's model,
    /// `Some(false)` another one; `None` every model of the provider.
    pub model: Option<bool>,
    /// The row prices this request's tier.
    pub tier: bool,
}

/// The index in `rows` of the row that prices the request: the first row
/// of its model that prices its tier, else the first row of every model
/// that does; `None` when no row does.
#[must_use]
pub fn tier_row(rows: &[TierRow]) -> Option<usize> {
    expect_core(Entry::ModelFacts, tier_row_call(rows))
}

fn tier_row_call(rows: &[TierRow]) -> Result<Option<usize>, Error> {
    let mut request = Writer::new();
    request.tag(3).count(rows.len());
    for (index, row) in rows.iter().enumerate() {
        match row.model {
            None => request.none(),
            Some(this) => request.some().nat(u64::from(!this)),
        };
        // Each row carries its index as its multiplier: the reply names it.
        request
            .nat(u64::from(!row.tier))
            .nat(u64::try_from(index).unwrap_or(u64::MAX));
    }
    // This model and this tier are 0.
    request.nat(0).nat(0);
    let reply = call(Entry::ModelFacts, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let row = if reader.maybe()? {
        let index = reader.nat()?;
        Some(usize::try_from(index).map_err(|_| WireError::Malformed {
            at: 0,
            expected: "a row index",
        })?)
    } else {
        None
    };
    reader.end()?;
    Ok(row)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The reasoning fields of each shape come from the compiled core:
    /// GPT's map string first, its own xhigh; gpt-oss capped at high.
    #[test]
    fn the_bedrock_reasoning_fields_come_from_the_compiled_core() {
        use MapEntry::{Missing, Null, Wire};
        assert_eq!(
            [
                reasoning(None, Wire, Level::High),
                reasoning(Some(Shape::Claude), Missing, Level::Max),
                reasoning(Some(Shape::Gpt), Wire, Level::Minimal),
                reasoning(Some(Shape::Gpt), Null, Level::Xhigh),
                reasoning(Some(Shape::GptOss), Wire, Level::Max),
                reasoning(Some(Shape::GptOss), Missing, Level::Minimal),
            ],
            [
                ReasoningFields::None,
                ReasoningFields::Claude,
                ReasoningFields::Nested(GptEffort::Mapped),
                ReasoningFields::Nested(GptEffort::Xhigh),
                ReasoningFields::Flat(GptEffort::High),
                ReasoningFields::Flat(GptEffort::Low),
            ]
        );
    }

    /// Each decision comes from the compiled core.
    #[test]
    fn the_model_fact_decisions_come_from_the_compiled_core() {
        use MapEntry::{Missing, Null, Wire};
        assert_eq!(
            (
                flag(None, true),
                flag(Some(false), true),
                adaptive(Some(false), Some(true)),
                adaptive(None, Some(true)),
                effort(
                    [Missing, Missing, Missing, Wire, Missing, Missing],
                    Level::High
                ),
                effort(
                    [Missing, Missing, Null, Missing, Missing, Missing],
                    Level::Medium
                ),
                effort([Missing; 6], Level::Max),
                tier_row(&[
                    TierRow {
                        model: None,
                        tier: true
                    },
                    TierRow {
                        model: Some(true),
                        tier: true
                    },
                ]),
                tier_row(&[TierRow {
                    model: Some(false),
                    tier: true
                }]),
            ),
            (
                true,
                false,
                false,
                true,
                Effort::Mapped,
                Effort::Medium,
                Effort::High,
                Some(1),
                None
            )
        );
    }
}
