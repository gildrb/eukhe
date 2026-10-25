//! The texts of a thread goal (`bend/goal_text.bend`, entry
//! `bend/ffi_goal_text.bend`; `laws/goal_text.bend`): the continuation,
//! budget-limit and objective-updated prompts, the usage line of a status
//! display, and what a goal tool call answers (the tokens left and the
//! completion budget report). Rust sends the goal with its numbers as
//! decimal digits and reads the texts; the tokens left come back as digits
//! no larger than the budget.

use eukhe_types::goal::{GoalContextKind, GoalState, GoalStatus};

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Error};

/// What a goal tool call answers about a goal that is set.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HostAnswer {
    /// The budget less the tokens used, never below 0 (with a budget).
    pub remaining_tokens: Option<u64>,
    /// The completion budget report, when asked for and the goal is
    /// complete.
    pub completion_budget_report: Option<String>,
}

/// Whether a goal tool call asks for the completion budget report.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Report {
    Asked,
    NotAsked,
}

/// The question tags of the entry.
const PROMPT: u32 = 0;
const USAGE: u32 = 1;
const HOST: u32 = 2;

/// The prompt of `kind` for the goal (its objective escaped as XML text).
#[must_use]
pub fn prompt(goal: &GoalState, kind: GoalContextKind) -> String {
    expect_core(Entry::GoalText, prompt_call(goal, kind))
}

/// The usage line of a status display: `<used> / <budget> tokens` with a
/// budget, else `<seconds>s`, none for 0 seconds.
#[must_use]
pub fn usage(goal: &GoalState) -> Option<String> {
    expect_core(Entry::GoalText, usage_call(goal))
}

/// What a goal tool call answers: none for an idle goal or one without an
/// objective.
#[must_use]
pub fn host(goal: &GoalState, report: Report) -> Option<HostAnswer> {
    expect_core(Entry::GoalText, host_call(goal, report))
}

fn prompt_call(goal: &GoalState, kind: GoalContextKind) -> Result<String, Error> {
    let kind = match kind {
        GoalContextKind::Continuation => 0,
        GoalContextKind::BudgetLimit => 1,
        GoalContextKind::ObjectiveUpdated => 2,
    };
    let mut writer = Writer::new();
    writer.tag(PROMPT).tag(kind);
    put_goal(&mut writer, goal);
    let reply = call(Entry::GoalText, &writer.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let text = reader.str()?.to_string();
    reader.end()?;
    Ok(text)
}

fn usage_call(goal: &GoalState) -> Result<Option<String>, Error> {
    let mut writer = Writer::new();
    writer.tag(USAGE);
    put_goal(&mut writer, goal);
    let reply = call(Entry::GoalText, &writer.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let line = maybe_str(&mut reader)?;
    reader.end()?;
    Ok(line)
}

fn host_call(goal: &GoalState, report: Report) -> Result<Option<HostAnswer>, Error> {
    let mut writer = Writer::new();
    writer.tag(HOST);
    put_goal(&mut writer, goal);
    writer.bool(match report {
        Report::Asked => true,
        Report::NotAsked => false,
    });
    let reply = call(Entry::GoalText, &writer.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let answer = if reader.maybe()? {
        let remaining_tokens = match maybe_str(&mut reader)? {
            Some(digits) => Some(digits.parse().map_err(|_| WireError::Malformed {
                at: 0,
                expected: "the digits of a u64",
            })?),
            None => None,
        };
        Some(HostAnswer {
            remaining_tokens,
            completion_budget_report: maybe_str(&mut reader)?,
        })
    } else {
        None
    };
    reader.end()?;
    Ok(answer)
}

/// The goal as the entry reads it: status tag, objective, budget digits,
/// tokens used and seconds used.
fn put_goal(writer: &mut Writer, goal: &GoalState) {
    writer.tag(match goal.status {
        GoalStatus::Idle => 0,
        GoalStatus::Active => 1,
        GoalStatus::Paused => 2,
        GoalStatus::BudgetLimited => 3,
        GoalStatus::Complete => 4,
        GoalStatus::Error => 5,
    });
    match &goal.objective {
        Some(objective) => writer.some().str(objective),
        None => writer.none(),
    };
    match goal.token_budget {
        Some(budget) => writer.some().str(&budget.to_string()),
        None => writer.none(),
    };
    writer
        .str(&goal.tokens_used.to_string())
        .str(&goal.time_used_seconds.to_string());
}

fn maybe_str(reader: &mut Reader<'_>) -> Result<Option<String>, WireError> {
    Ok(if reader.maybe()? {
        Some(reader.str()?.to_string())
    } else {
        None
    })
}

#[cfg(test)]
mod tests {
    use eukhe_types::goal::{empty_goal_state, GoalStatus};

    use super::*;

    /// The answers come from the compiled core: the tokens left saturate at
    /// 0, the report joins both parts, the usage line shows the budget.
    #[test]
    fn the_core_writes_goal_texts() {
        let goal = GoalState {
            status: GoalStatus::Complete,
            objective: Some("ship <it>".to_string()),
            token_budget: Some(100),
            tokens_used: 250,
            time_used_seconds: 7,
            ..empty_goal_state()
        };
        assert_eq!(
            host(&goal, Report::Asked),
            Some(HostAnswer {
                remaining_tokens: Some(0),
                completion_budget_report: Some(
                    "Goal achieved. Report final budget usage to the user: tokens used: 250 of 100; time used: 7 seconds."
                        .to_string()
                ),
            })
        );
        assert_eq!(usage(&goal).as_deref(), Some("250 / 100 tokens"));
        assert!(prompt(&goal, GoalContextKind::Continuation).contains("ship &lt;it&gt;"));
    }
}
