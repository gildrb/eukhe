//! The bridge between the work ledger ([`WorkLedger`]) with the goal's
//! progress check ([`goal_check`]) and their Bend model (`work` and
//! `check` in `bend/progress.bend`, whose laws `PROOF.bend` proves): both
//! run the same scenarios and must print the same transcript, byte for
//! byte. `bend/bridge_progress.bend` documents the scenario format: a cap,
//! then goal continuations, each after the acts of the run since the last
//! one; after each, the work and the check's verdict.
//!
//! An act `f` is a tool call `t{f % 3}` with arguments `{"x": f}` and its
//! result `r{f}` (an error when `f % 5 == 0`). The transcript also holds
//! what is not work: a fresh call id and timestamp for every call, text
//! and thinking around the calls, answers, user inputs, and display rows.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;

use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use eukhe_durable::types::{ConversationId, EntryId, EntryRecord, SubmissionId};
use eukhe_types::pi_ai::Message;
use serde_json::json;

use super::{goal_check, GoalProgress, Stall, WorkLedger};
use crate::goals::GoalState;

/// The transcript a scenario builds, with fresh ids and timestamps.
struct Transcript {
    entries: Vec<EntryRecord>,
    calls: u64,
}

impl Transcript {
    fn push(&mut self, message: Option<serde_json::Value>) {
        let model = message
            .map(|message| vec![serde_json::from_value::<Message>(message).expect("a message")]);
        let id = EntryId::from_number(u64::try_from(self.entries.len()).expect("a count") + 1);
        self.entries.push(EntryRecord {
            model,
            data: None,
            edits: None,
            kind: "pi.entry".to_owned(),
            id,
            conversation_id: ConversationId::from_number(1),
            head: None,
            by_task_id: None,
        });
    }

    fn assistant(&mut self, content: &[serde_json::Value], stop: &str, rng: &mut Rng) {
        self.push(Some(json!({
            "role": "assistant",
            "content": content,
            "api": "faux",
            "provider": "faux",
            "model": "faux-1",
            "usage": {
                "input": rng.range(1, 900), "output": rng.range(1, 90), "cacheRead": 0,
                "cacheWrite": 0, "totalTokens": 0,
                "cost": {"input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0}
            },
            "stopReason": stop,
            "timestamp": rng.range(1, 1_000_000),
        })));
    }

    /// The acts `acts` in one or two rounds, with noise around them.
    fn acts(&mut self, acts: &[u64], rng: &mut Rng) {
        for chunk in acts.chunks(2) {
            let mut content = Vec::new();
            if rng.chance(50) {
                content.push(json!({"type": "thinking", "thinking": format!("hmm {}", rng.range(0, 1_000_000))}));
            }
            if rng.chance(50) {
                content.push(json!({"type": "text", "text": format!("let me look {}", rng.range(0, 1_000_000))}));
            }
            let mut results = Vec::new();
            for act in chunk {
                self.calls += 1;
                let id = format!("call-{}", self.calls);
                content.push(json!({
                    "type": "toolCall", "id": id, "name": format!("t{}", act % 3),
                    "arguments": {"x": act},
                }));
                results.push(json!({
                    "role": "toolResult", "toolCallId": id, "toolName": format!("t{}", act % 3),
                    "content": [{"type": "text", "text": format!("r{act}")}],
                    "isError": act % 5 == 0, "timestamp": rng.range(1, 1_000_000),
                }));
            }
            self.assistant(&content, "toolUse", rng);
            for result in results {
                self.push(Some(result));
            }
        }
    }

    /// What is not work: an answer, a user input, or a display row.
    fn noise(&mut self, rng: &mut Rng) {
        match rng.below(3) {
            0 => {
                let content = vec![
                    json!({"type": "text", "text": format!("waiting {}", rng.range(0, 1_000_000))}),
                ];
                self.assistant(&content, "stop", rng);
            }
            1 => self.push(Some(json!({
                "role": "user", "content": format!("go on {}", rng.range(0, 1_000_000)),
                "timestamp": rng.range(1, 1_000_000),
            }))),
            _ => self.push(None),
        }
    }
}

/// One scenario: its events, for the model, and what the Rust code
/// printed. `repeat` is the percentage of acts the session did before.
fn scenario(seed: u64, steps: usize, repeat: u64) -> (String, String) {
    let mut rng = Rng(seed);
    let cap = rng.range(1, 4);
    let mut events = format!("9 {cap}\n");
    let mut out = String::new();
    let mut transcript = Transcript {
        entries: Vec::new(),
        calls: 0,
    };
    let mut ledger = WorkLedger::default();
    let mut done: Vec<u64> = Vec::new();
    let goal = GoalState {
        goal_id: Some("goal".to_owned()),
        ..GoalState::default()
    };
    let mut run = 1;
    let mut prior = Some(GoalProgress {
        input: Some(SubmissionId::from_number(run)),
        goal_id: goal.goal_id.clone(),
        work: 0,
        stalls: 0,
    });
    let mut fresh_run = false;
    for _ in 0..steps {
        let count = rng.below(4);
        let acts: Vec<u64> = (0..count)
            .map(|_| match rng.pick(&done) {
                Some(old) if rng.chance(repeat) => old,
                _ => rng.range(1, 40),
            })
            .collect();
        if fresh_run {
            run += 1;
        }
        let kind = u8::from(fresh_run);
        fresh_run = false;
        let mut line = kind.to_string();
        for act in &acts {
            write!(line, " {act}").unwrap();
        }
        writeln!(events, "{line}").unwrap();
        if rng.chance(50) {
            transcript.noise(&mut rng);
        }
        transcript.acts(&acts, &mut rng);
        if rng.chance(50) {
            transcript.noise(&mut rng);
        }
        done.extend(&acts);
        ledger.read_entries(&transcript.entries);
        let work = ledger.count();
        let input = Some(SubmissionId::from_number(run));
        let check = goal_check(prior.as_ref(), input, &goal, work, cap);
        let stalls = match check.stall {
            Stall::Go { stalls } => {
                writeln!(out, "w={work} G{stalls}").unwrap();
                stalls
            }
            Stall::Stop { stalls } => {
                writeln!(out, "w={work} S{stalls}").unwrap();
                // The paused goal goes on only in a new run (a resume).
                fresh_run = true;
                stalls
            }
        };
        prior = Some(GoalProgress {
            input,
            goal_id: goal.goal_id.clone(),
            work,
            stalls,
        });
    }
    (events, out)
}

#[test]
fn the_rust_progress_check_equals_the_bend_model() {
    // Mostly new work, then mixed, then mostly loops.
    let scenarios = (1..=40).map(|seed| {
        let repeat = [10, 50, 90][usize::try_from(seed % 3).unwrap()];
        let (events, transcript) = scenario(seed, 60, repeat);
        Scenario {
            name: seed.to_string(),
            events,
            transcript,
        }
    });
    compare("bend/bridge_progress.bend", scenarios);
}
