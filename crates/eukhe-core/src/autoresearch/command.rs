//! `/autoresearch <goal> | off | status | clear` (port of the omp
//! command): `<goal>` puts the workspace on an `autoresearch/*` branch,
//! turns the Lab's mode on, starts the loop's continuation and asks the
//! model to set up the harness (a new session) or resume (an open one);
//! `off` turns the mode and the loop off; `status` (or no argument)
//! reports; `clear` turns everything off and moves the branch's store
//! aside.

use eukhe_bend::rules::autoresearch::{Direction, Mode, Snapshot};
use eukhe_chord::context::Context;
use eukhe_durable::harness::types::{InputSubmissionDraft, WhenBusy};
use eukhe_durable::harness::Conversation;
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::pi_ai::UserContent;
use serde_json::Value;

use super::host::{follow_mode, of};
use super::ops::Reply;
use crate::durable::EukheSession;

/// Run `/autoresearch <args>` on `conversation`; the text of its result
/// row.
///
/// # Errors
///
/// The failure as the result row reads it.
pub(crate) async fn execute(
    session: &EukheSession,
    conversation: &Conversation,
    args: &str,
    cx: &Context,
) -> Result<String, String> {
    let failed = |error: anyhow::Error| format!("{error:#}");
    let lab = of(session.deps());
    let harness = session.harness();
    let id = conversation.id();
    match args.trim() {
        "" | "status" => Ok(status_text(&lab.snapshot().await.map_err(failed)?)),
        "off" => {
            let reply = lab.set_mode(Mode::Off).await.map_err(failed)?;
            follow_mode(harness, id, &reply).await.map_err(failed)?;
            Ok("Autoresearch mode off: the loop stops after this turn.".to_owned())
        }
        "clear" => {
            let aside = lab.clear().await.map_err(failed)?;
            let reply = Reply {
                value: Value::Null,
                mode: Mode::Off,
                started: false,
            };
            follow_mode(harness, id, &reply).await.map_err(failed)?;
            Ok(format!(
                "Autoresearch session closed; its log moved to {}.",
                aside.display()
            ))
        }
        goal => {
            let begun = lab.begin(goal).await.map_err(failed)?;
            let reply = Reply {
                value: Value::Null,
                mode: Mode::On,
                started: true,
            };
            follow_mode(harness, id, &reply).await.map_err(failed)?;
            let branch = begun.branch.line();
            let text = if begun.configured {
                format!(
                    "Resume autoresearch on the open session.\n\n{branch}\n\nAdditional context from \
the user:\n\n{goal}\n\n- Call `await autoresearch.state()`: it is the source of truth for the goal, \
scope and run history.\n- Inspect recent git history for context.\n- Continue the most promising \
unfinished direction.\n- Keep iterating until the user stops you or the iteration cap is reached."
                )
            } else {
                format!(
                    "Autoresearch mode is on. Goal: {goal}\n\n{branch}\n\nFollow the autoresearch \
skill. First build the benchmark harness: write `autoresearch.sh` in the repository root (exit 0 on \
success, a deterministic workload, one `METRIC <name>=<value>` line for the primary metric), \
validate it with `bash autoresearch.sh`, then call `await autoresearch.init(...)` and run the \
baseline."
                )
            };
            conversation
                .submit(
                    InputSubmissionDraft {
                        request_id: None,
                        content: UserContent::Text(text),
                        when_busy: Some(WhenBusy::FollowUp),
                        origin: InputOrigin::User,
                        entry: None,
                    },
                    cx,
                )
                .await
                .map_err(|error| error.to_string())?;
            Ok(format!("Autoresearch mode on. {branch}"))
        }
    }
}

/// The `/autoresearch status` line.
fn status_text(snapshot: &Snapshot) -> String {
    let mode = match snapshot.mode {
        Mode::On => "on",
        Mode::Off => "off",
    };
    let Some(config) = &snapshot.config else {
        return format!("Autoresearch mode {mode}; no session on this branch yet.");
    };
    let better = match config.direction {
        Direction::Lower => "lower",
        Direction::Higher => "higher",
    };
    let unit = if config.unit.is_empty() {
        String::new()
    } else {
        format!(" {}", config.unit)
    };
    let shown = |value: Option<&eukhe_bend::rules::autoresearch::Metric>| {
        value.map_or_else(|| "none".to_owned(), |value| format!("{value}{unit}"))
    };
    let cap = config
        .max_iterations
        .map_or_else(String::new, |max| format!("/{max}"));
    let pending = snapshot
        .pending
        .map_or_else(String::new, |run| format!("; run #{run} waits for its log"));
    format!(
        "Autoresearch mode {mode}: {} ({}, {better} is better). Segment {}: {}{cap} runs logged; \
baseline {}; best {}{pending}.",
        config.name,
        config.metric,
        snapshot.segment,
        snapshot.logged_in_segment,
        shown(snapshot.baseline.as_ref()),
        shown(snapshot.best.as_ref()),
    )
}
