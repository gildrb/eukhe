//! The commands a run executed, as the harness recorded them: each call of
//! the `bash` tool with the exit status of every step it ran, how its
//! script ended and the tail of its output; and each process a python
//! cell's `bash()` started, with its exit code and the tail of its output
//! (the cell's result records the ones the cell read; the host's completion
//! notice, the ones that ended after their cell). The intent judge reads
//! them beside the workspace, so a requirement to run something (the
//! tests) is decided by what the record shows ran and how it ended, never
//! by the worker's word. Bounded: the newest runs only, each command and
//! each output cut.

use std::collections::HashMap;
use std::fmt::Write as _;

use eukhe_chord::context::Context;
use eukhe_durable::entries::TOOL_RESULT_ENTRY;
use eukhe_durable::harness::{Conversation, ConversationEntryQuery};
use eukhe_durable::session::SessionResult;
use eukhe_durable::types::EntryRecord;
use eukhe_types::pi_ai::{Message, UserContent, UserContentBlock};
use serde_json::Value;

use crate::durable::entries::CUSTOM_ENTRY;
use crate::durable::messages::{ASYNC_BASH_COMPLETION_CUSTOM_TYPE, JOB_SETTLED_CUSTOM_TYPE};
use crate::durable::rlm::PYTHON_VERSION;
use crate::durable::shell::VERSION as BASH_VERSION;

/// How many entries one read of the conversation takes.
const PAGE: usize = 64;
/// The most runs the judge reads: the newest.
const MAX_RUNS: usize = 12;
/// The most steps of one run the judge reads: its last.
const MAX_STEPS: usize = 20;
/// The most characters of one step's command.
const MAX_COMMAND_CHARS: usize = 300;
/// The most characters of one run's output: its tail.
const MAX_OUTPUT_CHARS: usize = 1500;
/// The most characters of all the runs, filled newest first.
const MAX_RUNS_CHARS: usize = 16_000;

/// One command the record shows ran.
enum Run {
    /// A call of the `bash` tool: its result's `bash@1` details and text.
    Tool { details: Value, output: String },
    /// A process a python cell's `bash()` started and the cell read: one
    /// of the `bashRuns` of its `python@1` result.
    Cell(Value),
    /// A `bash()` process that ended after its cell: the details of the
    /// host's completion notice.
    Noticed(Value),
}

/// How a detached script's job settled: its status and its text.
struct Settled {
    status: String,
    text: String,
}

/// The commands `conversation` ran, oldest first, for the judge: the
/// newest [`MAX_RUNS`] that fit in [`MAX_RUNS_CHARS`]. `None` when it ran
/// none.
///
/// # Errors
///
/// Read failures.
pub(crate) async fn ran_commands(
    conversation: &Conversation,
    cx: &Context,
) -> SessionResult<Option<String>> {
    // Newest first: a job settles after the call that detached it, so its
    // end is read before the call.
    let mut runs = Vec::new();
    let mut settled = HashMap::new();
    let mut earlier = false;
    let mut cursor = None;
    'read: loop {
        let page = conversation
            .entries(ConversationEntryQuery::default(), PAGE, cursor, cx)
            .await?;
        for entry in &page.items {
            if let Some((job, end)) = job_settled(entry) {
                settled.entry(job).or_insert(end);
                continue;
            }
            for run in runs_of(entry) {
                if runs.len() == MAX_RUNS {
                    earlier = true;
                    break 'read;
                }
                runs.push(run);
            }
        }
        match page.next {
            Some(next) => cursor = Some(next),
            None => break,
        }
    }
    Ok(render(&runs, &settled, earlier))
}

/// The runs `entry` records, newest first.
fn runs_of(entry: &EntryRecord) -> Vec<Run> {
    if entry.kind == TOOL_RESULT_ENTRY.kind() {
        let Some(Message::ToolResult(result)) =
            entry.model.as_ref().and_then(|model| model.first())
        else {
            return Vec::new();
        };
        let Some(details) = result.details.as_ref() else {
            return Vec::new();
        };
        return match details.get("version").and_then(Value::as_str) {
            Some(BASH_VERSION) => vec![Run::Tool {
                details: details.clone(),
                output: blocks_text(&result.content),
            }],
            Some(PYTHON_VERSION) => details
                .get("bashRuns")
                .and_then(Value::as_array)
                .map_or_else(Vec::new, |cell| {
                    cell.iter().rev().cloned().map(Run::Cell).collect()
                }),
            _ => Vec::new(),
        };
    }
    if entry.kind == CUSTOM_ENTRY.kind() {
        if let Some(custom) = CUSTOM_ENTRY.narrow(entry.clone()).ok().flatten() {
            let data = custom.data();
            if data.custom_type == ASYNC_BASH_COMPLETION_CUSTOM_TYPE {
                if let Some(details) = &data.details {
                    return vec![Run::Noticed(details.clone())];
                }
            }
        }
    }
    Vec::new()
}

/// The job and its end a `job_settled` row records.
fn job_settled(entry: &EntryRecord) -> Option<(String, Settled)> {
    if entry.kind != CUSTOM_ENTRY.kind() {
        return None;
    }
    let custom = CUSTOM_ENTRY.narrow(entry.clone()).ok().flatten()?;
    let data = custom.data();
    if data.custom_type != JOB_SETTLED_CUSTOM_TYPE {
        return None;
    }
    let details = data.details.as_ref()?;
    let job = details.get("job").and_then(Value::as_str)?.to_owned();
    let status = details.get("status").and_then(Value::as_str)?.to_owned();
    let text = match &data.content {
        Some(UserContent::Text(text)) => text.clone(),
        Some(UserContent::Blocks(blocks)) => blocks_text(blocks),
        None => String::new(),
    };
    Some((job, Settled { status, text }))
}

fn blocks_text(blocks: &[UserContentBlock]) -> String {
    blocks
        .iter()
        .filter_map(|block| match block {
            UserContentBlock::Text(text) => Some(text.text.as_str()),
            UserContentBlock::Image(_) => None,
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// The runs (`runs` newest first) as the judge reads them, oldest first;
/// `earlier` when older runs were left out.
fn render(runs: &[Run], settled: &HashMap<String, Settled>, earlier: bool) -> Option<String> {
    let mut shown = Vec::new();
    let mut size = 0;
    for run in runs {
        let text = describe(run, settled);
        size += text.chars().count();
        if size > MAX_RUNS_CHARS && !shown.is_empty() {
            break;
        }
        shown.push(text);
    }
    if shown.is_empty() {
        return None;
    }
    let order = if earlier || shown.len() < runs.len() {
        format!(
            "the last {}, oldest first; earlier runs left out",
            shown.len()
        )
    } else {
        "oldest first".to_owned()
    };
    shown.reverse();
    Some(format!(
        "Commands the worker ran, as the harness recorded them ({order}; each with its exit status):\n{}",
        shown.join("\n")
    ))
}

/// One run: what ran with its exit status, how it ended, the tail of its
/// output.
fn describe(run: &Run, settled: &HashMap<String, Settled>) -> String {
    match run {
        Run::Tool { details, output } => describe_tool(details, output, settled),
        Run::Cell(run) => {
            let mut text = String::from("--- `bash()` in a python cell\n");
            let _ = writeln!(
                text,
                "`{}` exited {}",
                command(run.get("command")),
                number(run.get("exitCode"))
            );
            push_output(
                &mut text,
                run.get("output").and_then(Value::as_str).unwrap_or(""),
            );
            text
        }
        Run::Noticed(notice) => {
            let mut text = String::from("--- `bash()` in a python cell, ended after the cell\n");
            let _ = write!(
                text,
                "`{}` exited {}",
                command(notice.get("command")),
                number(notice.get("exitCode"))
            );
            if let Some(stopper) = notice.get("stoppedBy").and_then(Value::as_str) {
                let _ = write!(text, " (stopped by {stopper})");
            }
            text
        }
    }
}

/// A call of the `bash` tool: its steps with their exit statuses, how its
/// script ended, the tail of its output.
fn describe_tool(details: &Value, output: &str, settled: &HashMap<String, Settled>) -> String {
    let mut text = String::from("--- `bash` tool run\n");
    let steps = details
        .get("steps")
        .and_then(Value::as_array)
        .map_or(&[][..], Vec::as_slice);
    if steps.len() > MAX_STEPS {
        let _ = writeln!(text, "({} earlier steps left out)", steps.len() - MAX_STEPS);
    }
    for step in &steps[steps.len().saturating_sub(MAX_STEPS)..] {
        let _ = writeln!(
            text,
            "step {} `{}` exited {}",
            number(step.get("step")),
            command(step.get("command")),
            number(step.get("status"))
        );
    }
    let mut output = output;
    if details.get("status").and_then(Value::as_str) == Some("detached") {
        let job = details
            .get("job")
            .and_then(|job| job.get("id"))
            .and_then(Value::as_str)
            .unwrap_or("?");
        match settled.get(job) {
            Some(end) => {
                let _ = writeln!(
                    text,
                    "the script outlived the blocking budget and ran on as job {job}, which settled with status {}",
                    end.status
                );
                output = &end.text;
            }
            None => {
                let _ = writeln!(
                    text,
                    "the script outlived the blocking budget and ran on as job {job}; the record holds no end of it"
                );
            }
        }
    } else {
        let end = details.get("end");
        let status = number(end.and_then(|end| end.get("status")));
        let _ = match end.and_then(|end| end.get("kind")).and_then(Value::as_str) {
            Some("finished") => writeln!(text, "the script ended with status {status}"),
            Some("exited") => writeln!(text, "the script ran `exit` with status {status}"),
            Some("refused") => {
                let end = end.unwrap_or(&Value::Null);
                writeln!(
                    text,
                    "step {} `{}` did not run ({}); the steps after it did not run",
                    number(end.get("step")),
                    command(end.get("command")),
                    end.get("refusal")
                        .and_then(Value::as_str)
                        .unwrap_or("refused")
                        .replace('_', " ")
                )
            }
            _ => writeln!(text, "the record holds no end of this run"),
        };
    }
    push_output(&mut text, output);
    text
}

/// The tail of `output`, cut to [`MAX_OUTPUT_CHARS`].
fn push_output(text: &mut String, output: &str) {
    let output = output.trim();
    if output.is_empty() {
        text.push_str("no output");
        return;
    }
    let count = output.chars().count();
    if count > MAX_OUTPUT_CHARS {
        let tail: String = output.chars().skip(count - MAX_OUTPUT_CHARS).collect();
        let _ = write!(
            text,
            "output, its last {MAX_OUTPUT_CHARS} characters:\n{tail}"
        );
    } else {
        let _ = write!(text, "output:\n{output}");
    }
}

/// A recorded number; `?` when it is missing.
fn number(value: Option<&Value>) -> String {
    value
        .and_then(Value::as_i64)
        .map_or_else(|| "?".to_owned(), |number| number.to_string())
}

/// A recorded command, cut to [`MAX_COMMAND_CHARS`].
fn command(value: Option<&Value>) -> String {
    let command = value.and_then(Value::as_str).unwrap_or("?");
    if command.chars().count() <= MAX_COMMAND_CHARS {
        return command.to_owned();
    }
    let prefix: String = command.chars().take(MAX_COMMAND_CHARS).collect();
    format!("{prefix}...")
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    fn run(command: &str, status: i64, output: &str) -> Run {
        Run::Tool {
            details: json!({
                "version": BASH_VERSION,
                "steps": [{ "step": 1, "command": command, "status": status }],
                "end": { "kind": "finished", "status": status },
            }),
            output: output.to_owned(),
        }
    }

    /// Each run shows what ran with its exit status, how it ended and its
    /// output, oldest first: a `bash` tool run its steps, a refused step and
    /// a detached script's settled job; a python cell's `bash()` its
    /// command, and one that ended after its cell how the notice says.
    #[test]
    fn runs_show_their_commands_their_ends_and_their_output() {
        let refused = Run::Tool {
            details: json!({
                "version": BASH_VERSION,
                "steps": [],
                "end": { "kind": "refused", "step": 1, "command": "rm -rf /", "refusal": "denied" },
            }),
            output: String::new(),
        };
        let detached = Run::Tool {
            details: json!({
                "version": BASH_VERSION,
                "status": "detached",
                "job": { "id": "shell-1", "kind": "shell" },
            }),
            output: "collecting".to_owned(),
        };
        let cell =
            Run::Cell(json!({ "command": "pytest -q", "exitCode": 0, "output": "5 passed" }));
        let noticed = Run::Noticed(
            json!({ "pid": 7, "command": "sleep 9", "exitCode": 143, "stoppedBy": "agent" }),
        );
        let settled = HashMap::from([(
            "shell-1".to_owned(),
            Settled {
                status: "ok".to_owned(),
                text: "[step 1 exited 0]\n9 passed".to_owned(),
            },
        )]);
        assert_eq!(
            render(
                &[noticed, cell, detached, refused, run("pytest -q", 0, "3 passed\n")],
                &settled,
                false
            ),
            Some(
                "Commands the worker ran, as the harness recorded them (oldest first; each with its exit status):\n\
                 --- `bash` tool run\nstep 1 `pytest -q` exited 0\nthe script ended with status 0\noutput:\n3 passed\n\
                 --- `bash` tool run\nstep 1 `rm -rf /` did not run (denied); the steps after it did not run\nno output\n\
                 --- `bash` tool run\nthe script outlived the blocking budget and ran on as job shell-1, which settled with status ok\noutput:\n[step 1 exited 0]\n9 passed\n\
                 --- `bash()` in a python cell\n`pytest -q` exited 0\noutput:\n5 passed\n\
                 --- `bash()` in a python cell, ended after the cell\n`sleep 9` exited 143 (stopped by agent)"
                    .to_owned()
            )
        );
        assert_eq!(render(&[], &settled, false), None);
    }

    /// The judge reads the newest runs within the bound, the tail of each
    /// output and the last steps of each run, and is told what was left out.
    #[test]
    fn runs_are_bounded_newest_first() {
        let long = "x".repeat(MAX_OUTPUT_CHARS) + "END";
        let runs: Vec<Run> = (0..MAX_RUNS)
            .map(|index| run(&format!("cmd{index}"), 0, &long))
            .collect();
        let text = render(&runs, &HashMap::new(), true).expect("runs");
        assert!(
            text.chars().count() <= MAX_RUNS_CHARS + 200,
            "{}",
            text.len()
        );
        assert!(text.contains("earlier runs left out"), "{text}");
        assert!(text.contains("`cmd0` exited 0"), "the newest run is kept");
        assert!(
            !text.contains(&format!("`cmd{}`", MAX_RUNS - 1)),
            "the oldest is left out"
        );
        assert!(text.contains(&format!(
            "output, its last {MAX_OUTPUT_CHARS} characters:\n{}END",
            "x".repeat(MAX_OUTPUT_CHARS - 3)
        )));
        let steps: Vec<Value> = (1..=30)
            .map(|step| json!({ "step": step, "command": "true", "status": 0 }))
            .collect();
        let many = Run::Tool {
            details: json!({ "version": BASH_VERSION, "steps": steps, "end": { "kind": "finished", "status": 0 } }),
            output: String::new(),
        };
        let text = render(&[many], &HashMap::new(), false).expect("a run");
        assert!(
            text.contains("(10 earlier steps left out)\nstep 11 `true` exited 0\n"),
            "{text}"
        );
        assert!(!text.contains("step 10 "), "{text}");
    }
}
