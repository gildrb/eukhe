//! LLM-facing message conversion. Port of convertToLlm and the message
//! presentation constants in core/messages.ts.

use crate::agent_messaging::sanitize_message_header_value;
use crate::cron::AgentCronJob;
use eukhe_types::ai::{TextContent, UserContent, UserContentBlock, UserMessage};
use eukhe_types::input_origin::Report;
use eukhe_types::job::JobSettled;
use eukhe_types::output::{bound_notice, OmittedOutput};
use eukhe_types::session::AgentMessage;
use std::fmt::Write as _;

pub const COMPACTION_SUMMARY_PREFIX: &str = "[compaction-summary]\n\nThe conversation history before this point was compacted into the following summary.\nThe retained messages below are authoritative; this summary may lag behind them.\n\n<summary>\n";
pub const COMPACTION_SUMMARY_SUFFIX: &str = "\n</summary>";
pub const BRANCH_SUMMARY_PREFIX: &str = "[branch-summary]\n\nThe following is a summary of a branch that this conversation came back from:\n\n<summary>\n";
pub const BRANCH_SUMMARY_SUFFIX: &str = "\n</summary>";
pub const HARNESS_DIGEST_PREFIX: &str = "[harness-digest]\n\nThe persistent memories produced across this session so far:\n\n<harness_state>\n";
pub const HARNESS_DIGEST_SUFFIX: &str = "\n</harness_state>";

pub use eukhe_types::slash_commands::{
    SESSION_SLASH_COMMAND_CUSTOM_TYPE, SESSION_SLASH_COMMAND_RESULT_CUSTOM_TYPE,
};
pub const COMPACTION_OUTCOME_CUSTOM_TYPE: &str = "compaction_outcome";
pub const REFINEMENT_OUTCOME_CUSTOM_TYPE: &str = "refinement_outcome";
pub const REFINEMENT_NOTICE_CUSTOM_TYPE: &str = "refinement_notice";
/// Audit entry type recording each applied refinement.
pub const REFINEMENT_AUDIT_CUSTOM_TYPE: &str = "eukhe.refinement";
/// The custom type of the harness-digest row (the model-facing digest of
/// the continual-harness state).
pub const HARNESS_DIGEST_CUSTOM_TYPE: &str = "harness_digest";
/// The durable single-row disclosure of one provider-retry episode
/// (SANCTIONED DIVERGENCE from TS, operator ruling 2026-09-23: the TS chat
/// leaves one error row per failed attempt, which a 429-storm turned into
/// chat spam): a `provider_retry_outcome` custom message carrying the one
/// resolved/terminal row of the whole episode, with
/// `{success, attempts, finalError}` details. Like the compaction outcome
/// it is a user-facing disclosure, never model context — `convert_to_llm`
/// drops it.
pub const PROVIDER_RETRY_OUTCOME_CUSTOM_TYPE: &str = "provider_retry_outcome";
pub const HEARTBEAT_PROMPT_CUSTOM_TYPE: &str = "heartbeat_prompt";
/// TS `ASYNC_BASH_COMPLETION_CUSTOM_TYPE`: the durable row a detached
/// kernel bash completion admits as the woken turn's injected prompt.
pub const ASYNC_BASH_COMPLETION_CUSTOM_TYPE: &str = "async_bash_completion";
/// The durable row a settled detached `ipython` cell admits as the woken
/// turn's injected prompt.
pub const JOB_SETTLED_CUSTOM_TYPE: &str = "job_settled";
/// TS `SESSION_RENAMED_CUSTOM_TYPE` (#2529): the displayed notice a
/// rename that changed an existing name leaves in the renamed session's
/// transcript.
pub const SESSION_RENAMED_CUSTOM_TYPE: &str = "session_renamed";
/// TS `ASYNC_BASH_COMPLETION_PREVIEW_LABEL`: the queue-strip label the
/// notice's queued row carries (the TUI renders it with its own label,
/// no lane prefix).
pub const ASYNC_BASH_COMPLETION_PREVIEW_LABEL: &str = "Background command finished";
/// The queue-strip preview label for a parked heartbeat fire (TS
/// `HEARTBEAT_PROMPT_PREVIEW_LABEL`): the queued row reads
/// `Heartbeat prompt: <content>` instead of the lane-labeled preview.
pub const HEARTBEAT_PROMPT_PREVIEW_LABEL: &str = "Heartbeat prompt";

/// Why an unsuccessful compaction ran (TS `CompactionOutcomeReason`): the
/// automatic threshold trigger, the overflow recovery, or the model's
/// `compact.run` request consumed at a turn boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompactionOutcomeReason {
    /// The context crossed the auto-compaction threshold.
    Threshold,
    /// A context-overflow recovery attempt.
    Overflow,
    /// The model requested the compaction (`compact.run`).
    Requested,
}

impl CompactionOutcomeReason {
    /// The wire `reason` string: the outcome row's `details.reason` and the
    /// `compaction_end` event's `reason`.
    #[must_use]
    pub fn wire(self) -> &'static str {
        match self {
            Self::Threshold => "threshold",
            Self::Overflow => "overflow",
            Self::Requested => "requested",
        }
    }
}

/// How an unsuccessful compaction ended (TS `CompactionOutcome`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompactionOutcomeKind {
    /// Nothing to summarize (TS `CompactionSkippedError`).
    Skipped,
    /// Aborted mid-run.
    Cancelled,
    /// The summarization failed.
    Failed,
}

impl CompactionOutcomeKind {
    /// The wire `outcome` string: the outcome row's `details.outcome`.
    #[must_use]
    pub fn wire(self) -> &'static str {
        match self {
            Self::Skipped => "skipped",
            Self::Cancelled => "cancelled",
            Self::Failed => "failed",
        }
    }
}

fn now_millis() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |duration| duration.as_millis() as u64)
}

/// The resolved-line text of a retry episode that recovered: the last
/// error plus how many retries it took. This is the ONE line the episode
/// leaves in the chat (live and rebuilt), replacing the per-attempt error
/// rows TS keeps.
#[must_use]
pub fn provider_retry_recovered_text(attempts: u32, last_error: &str) -> String {
    format!("Recovered after {attempts} retries: {last_error}")
}

/// The terminal-line text of a retry episode that gave up: the same text
/// the TS `auto_retry_end` live row carries, so the durable row and the
/// live one read identically. A zero-attempt failure (the
/// failure-scoped disclosure of a permanent classification on the first
/// attempt) never retried, so it reads as the plain provider failure it
/// is -- TS never emits this shape (that omission is the silent empty
/// message the disclosure now covers).
#[must_use]
pub fn provider_retry_exhausted_text(attempts: u32, final_error: &str) -> String {
    if attempts == 0 {
        format!("! Error: {final_error}")
    } else {
        format!("! Error: Retry failed after {attempts} attempts: {final_error}")
    }
}

/// The durable disclosure row of one provider-retry episode (see
/// [`PROVIDER_RETRY_OUTCOME_CUSTOM_TYPE`]): `content` carries the row text
/// the chat renders, `details` the structured verdict.
#[must_use]
pub fn create_provider_retry_outcome_message(
    success: bool,
    attempts: u32,
    error: &str,
) -> eukhe_types::session::CustomMessage {
    let content = if success {
        provider_retry_recovered_text(attempts, error)
    } else {
        provider_retry_exhausted_text(attempts, error)
    };
    eukhe_types::session::CustomMessage {
        custom_type: PROVIDER_RETRY_OUTCOME_CUSTOM_TYPE.to_string(),
        content: UserContent::Text(content),
        display: true,
        details: Some(serde_json::json!({
            "success": success,
            "attempts": attempts,
            "finalError": error,
        })),
        timestamp: now_millis(),
        rest: serde_json::Map::default(),
    }
}

/// The durable disclosure row for an unsuccessful compaction (TS
/// `createCompactionOutcomeMessage`): a `compaction_outcome` custom message
/// carrying the outcome message and `{reason, outcome}` details. It is a
/// user-facing disclosure, never model context — `convert_to_llm` drops it,
/// so the KV-cacheable prefix is unaffected.
#[must_use]
pub fn create_compaction_outcome_message(
    content: &str,
    reason: CompactionOutcomeReason,
    outcome: CompactionOutcomeKind,
) -> eukhe_types::session::CustomMessage {
    eukhe_types::session::CustomMessage {
        custom_type: COMPACTION_OUTCOME_CUSTOM_TYPE.to_string(),
        content: UserContent::Text(content.to_string()),
        display: true,
        details: Some(serde_json::json!({
            "reason": reason.wire(),
            "outcome": outcome.wire(),
        })),
        timestamp: now_millis(),
        rest: serde_json::Map::default(),
    }
}

/// The report of one heartbeat fire: the sanitized schedule and the run.
#[must_use]
pub fn heartbeat_report(job: &AgentCronJob) -> Report {
    Report::Heartbeat {
        schedule: sanitize_message_header_value(&job.schedule.expression),
        run: job.run_count,
    }
}

/// The durable heartbeat delivery row (TS `createHeartbeatPromptMessage`):
/// a `heartbeat_prompt` custom message carrying the job's prompt under the
/// `[heartbeat: <schedule> run#<n>]` header, with the job's run bookkeeping
/// in details. The header value is sanitized like every other
/// `[<kind> ...]` header (TS `sanitizeMessageHeaderValue`); the daemon's
/// fire delivers the row as the turn's injected prompt, so the transcript
/// renders the heartbeat component instead of a plain user message.
#[must_use]
pub fn create_heartbeat_prompt_message(
    job: &AgentCronJob,
    timestamp: u64,
) -> eukhe_types::session::CustomMessage {
    let content = heartbeat_report(job).render(&job.prompt);
    // The details block mirrors the TS JSON exactly: the fixed keys in
    // the TS order, and the optional `nextRunAt`/`lastRunAt` omitted
    // while undefined (TS `JSON.stringify` drops undefined fields, so a
    // first fire carries no `lastRunAt`).
    let mut details = serde_json::Map::new();
    details.insert("jobId".to_string(), serde_json::json!(job.id));
    details.insert(
        "schedule".to_string(),
        serde_json::json!(job.schedule.expression),
    );
    details.insert(
        "status".to_string(),
        serde_json::to_value(job.status).unwrap_or(serde_json::Value::Null),
    );
    details.insert("runCount".to_string(), serde_json::json!(job.run_count));
    if let Some(next_run_at) = &job.next_run_at {
        details.insert("nextRunAt".to_string(), serde_json::json!(next_run_at));
    }
    if let Some(last_run_at) = &job.last_run_at {
        details.insert("lastRunAt".to_string(), serde_json::json!(last_run_at));
    }
    eukhe_types::session::CustomMessage {
        custom_type: HEARTBEAT_PROMPT_CUSTOM_TYPE.to_string(),
        content: UserContent::Text(content),
        display: true,
        details: Some(serde_json::Value::Object(details)),
        timestamp,
        rest: serde_json::Map::default(),
    }
}

/// The row a settled job admits as the woken turn's injected prompt (the
/// daemon's one job-settled wake; ADR 0010):
/// - a background kernel `bash()` command (TS
///   `createAsyncBashCompletionMessage`): an `async_bash_completion` row
///   carrying `[bash-done pid:N exit:M]` plus the JSON-encoded command, with
///   `{pid, command, exitCode}` in details; a later kernel read that
///   reaches the model first withdraws it through its details
///   (`bash.consumed`);
/// - a detached `ipython` cell or `bash` tool script: a `job_settled` row
///   carrying `[job-settled job:ID status:S]` plus its bounded output,
///   with `{job, status}` in details.
#[must_use]
pub fn create_job_settled_message(
    settled: &JobSettled,
    timestamp: u64,
) -> eukhe_types::session::CustomMessage {
    let report = settled.report();
    let (custom_type, content, details) = match settled {
        JobSettled::Bash {
            pid,
            command,
            exit_code,
        } => {
            // TS `JSON.stringify(details.command)`: the quoted, escaped command.
            let encoded_command = serde_json::to_string(command).unwrap_or_default();
            (
                ASYNC_BASH_COMPLETION_CUSTOM_TYPE,
                report.render(&format!("Command: {encoded_command}")),
                serde_json::json!({
                    "pid": pid,
                    "command": command,
                    "exitCode": exit_code,
                }),
            )
        }
        JobSettled::Cell {
            job,
            status,
            output,
        }
        | JobSettled::Shell {
            job,
            status,
            output,
        } => (
            JOB_SETTLED_CUSTOM_TYPE,
            report.render(output),
            serde_json::json!({ "job": job.as_str(), "status": status.label() }),
        ),
    };
    eukhe_types::session::CustomMessage {
        custom_type: custom_type.to_string(),
        content: UserContent::Text(content),
        display: true,
        details: Some(details),
        timestamp,
        rest: serde_json::Map::default(),
    }
}

/// Bash output rendered as a fenced block with a fence longer than any
/// backtick run inside the output.
fn bash_output_to_text(
    output: &str,
    exit_code: Option<i64>,
    cancelled: bool,
    omitted: Option<&OmittedOutput>,
    artifact: Option<&str>,
) -> String {
    let mut text = String::new();
    if output.is_empty() {
        text.push_str("(no output)");
    } else {
        let longest = output
            .match_indices('`')
            .fold(0usize, |longest, (index, _)| {
                let mut run = 0usize;
                let mut chars = output[index..].chars();
                while chars.next() == Some('`') {
                    run += 1;
                }
                run.max(longest)
            });
        let fence = "`".repeat(longest.max(3).max(longest + 1));
        text.push_str(&fence);
        text.push('\n');
        text.push_str(output);
        text.push('\n');
        text.push_str(&fence);
    }
    if cancelled {
        text.push_str("\n\n(command cancelled)");
    } else if let Some(code) = exit_code {
        if code != 0 {
            let _ = write!(text, "\n\nCommand exited with code {code}");
        }
    }
    if omitted.is_some() || artifact.is_some() {
        text.push_str("\n\n");
        text.push_str(&bound_notice(omitted, artifact));
    }
    text
}

/// Bash execution as user-facing text for LLM context.
#[must_use]
pub fn bash_execution_to_text(message: &eukhe_types::session::BashExecutionMessage) -> String {
    format!(
        "Ran `{}`\n{}",
        message.command,
        bash_output_to_text(
            &message.output,
            message.exit_code,
            message.cancelled,
            message.omitted.as_ref(),
            message.artifact.as_deref(),
        )
    )
}

fn text_block(text: String) -> UserContentBlock {
    UserContentBlock::Text(TextContent {
        text,
        text_signature: None,
        rest: serde_json::Map::default(),
        cache_breakpoint: None,
    })
}

/// The LLM message view of session messages: session-only roles become user
/// text turns; bookkeeping custom types drop out entirely.
#[must_use]
pub fn convert_to_llm(messages: &[AgentMessage]) -> Vec<AgentMessage> {
    let mut out = Vec::new();
    for message in messages {
        let converted = match message {
            AgentMessage::BashExecution(bash) => {
                if bash.exclude_from_context.unwrap_or(false) {
                    continue;
                }
                AgentMessage::User(UserMessage {
                    content: UserContent::Blocks(vec![text_block(bash_execution_to_text(bash))]),
                    timestamp: bash.timestamp,
                    rest: serde_json::Map::default(),
                })
            }
            AgentMessage::Custom(custom) => {
                if matches!(
                    custom.custom_type.as_str(),
                    SESSION_SLASH_COMMAND_CUSTOM_TYPE
                        | SESSION_SLASH_COMMAND_RESULT_CUSTOM_TYPE
                        | COMPACTION_OUTCOME_CUSTOM_TYPE
                        | REFINEMENT_OUTCOME_CUSTOM_TYPE
                        | PROVIDER_RETRY_OUTCOME_CUSTOM_TYPE
                        | crate::prompts::model_prompts::MODEL_PROMPT_ERROR_CUSTOM_TYPE
                        | crate::durable::settings::SETTINGS_ERROR_CUSTOM_TYPE
                        | crate::durable::compaction::auxiliary_model::AUXILIARY_MODEL_NOTICE_CUSTOM_TYPE
                ) {
                    continue;
                }
                // TS wraps a string content into a text-part array and
                // passes block content through (the request's cacheable
                // shape is the array either way).
                let content = match custom.content.clone() {
                    UserContent::Text(text) => UserContent::Blocks(vec![text_block(text)]),
                    blocks @ UserContent::Blocks(_) => blocks,
                };
                AgentMessage::User(UserMessage {
                    content,
                    timestamp: custom.timestamp,
                    rest: serde_json::Map::default(),
                })
            }
            AgentMessage::BranchSummary(summary) => AgentMessage::User(UserMessage {
                content: UserContent::Blocks(vec![text_block(format!(
                    "{BRANCH_SUMMARY_PREFIX}{}{BRANCH_SUMMARY_SUFFIX}",
                    summary.summary
                ))]),
                timestamp: summary.timestamp,
                rest: serde_json::Map::default(),
            }),
            AgentMessage::CompactionSummary(summary) => {
                let digest_block = summary
                    .harness_digest
                    .as_deref()
                    .map(|digest| {
                        format!("{HARNESS_DIGEST_PREFIX}{digest}{HARNESS_DIGEST_SUFFIX}\n\n")
                    })
                    .unwrap_or_default();
                AgentMessage::User(UserMessage {
                    content: UserContent::Blocks(vec![text_block(format!(
                        "{digest_block}{COMPACTION_SUMMARY_PREFIX}{}{COMPACTION_SUMMARY_SUFFIX}",
                        summary.summary
                    ))]),
                    timestamp: summary.timestamp,
                    rest: serde_json::Map::default(),
                })
            }
            AgentMessage::User(_) | AgentMessage::Assistant(_) | AgentMessage::ToolResult(_) => {
                message.clone()
            }
        };
        out.push(converted);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The retry-outcome row (SANCTIONED DIVERGENCE, operator ruling
    /// 2026-09-23): one durable line per episode — the recovered and
    /// exhausted texts, the structured details — and never model context.
    #[test]
    fn provider_retry_outcome_row_is_the_one_line_and_never_context() {
        let recovered =
            create_provider_retry_outcome_message(true, 3, "429 Too many concurrent requests");
        assert_eq!(recovered.custom_type, PROVIDER_RETRY_OUTCOME_CUSTOM_TYPE);
        assert_eq!(
            recovered.content,
            UserContent::Text(
                "Recovered after 3 retries: 429 Too many concurrent requests".to_string()
            )
        );
        assert!(recovered.display);
        assert_eq!(
            recovered.details,
            Some(serde_json::json!({
                "success": true,
                "attempts": 3,
                "finalError": "429 Too many concurrent requests",
            }))
        );
        let exhausted = create_provider_retry_outcome_message(false, 2, "provider down");
        assert_eq!(
            exhausted.content,
            UserContent::Text("! Error: Retry failed after 2 attempts: provider down".to_string())
        );
        // The disclosure never enters the model context.
        let converted = convert_to_llm(&[AgentMessage::Custom(recovered)]);
        assert!(
            converted.is_empty(),
            "outcome row must not convert to LLM context"
        );
    }

    #[test]
    fn model_prompt_error_row_is_never_context() {
        let message = crate::prompts::model_prompts::model_prompt_error_message(&[
            "/x/model-prompts.toml: bad TOML".to_string(),
        ]);
        assert!(convert_to_llm(&[AgentMessage::Custom(message)]).is_empty());
    }

    #[test]
    fn bash_output_fences_and_status() {
        let omitted = OmittedOutput {
            bytes: 9,
            lines: 2,
            at: eukhe_types::output::OmittedAt::AfterLine(1),
        };
        let rendered = bash_output_to_text(
            "has `ticks` inside",
            Some(1),
            false,
            Some(&omitted),
            Some("/tmp/full.txt"),
        );
        assert!(rendered.contains("```\nhas `ticks` inside\n```")); // default fence
        assert!(rendered.contains("Command exited with code 1"));
        assert!(rendered.ends_with("<harness>\n[info] Output bounded. 9 bytes (2 lines) omitted after line 1. Full output: /tmp/full.txt\n</harness>"));
        assert!(bash_output_to_text("", None, false, None, None).contains("(no output)"));
        let cancelled = bash_output_to_text("x", None, true, None, None);
        assert!(cancelled.contains("(command cancelled)"));
        // A 3-backtick run in the output forces a 4-backtick fence.
        let fenced = bash_output_to_text("a ``` b", None, false, None, None);
        assert!(fenced.contains("````\na ``` b\n````"));
    }

    #[test]
    fn conversion_wraps_summaries_and_drops_bookkeeping() {
        let messages = vec![
            AgentMessage::User(UserMessage {
                content: UserContent::Text("keep me".to_string()),
                timestamp: 0,
                rest: serde_json::Map::default(),
            }),
            AgentMessage::Custom(eukhe_types::session::CustomMessage {
                custom_type: SESSION_SLASH_COMMAND_CUSTOM_TYPE.to_string(),
                content: UserContent::Text("/model".to_string()),
                display: true,
                details: None,
                timestamp: 0,
                rest: serde_json::Map::default(),
            }),
            AgentMessage::Custom(eukhe_types::session::CustomMessage {
                custom_type: "arbitrary_note".to_string(),
                content: UserContent::Text("a note".to_string()),
                display: true,
                details: None,
                timestamp: 0,
                rest: serde_json::Map::default(),
            }),
            AgentMessage::BranchSummary(eukhe_types::session::BranchSummaryMessage {
                summary: "the branch".to_string(),
                from_id: "x".to_string(),
                timestamp: 0,
            }),
            AgentMessage::CompactionSummary(eukhe_types::session::CompactionSummaryMessage {
                summary: "the story".to_string(),
                tokens_before: 1,
                retained_message_count: None,
                custom_instructions: None,
                harness_digest: Some("digest".to_string()),
                harness_state_fingerprint: None,
                timestamp: 0,
            }),
        ];
        let converted = convert_to_llm(&messages);
        // Bookkeeping custom dropped; other custom becomes user.
        assert_eq!(converted.len(), 4);
        assert!(matches!(converted[0], AgentMessage::User(_)));
        let note = match &converted[1] {
            AgentMessage::User(user) => user.content.text(),
            _ => panic!("expected user"),
        };
        assert_eq!(note, "a note");
        let branch = match &converted[2] {
            AgentMessage::User(user) => user.content.text(),
            _ => panic!("expected user"),
        };
        assert!(branch.contains("[branch-summary]"));
        assert!(branch.contains("the branch"));
        let compaction = match &converted[3] {
            AgentMessage::User(user) => user.content.text(),
            _ => panic!("expected user"),
        };
        assert!(compaction.contains("[harness-digest]"));
        assert!(compaction.contains("<harness_state>\ndigest\n</harness_state>"));
        assert!(compaction.contains("[compaction-summary]"));
        assert!(compaction.contains("the story"));
    }

    #[test]
    fn heartbeat_prompt_message_matches_the_ts_shape() {
        let job = AgentCronJob {
            id: "job-1".to_string(),
            status: crate::cron::JobStatus::Active,
            source: crate::cron::JobSource::RlmHeartbeat,
            runtime_kind: None,
            delivery_mode: Some(crate::cron::DeliveryMode::Steer),
            active_session_id: "live-1".to_string(),
            session_id: "session-1".to_string(),
            session_file: "/w/session.jsonl".to_string(),
            cwd: "/w".to_string(),
            label: Some("mission".to_string()),
            prompt: "check the mission".to_string(),
            schedule: crate::cron::AgentCronSchedule {
                kind: crate::cron::ScheduleKind::Interval,
                expression: "every 10m".to_string(),
                interval_ms: Some(600_000),
            },
            created_at: "2026-09-22T00:00:00.000Z".to_string(),
            updated_at: "2026-09-22T00:00:00.000Z".to_string(),
            next_run_at: Some("2026-09-22T00:10:00.000Z".to_string()),
            last_run_at: None,
            last_skipped_at: None,
            last_error: None,
            run_count: 0,
            failure_streak: 0,
        };
        let message = create_heartbeat_prompt_message(&job, 1_000);
        assert_eq!(message.custom_type, "heartbeat_prompt");
        assert!(message.display);
        assert_eq!(message.timestamp, 1_000);
        // The header sanitizes its schedule value; the prompt rides as
        // the body (TS `createHeartbeatPromptMessage`).
        assert_eq!(
            message.content,
            UserContent::Text("[heartbeat: every 10m run#0]\n\ncheck the mission".to_string())
        );
        let details = message.details.unwrap();
        assert_eq!(details["jobId"], "job-1");
        assert_eq!(details["schedule"], "every 10m");
        assert_eq!(details["status"], "active");
        assert_eq!(details["runCount"], 0);
        assert_eq!(details["nextRunAt"], "2026-09-22T00:10:00.000Z");
        // An undefined lastRunAt is omitted, not null (TS JSON.stringify
        // drops undefined fields; a first fire carries no lastRunAt).
        assert!(details.get("lastRunAt").is_none());
        // A schedule with header delimiters collapses to spaces.
        let delimited = crate::cron::AgentCronJob {
            schedule: crate::cron::AgentCronSchedule {
                kind: crate::cron::ScheduleKind::Cron,
                expression: "0 0,12:every[day]".to_string(),
                interval_ms: None,
            },
            ..job.clone()
        };
        let message = create_heartbeat_prompt_message(&delimited, 2_000);
        assert!(matches!(message.content, UserContent::Text(text)
                if text.starts_with("[heartbeat: 0 0 12 every day run#0]")));
        // A repeat fire carries the previous run's lastRunAt.
        let repeat = crate::cron::AgentCronJob {
            last_run_at: Some("2026-09-22T00:10:00.000Z".to_string()),
            run_count: 1,
            ..job
        };
        let message = create_heartbeat_prompt_message(&repeat, 2_000);
        assert!(matches!(message.content, UserContent::Text(text)
                if text.starts_with("[heartbeat: every 10m run#1]")));
        let details = message.details.unwrap();
        assert_eq!(details["runCount"], 1);
        assert_eq!(details["lastRunAt"], "2026-09-22T00:10:00.000Z");
    }

    #[test]
    fn async_bash_completion_message_matches_the_ts_shape() {
        // TS `createAsyncBashCompletionMessage`: the custom type, the
        // `[bash-done pid:N exit:M]` header with the JSON-encoded
        // command, display, and the `{pid, command, exitCode}` details.
        let bash = |pid, command: &str, exit_code| JobSettled::Bash {
            pid,
            command: command.to_owned(),
            exit_code,
        };
        let message =
            create_job_settled_message(&bash(4321, "sleep 12; echo RW_WAKE_DONE", 0), 1_000);
        assert_eq!(message.custom_type, "async_bash_completion");
        assert!(message.display);
        assert_eq!(message.timestamp, 1_000);
        assert_eq!(
            message.content,
            UserContent::Text(
                "[bash-done pid:4321 exit:0]\n\nCommand: \"sleep 12; echo RW_WAKE_DONE\""
                    .to_string()
            )
        );
        let details = message.details.unwrap();
        assert_eq!(details["pid"], 4321);
        assert_eq!(details["command"], "sleep 12; echo RW_WAKE_DONE");
        assert_eq!(details["exitCode"], 0);
        // A nonzero exit and embedded quotes round the same shape.
        let message = create_job_settled_message(&bash(11, "echo \"done\" && exit 2", 2), 2_000);
        assert_eq!(message.timestamp, 2_000);
        assert!(matches!(message.content, UserContent::Text(text)
            if text.starts_with("[bash-done pid:11 exit:2]\n\nCommand: \"echo \\\"done\\\" && exit 2\"")));
        let details = message.details.unwrap();
        assert_eq!(details["exitCode"], 2);
    }

    #[test]
    fn a_settled_cell_row_carries_its_report_and_output() {
        let settled = JobSettled::Cell {
            job: eukhe_types::job::JobId::new("cell-1").expect("id"),
            status: eukhe_types::job::CellStatus::Ok,
            output: "slept\n42".to_owned(),
        };
        let message = create_job_settled_message(&settled, 3_000);
        assert_eq!(message.custom_type, JOB_SETTLED_CUSTOM_TYPE);
        assert_eq!(
            message.content,
            UserContent::Text("[job-settled job:cell-1 status:ok]\n\nslept\n42".to_owned())
        );
        assert_eq!(
            message.details,
            Some(serde_json::json!({ "job": "cell-1", "status": "ok" }))
        );
    }

    #[test]
    fn bash_execution_becomes_user_text() {
        let bash = AgentMessage::BashExecution(eukhe_types::session::BashExecutionMessage {
            command: "cargo test".to_string(),
            output: "ok".to_string(),
            exit_code: Some(0),
            cancelled: false,
            omitted: None,
            artifact: None,
            timestamp: 0,
            exclude_from_context: None,
        });
        let converted = convert_to_llm(std::slice::from_ref(&bash));
        match &converted[0] {
            AgentMessage::User(user) => {
                assert!(user.content.text().starts_with("Ran `cargo test`"));
                assert!(user.content.text().contains("```"));
            }
            _ => panic!("expected user"),
        }
        // Excluded executions drop out entirely.
        let excluded = AgentMessage::BashExecution(eukhe_types::session::BashExecutionMessage {
            exclude_from_context: Some(true),
            command: "secret".to_string(),
            output: String::new(),
            exit_code: None,
            cancelled: false,
            omitted: None,
            artifact: None,
            timestamp: 0,
        });
        assert!(convert_to_llm(std::slice::from_ref(&excluded)).is_empty());
    }
}
