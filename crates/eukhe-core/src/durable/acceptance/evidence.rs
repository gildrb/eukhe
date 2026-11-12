//! The evidence of an acceptance check, gathered by the harness itself:
//! the check's command run in the session cwd, the protected files hashed
//! again, the judge asked in a request of its own. The worker's words (its
//! final answer, its claim) never enter: a judge reads the condition its
//! owner wrote and what the harness observed, nothing else. The verdict of
//! each piece of evidence is the compiled core's
//! (`eukhe_bend::rules::verify`).

use std::path::{Path, PathBuf};
use std::sync::Arc;

use eukhe_ai::models::{Models, ModelsSimpleStreamOptions};
use eukhe_ai::types::SimpleStreamOptions;
use eukhe_bend::rules::verify::{self, Answer, Evidence, Verdict};
use eukhe_chord::context::{await_with_context, Context};
use eukhe_chord::json::{from_json, JsonValue};
use eukhe_durable::harness::agent::AGENT_DOC;
use eukhe_durable::harness::types::AgentState;
use eukhe_durable::harness::Conversation;
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{ConversationId, DocumentReaderExt};
use eukhe_types::acceptance::{AcceptanceCheck, CheckResult, CheckSpec, ProtectedFile};
use eukhe_types::pi_ai::{
    AssistantContentBlock, Context as PiContext, Message, StopReason, UserContent, UserMessage,
};
use futures::future::BoxFuture;
use futures::FutureExt;
use sha2::{Digest, Sha256};

use super::docs::verdict_of;
use super::workspace::{user_messages, workspace_files};
use crate::autonomous::{now_millis, ChildProcessResult, GateCommandRunner};
use crate::durable::children::children_verdicts;
use crate::durable::HarnessCell;

/// The time limit of a check's command when its owner set none.
pub(crate) const DEFAULT_CHECK_TIMEOUT_MS: u64 = 600_000;
/// The most characters of evidence one check keeps.
const MAX_EVIDENCE_CHARS: usize = 6000;
/// The most characters of evidence one judge request carries.
const MAX_JUDGE_EVIDENCE_CHARS: usize = 60_000;
/// The most characters of one user message the intent judge reads.
const MAX_USER_MESSAGE_CHARS: usize = 8000;
/// The most characters of the workspace's files the intent judge reads.
const MAX_FILES_CHARS: usize = 24_000;

/// The judge's system prompt for a condition: it decides from the evidence
/// alone.
const JUDGE_SYSTEM_PROMPT: &str = "You are an independent acceptance judge. You did not do the work, and you never see the worker's own account of it. Decide from the EVIDENCE alone whether the CONDITION holds. The harness gathered the evidence itself; the worker did not write it. If the evidence does not show that the condition holds, the answer is FAIL. Reply with the single word PASS or FAIL on the first line, then one short paragraph naming the evidence that decided it.";

/// The judge's system prompt for the task's intent: it reads the user's
/// own messages, decides what they ask for now, and decides from the
/// evidence alone whether the final state meets it.
const INTENT_SYSTEM_PROMPT: &str = "You are an independent acceptance judge. You did not do the work, and you never see the worker's own account of it. The USER MESSAGES are everything the user wrote in this conversation, oldest first. First decide what the conversation asks for now: a later message that adds a requirement extends the task; a later message that drops or changes a requirement removes or replaces it; a side question (a message that asks for information or an explanation and changes nothing in the task) adds no requirement and does not end the task; a request that is only for an answer in chat is met by the reply, which you do not see, so it puts no requirement on the final state. Then decide from the EVIDENCE alone whether the final state meets every current requirement. The harness gathered the evidence itself; the worker did not write it. If the evidence does not show a current requirement met, the answer is FAIL. Reply with the single word PASS or FAIL on the first line, then list the current requirements, each with the evidence that decided it.";

/// What a judge decides.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum JudgeQuestion {
    /// Whether the condition the task's owner wrote holds.
    Condition(String),
    /// Whether the final state meets what the user's messages (oldest
    /// first) ask for now.
    Intent(Vec<String>),
}

/// What a judge is asked.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JudgeRequest {
    /// The conversation whose task is judged.
    pub conversation_id: ConversationId,
    /// What the judge decides.
    pub question: JudgeQuestion,
    /// What the harness observed.
    pub evidence: String,
    /// The judge's model (`provider/id`); the session's when `None`.
    pub model: Option<String>,
}

/// What a judge answered.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum JudgeReply {
    /// The judge's reply text.
    Text(String),
    /// No reply: the request failed, was refused, or no model is set.
    Unavailable(String),
    /// The request was cancelled.
    Stopped,
}

/// Asks an independent judge. The product implementation is one model
/// request with no tools and no transcript: the judge shares no context
/// with the worker. Implementations always resolve; a failure is
/// [`JudgeReply::Unavailable`], which the compiled core grades as a broken
/// check, never as a pass.
pub trait Judge: Send + Sync {
    /// Ask whether `request.condition` holds on `request.evidence`.
    fn judge(&self, request: JudgeRequest, cx: &Context) -> BoxFuture<'_, JudgeReply>;
}

/// The product judge: one request to the check's model, else the
/// conversation's.
pub(crate) struct ModelJudge {
    pub(crate) harness: HarnessCell,
    pub(crate) models: Models,
}

impl Judge for ModelJudge {
    fn judge(&self, request: JudgeRequest, cx: &Context) -> BoxFuture<'_, JudgeReply> {
        let cx = cx.clone();
        async move {
            let selector = match request.model.clone() {
                Some(selector) => Some(selector),
                None => match self.session_model(request.conversation_id, &cx).await {
                    Ok(selector) => selector,
                    Err(error) => return JudgeReply::Unavailable(error.to_string()),
                },
            };
            let Some(selector) = selector else {
                return JudgeReply::Unavailable(
                    "the judge has no model: the session has none and the check names none"
                        .to_owned(),
                );
            };
            let Some(model) = selector
                .split_once('/')
                .and_then(|(provider, id)| self.models.get_model(provider, id))
            else {
                return JudgeReply::Unavailable(format!(
                    "the judge's model {selector:?} is not available"
                ));
            };
            let system_prompt = match request.question {
                JudgeQuestion::Condition(_) => JUDGE_SYSTEM_PROMPT,
                JudgeQuestion::Intent(_) => INTENT_SYSTEM_PROMPT,
            };
            let context = PiContext {
                system_prompt: Some(system_prompt.to_owned()),
                messages: vec![Message::User(UserMessage {
                    content: UserContent::Text(judge_prompt(&request)),
                    timestamp: now_millis(),
                })],
                tools: None,
            };
            let mut options: ModelsSimpleStreamOptions = SimpleStreamOptions::default().into();
            options.options.stream.request.signal = cx.abort_signal();
            let reply = self.models.complete_simple(&model, context, options).await;
            match reply.stop_reason {
                StopReason::Stop | StopReason::Length | StopReason::ToolUse => JudgeReply::Text(
                    reply
                        .content
                        .iter()
                        .filter_map(|block| match block {
                            AssistantContentBlock::Text(text) => Some(text.text.as_str()),
                            AssistantContentBlock::Thinking(_)
                            | AssistantContentBlock::ToolCall(_) => None,
                        })
                        .collect(),
                ),
                StopReason::Aborted => JudgeReply::Stopped,
                StopReason::Error => JudgeReply::Unavailable(
                    reply
                        .error_message
                        .unwrap_or_else(|| "the judge's request failed".to_owned()),
                ),
                StopReason::Pending | StopReason::Deferred => {
                    JudgeReply::Unavailable("the judge's request did not complete".to_owned())
                }
            }
        }
        .boxed()
    }
}

impl ModelJudge {
    /// The conversation's chat model (`provider/id`).
    async fn session_model(
        &self,
        conversation_id: ConversationId,
        cx: &Context,
    ) -> SessionResult<Option<String>> {
        let harness = self.harness.require()?;
        let agent: Option<AgentState> =
            match harness.snapshot(&AGENT_DOC, conversation_id, cx).await? {
                Some(value) => Some(from_json(&JsonValue::Object(value))?),
                None => None,
            };
        Ok(agent
            .and_then(|agent| agent.model)
            .map(|model| format!("{}/{}", model.provider, model.model_id)))
    }
}

/// The judge's user message: the condition or the user's messages, then
/// the evidence.
pub(crate) fn judge_prompt(request: &JudgeRequest) -> String {
    let question = match &request.question {
        JudgeQuestion::Condition(condition) => {
            format!("<condition>\n{condition}\n</condition>")
        }
        JudgeQuestion::Intent(messages) => {
            let messages: Vec<String> = messages
                .iter()
                .enumerate()
                .map(|(index, text)| format!("<message n=\"{}\">\n{text}\n</message>", index + 1))
                .collect();
            format!("<user_messages>\n{}\n</user_messages>", messages.join("\n"))
        }
    };
    format!(
        "{question}\n\n<evidence>\n{}\n</evidence>",
        request.evidence
    )
}

/// The answer a judge's reply gives: its first word, PASS or FAIL in any
/// case; any other reply is unreadable.
pub(crate) fn read_answer(reply: &JudgeReply) -> Answer {
    match reply {
        JudgeReply::Unavailable(_) => Answer::Unavailable,
        JudgeReply::Stopped => Answer::Stopped,
        JudgeReply::Text(text) => {
            let word: String = text
                .trim_start()
                .chars()
                .take_while(char::is_ascii_alphabetic)
                .collect();
            match word.to_ascii_uppercase().as_str() {
                "PASS" => Answer::Yes,
                "FAIL" => Answer::No,
                _ => Answer::Unreadable,
            }
        }
    }
}

/// The sha256 of the file at `path` under `cwd`; `None` when it cannot be
/// read (no such file).
fn hash_file(cwd: &Path, path: &str) -> Option<String> {
    let bytes = std::fs::read(cwd.join(path)).ok()?;
    let mut hasher = Sha256::new();
    hasher.update(&bytes);
    Some(format!("{:x}", hasher.finalize()))
}

/// The protected files of `paths` as they are now under `cwd`.
pub(crate) fn protect(cwd: &Path, paths: &[String]) -> Vec<ProtectedFile> {
    paths
        .iter()
        .map(|path| ProtectedFile {
            path: path.clone(),
            sha256: hash_file(cwd, path),
        })
        .collect()
}

/// The first protected file that is no longer as its owner left it.
fn changed<'a>(cwd: &Path, protected: &'a [ProtectedFile]) -> Option<&'a ProtectedFile> {
    protected
        .iter()
        .find(|file| hash_file(cwd, &file.path) != file.sha256)
}

fn cut(text: &str, max: usize) -> String {
    if text.chars().count() <= max {
        return text.to_owned();
    }
    let prefix: String = text.chars().take(max).collect();
    format!("{prefix}\n... [truncated]")
}

/// The output of a finished command: stdout, then stderr.
fn output_of(result: &ChildProcessResult) -> String {
    [result.stdout.as_str(), result.stderr.as_str()]
        .into_iter()
        .filter(|text| !text.is_empty())
        .collect::<Vec<_>>()
        .join("\n")
        .trim()
        .to_owned()
}

/// What the harness saw of a command, how it ended in one line, and its
/// output.
struct Ran {
    evidence: Evidence,
    summary: String,
    output: String,
}

/// What gathers the evidence of one conversation's checks.
#[derive(Clone)]
pub(crate) struct Gatherer {
    /// The session's Harness: the verdicts of the children a judge reads.
    pub(crate) harness: HarnessCell,
    /// Runs the checks' commands in the session cwd.
    pub(crate) runner: Arc<dyn GateCommandRunner>,
    pub(crate) judge: Arc<dyn Judge>,
    pub(crate) cwd: PathBuf,
}

impl Gatherer {
    /// Run `command`.
    ///
    /// # Errors
    ///
    /// `cx` was cancelled (an abort, a closing session): nothing is
    /// learned and nothing recorded, so the check runs again later.
    async fn run(
        &self,
        command: &str,
        timeout_ms: Option<u64>,
        cx: &Context,
    ) -> SessionResult<Ran> {
        let timeout_ms = timeout_ms.unwrap_or(DEFAULT_CHECK_TIMEOUT_MS);
        let result = await_with_context(self.runner.run_gate(command, timeout_ms), cx)
            .await
            .map_err(SessionError::Aborted)?;
        Ok(match result {
            Err(error) => Ran {
                evidence: Evidence::SpawnFailed,
                summary: format!("could not start: {error}"),
                output: String::new(),
            },
            Ok(result) if result.timed_out => Ran {
                evidence: Evidence::TimedOut,
                summary: format!("timed out after {timeout_ms} ms"),
                output: output_of(&result),
            },
            Ok(result) => match (result.error.as_ref(), result.status) {
                (Some(error), _) => Ran {
                    evidence: Evidence::SpawnFailed,
                    summary: format!("could not run: {error}"),
                    output: output_of(&result),
                },
                (None, Some(code)) => match u64::try_from(code) {
                    Ok(code) => Ran {
                        evidence: Evidence::Exited(code),
                        summary: format!("exited with code {code}"),
                        output: output_of(&result),
                    },
                    // A negative code is no exit status a command returns.
                    Err(_) => Ran {
                        evidence: Evidence::NoStatus,
                        summary: format!("ended with status {code}"),
                        output: output_of(&result),
                    },
                },
                (None, None) => Ran {
                    evidence: Evidence::NoStatus,
                    summary: "killed by a signal".to_owned(),
                    output: output_of(&result),
                },
            },
        })
    }

    /// Gather the evidence of `check` on the state `at` and grade it. `round`
    /// holds the results of the round's earlier checks: a judge reads them.
    ///
    /// # Errors
    ///
    /// `cx` was cancelled while the evidence was gathered (nothing is
    /// recorded: the check runs again later), or a compiled-core failure
    /// (an inconsistent build).
    pub(crate) async fn check(
        &self,
        conversation: &Conversation,
        check: &AcceptanceCheck,
        round: &[AcceptanceCheck],
        at: u64,
        cx: &Context,
    ) -> SessionResult<(Verdict, CheckResult)> {
        let conversation_id = conversation.id();
        let (verdict, summary, evidence) = match &check.spec {
            CheckSpec::Command {
                command,
                expect,
                timeout_ms,
                ..
            } => {
                let ran = self.run(command, *timeout_ms, cx).await?;
                let tampered = changed(&self.cwd, &check.protected);
                let verdict =
                    verify::grade_command(u64::from(*expect), tampered.is_none(), ran.evidence)
                        .map_err(SessionError::other)?;
                let summary = match tampered {
                    Some(file) => format!("protected file changed: {}", file.path),
                    None => ran.summary,
                };
                (verdict, summary, ran.output)
            }
            CheckSpec::Until {
                command,
                timeout_ms,
            } => {
                let ran = self.run(command, *timeout_ms, cx).await?;
                (
                    verify::grade_until(ran.evidence).map_err(SessionError::other)?,
                    ran.summary,
                    ran.output,
                )
            }
            CheckSpec::Judge {
                condition,
                evidence,
                model,
            } => {
                let observed = self
                    .observe(conversation_id, evidence, round, at, false, cx)
                    .await?;
                self.ask(
                    JudgeRequest {
                        conversation_id,
                        question: JudgeQuestion::Condition(condition.clone()),
                        evidence: observed,
                        model: model.clone(),
                    },
                    cx,
                )
                .await?
            }
            CheckSpec::Intent { model } => {
                let messages = user_messages(conversation, MAX_USER_MESSAGE_CHARS, cx).await?;
                let observed = self
                    .observe(conversation_id, &[], round, at, true, cx)
                    .await?;
                self.ask(
                    JudgeRequest {
                        conversation_id,
                        question: JudgeQuestion::Intent(messages),
                        evidence: observed,
                        model: model.clone(),
                    },
                    cx,
                )
                .await?
            }
        };
        Ok((
            verdict,
            CheckResult {
                verdict: verdict_of(verdict),
                at,
                summary,
                evidence: cut(&evidence, MAX_EVIDENCE_CHARS),
                judged_at: now_millis(),
            },
        ))
    }

    /// Ask the judge `request`: the verdict of its answer, how it ended in
    /// one line, and its reply.
    ///
    /// # Errors
    ///
    /// `cx` was cancelled (nothing is learned), or a compiled-core
    /// failure.
    async fn ask(
        &self,
        request: JudgeRequest,
        cx: &Context,
    ) -> SessionResult<(Verdict, String, String)> {
        let reply = self.judge.judge(request, cx).await;
        // A cancelled run cancels its judge: nothing is learned.
        if reply == JudgeReply::Stopped {
            if let Some(reason) = cx.abort_signal().and_then(|signal| signal.reason()) {
                return Err(SessionError::Aborted(reason));
            }
        }
        let answer = read_answer(&reply);
        let (summary, text) = match (&reply, answer) {
            (JudgeReply::Text(text), Answer::Yes) => {
                ("the judge answered PASS".to_owned(), text.clone())
            }
            (JudgeReply::Text(text), Answer::No) => {
                ("the judge answered FAIL".to_owned(), text.clone())
            }
            (JudgeReply::Text(text), _) => (
                "the judge's reply starts with neither PASS nor FAIL".to_owned(),
                text.clone(),
            ),
            (JudgeReply::Unavailable(why), _) => {
                (format!("the judge gave no answer: {why}"), String::new())
            }
            (JudgeReply::Stopped, _) => ("the judge was cancelled".to_owned(), String::new()),
        };
        Ok((
            verify::grade_judge(answer).map_err(SessionError::other)?,
            summary,
            text,
        ))
    }

    /// What a judge reads: the results the round's other checks got on the
    /// state `at`, the output of its own evidence commands, and with
    /// neither (always for the intent judge, `workspace`) the workspace:
    /// git status and diff, and the files git does not track yet (every
    /// file outside git). The verdicts of the conversation's children that
    /// carry checks, as their harness recorded them, come first.
    async fn observe(
        &self,
        conversation_id: ConversationId,
        commands: &[String],
        round: &[AcceptanceCheck],
        at: u64,
        workspace: bool,
        cx: &Context,
    ) -> SessionResult<String> {
        let mut parts = Vec::new();
        let children = children_verdicts(&self.harness.require()?, conversation_id, cx).await?;
        if !children.is_empty() {
            parts.push(format!(
                "Subagents with acceptance checks, as the harness verified them on each child's final state:\n{}",
                children.join("\n")
            ));
        }
        let observed_before = parts.len();
        for (index, other) in round.iter().enumerate() {
            let Some(result) = other.result.as_ref().filter(|result| result.at == at) else {
                continue;
            };
            let command = match &other.spec {
                CheckSpec::Command { command, .. } | CheckSpec::Until { command, .. } => command,
                // A judge never reads another judge's verdict.
                CheckSpec::Judge { .. } | CheckSpec::Intent { .. } => continue,
            };
            parts.push(format!(
                "Acceptance check {} ran `{command}`: {}\n{}",
                index + 1,
                result.summary,
                result.evidence
            ));
        }
        for command in commands {
            let ran = self.run(command, None, cx).await?;
            parts.push(format!("`{command}`: {}\n{}", ran.summary, ran.output));
        }
        if workspace || parts.len() == observed_before {
            let snapshot = self.runner.capture_snapshot().await;
            if let Some(snapshot) = &snapshot {
                parts.push(format!(
                    "`git status --porcelain`:\n{}\n\n`git diff HEAD`:\n{}",
                    snapshot.status.replace('\0', "\n"),
                    snapshot.diff
                ));
            }
            match workspace_files(&self.cwd, MAX_FILES_CHARS).await {
                Some(files) => parts.push(files),
                None if snapshot.is_none() => parts.push(
                    "The harness could observe nothing: the check names no evidence command and the workspace could not be read."
                        .to_owned(),
                ),
                None => {}
            }
        }
        Ok(cut(&parts.join("\n\n"), MAX_JUDGE_EVIDENCE_CHARS))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The judge's answer is its reply's first word; anything else is
    /// unreadable, never a pass.
    #[test]
    fn a_judges_answer_is_its_first_word() {
        let text = |reply: &str| read_answer(&JudgeReply::Text(reply.to_owned()));
        assert_eq!(
            [
                text("PASS\nThe tests ran green."),
                text("  pass."),
                text("FAIL: the output shows 2 failures"),
                text("Fail"),
                text("PASSING is not shown"),
                text("The condition holds. PASS"),
                text(""),
                read_answer(&JudgeReply::Unavailable("no model".to_owned())),
                read_answer(&JudgeReply::Stopped),
            ],
            [
                Answer::Yes,
                Answer::Yes,
                Answer::No,
                Answer::No,
                Answer::Unreadable,
                Answer::Unreadable,
                Answer::Unreadable,
                Answer::Unavailable,
                Answer::Stopped,
            ]
        );
    }
}
