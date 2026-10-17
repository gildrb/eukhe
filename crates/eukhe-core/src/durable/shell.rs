//! `eukhe.shell`: the `bash` tool (`bash@1`, docs/tools.md S7). It runs
//! a script in process ([`eukhe_shell::Shell`]) in the agent's working
//! directory. A step whose effect is in the auto set (the `shell.autoEffects`
//! setting, default `read`) runs unasked; every other step runs only when
//! the user approves it through the session's [`ShellApprovalSink`] (the
//! daemon asks the attached client). A denial, or no answer, stops the
//! script at that step.
//!
//! The tool obeys the S2 limits. Its output streams through one
//! [`BoundedOutput`] under the call's [`Truncation`](eukhe_durable::harness::Truncation):
//! kept within the cap, every dropped byte counted in the `output_bounded`
//! diagnostic, all of it kept under the opt-out. The call blocks at most
//! the blocking budget ([`HostDeps::blocking_budget`]): past it the call
//! settles `detached` with the output so far and the script runs on as a
//! [`Job`] of the session's [`JobTable`](super::jobs::JobTable). Its end
//! settles the job and reaches the session through
//! [`HostDeps::job_settled`]; the job's kill stops the script and every
//! process it started. External steps get the environment of a local
//! kernel ([`local_env`] over [`session_env`]).

#[cfg(test)]
mod tests;

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::{Arc, Mutex, MutexGuard, OnceLock, PoisonError};
use std::time::Duration;

use eukhe_chord::context::Context;
use eukhe_chord::json::JsonValue;
use eukhe_durable::env::Utf8Decoder;
use eukhe_durable::harness::define::{define_extension, define_tool};
use eukhe_durable::harness::types::{
    Extension, ToolDiagnostic, ToolDiagnosticSeverity, ToolExecutionApi, ToolExecutionMode,
    ToolExecutionResult, ToolRegistration, ToolReplay,
};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_shell::{
    Answer, Approval, Approver, Ask, AutoSet, End, Ran, Refusal, Shell, Sink, Stream,
};
use eukhe_types::job::{CellStatus, JobId, JobSettled};
use eukhe_types::pi_ai::{JsonValue as PiJsonValue, TextContent, UserContentBlock};
use eukhe_types::shell::{ShellApprovalRequest, ShellEffect, ShellVerdict};

use super::bounded_output::BoundedOutput;
use super::deps::ShellApprovalSink;
use super::jobs::{self, Job, JobEvent, JobKind, JobSpec, Wait};
use super::rlm::{aborted, call_aborted, session_env, with_diagnostics};
use super::HostDeps;
use crate::kernel::manager::local_env;

/// The extension's name.
pub const SHELL_EXTENSION: &str = "eukhe.shell";

/// The tool's name.
const NAME: &str = "bash";

/// The tool's durable identity, in each result's details.
const VERSION: &str = "bash@1";

const DESCRIPTION: &str = "Run a bash script in the working directory. Steps are simple commands \
joined by `;`, newlines, `&&`, `||`, `|`, with redirections; the commands of a pipeline run \
together. Read-only steps run at once; a step that writes files, runs another program, or uses \
the network runs only after the user approves it, and a denial stops the script there. Common \
commands (cat, ls, head, tail, wc, echo, pwd, mkdir, rm, rmdir, touch, cp, mv, grep) run in \
process; a script with control flow, functions, subshells or command substitution runs whole in \
bash as one step that needs approval. The result lists every step that ran with its exit status; \
the output is bounded. A script that outlives the blocking budget goes on as a job, and its end \
reaches the session as a [job-settled] message.";

/// Asks through the session's sink; each question's id is the tool
/// call's id and the step.
struct SinkApprover {
    sink: Option<ShellApprovalSink>,
    call: String,
}

impl Approver for SinkApprover {
    #[tracing::instrument(level = "debug", skip_all, fields(step = ask.step))]
    async fn approve(&self, ask: Ask) -> Answer {
        let Some(sink) = &self.sink else {
            return Answer::Unanswered;
        };
        let request = ShellApprovalRequest {
            request_id: format!("{}:{}", self.call, ask.step),
            step: ask.step,
            command: ask.command,
            effect: ask.effect,
        };
        match sink(request).await {
            Some(ShellVerdict::Approve) => Answer::Approve,
            Some(ShellVerdict::Deny) => Answer::Deny,
            None => Answer::Unanswered,
        }
    }
}

/// The bounded output of one script and its decoders, one per step's
/// stream (a chunk may end inside a character).
struct Shown {
    bounded: BoundedOutput,
    decoders: HashMap<(u64, Stream), Utf8Decoder>,
}

/// The script's model-facing output as it runs: `$ command` when a step
/// begins, its stdout and stderr as they arrive, `[step N exited S]`
/// when it ends with a status other than 0. Once the call detached, the
/// bytes also count on the job, which starts with the bytes written
/// before ([`JobSpec::written`]).
struct Transcript {
    shown: Mutex<Shown>,
    job: OnceLock<Job>,
}

impl Transcript {
    fn new(bounded: BoundedOutput) -> Self {
        Self {
            shown: Mutex::new(Shown {
                bounded,
                decoders: HashMap::new(),
            }),
            job: OnceLock::new(),
        }
    }

    fn shown(&self) -> MutexGuard<'_, Shown> {
        self.shown.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Append `text`; a part starts on its own line.
    fn push(&self, text: &str, part: bool) {
        if text.is_empty() {
            return;
        }
        let mut shown = self.shown();
        let before = shown.bounded.bytes();
        if part {
            shown.bounded.push_part(text);
        } else {
            shown.bounded.push(text);
        }
        let written = shown.bounded.bytes() - before;
        // Read under the lock the job starts under: every byte counts
        // once, in the job's start or here.
        let job = self.job.get().cloned();
        drop(shown);
        if let Some(job) = job {
            job.record(JobEvent::Output(written));
        }
    }

    /// The output so far and its `output_bounded` diagnostic.
    fn projection(&self) -> (String, Option<ToolDiagnostic>) {
        self.shown().bounded.projection()
    }
}

impl Sink for Transcript {
    fn begin(&self, _step: u64, command: &str) {
        self.push(&format!("$ {command}\n"), true);
    }

    fn output(&self, step: u64, stream: Stream, bytes: &[u8]) {
        let text = self
            .shown()
            .decoders
            .entry((step, stream))
            .or_default()
            .decode_chunk(bytes);
        self.push(&text, false);
    }

    fn end(&self, step: u64, status: i32) {
        let rest: String = {
            let mut shown = self.shown();
            [Stream::Stdout, Stream::Stderr]
                .into_iter()
                .filter_map(|stream| shown.decoders.remove(&(step, stream)))
                .map(|mut decoder| decoder.finish())
                .collect()
        };
        self.push(&rest, false);
        if status != 0 {
            self.push(&format!("[step {step} exited {status}]\n"), true);
        }
    }
}

/// Aborts the script's task when the call stops waiting for it before it
/// detached (the Harness drops an aborted call).
struct AbortUnlessDetached(Option<tokio::task::AbortHandle>);

impl Drop for AbortUnlessDetached {
    fn drop(&mut self) {
        if let Some(task) = self.0.take() {
            task.abort();
        }
    }
}

/// The shell extension of one session.
#[must_use]
pub fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    let deps = Arc::clone(deps);
    let schema = super::tool_contract::parameters(
        1,
        [(
            "script",
            eukhe_ai::typebox::Type::string_with(
                eukhe_ai::typebox::Options::new().set("description", "The bash script to run"),
            ),
        )],
    );
    let mut registration = ToolRegistration::new(
        NAME,
        DESCRIPTION,
        schema,
        move |args: PiJsonValue, api: Arc<dyn ToolExecutionApi>, cx: Context| {
            let deps = Arc::clone(&deps);
            async move { execute(&deps, args, api, &cx).await }
        },
    );
    // A step may have written before a crash: never replay.
    registration.execution_mode = Some(ToolExecutionMode::Sequential);
    registration.replay = Some(ToolReplay::Unsafe);
    define_extension(Extension {
        tools: vec![define_tool(registration)],
        ..Extension::named(SHELL_EXTENSION)
    })
}

/// The auto set of the `shell.autoEffects` setting. The setting admits
/// only effect names; a name it holds that names no effect is skipped.
fn auto_set(deps: &HostDeps) -> AutoSet {
    AutoSet::new(
        deps.settings
            .manager()
            .get_shell_auto_effects()
            .iter()
            .filter_map(|name| match name.as_str() {
                "read" => Some(ShellEffect::Read),
                "write" => Some(ShellEffect::Write),
                "exec" => Some(ShellEffect::Exec),
                "net" => Some(ShellEffect::Net),
                unknown => {
                    tracing::warn!(unknown, "shell.autoEffects holds an unknown effect");
                    None
                }
            }),
    )
}

#[tracing::instrument(level = "debug", skip_all, fields(task = %api.task_id()))]
async fn execute(
    deps: &HostDeps,
    args: PiJsonValue,
    api: Arc<dyn ToolExecutionApi>,
    cx: &Context,
) -> SessionResult<ToolExecutionResult> {
    let Some(script) = args.get("script").and_then(PiJsonValue::as_str) else {
        return Err(SessionError::error("bash needs a `script` string"));
    };
    let budget = deps.blocking_budget();
    let deadline = tokio::time::Instant::now() + budget;
    let cwd = api
        .agent(cx)
        .await?
        .cwd
        .clone()
        .map_or_else(|| deps.cwd.clone(), PathBuf::from);
    let approver = SinkApprover {
        sink: deps.shell_approval.clone(),
        call: api.task_id().to_string(),
    };
    let transcript = Arc::new(Transcript::new(BoundedOutput::in_session(
        deps.storage_dir.as_deref(),
        &api.task_id().to_string(),
        api.truncation(),
    )));
    let mut running = {
        let (auto, env) = (auto_set(deps), local_env(&session_env(deps)));
        let (script, transcript) = (script.to_owned(), Arc::clone(&transcript));
        tokio::spawn(async move {
            Shell::new(cwd, env, "bash")
                .run(&script, &auto, &approver, &*transcript)
                .await
        })
    };
    let mut abort_unless_detached = AbortUnlessDetached(Some(running.abort_handle()));
    let waited = tokio::select! {
        waited = jobs::wait_until(deadline, &mut running) => waited,
        () = call_aborted(cx) => {
            return Err(aborted(cx).unwrap_or_else(|| SessionError::error("aborted")));
        }
    };
    let ran = match waited {
        Wait::Settled(Ok(ran)) => ran,
        Wait::Settled(Err(error)) => {
            return Err(SessionError::error(format!(
                "the script's task failed: {error}"
            )))
        }
        Wait::Detached => {
            abort_unless_detached.0 = None;
            let id = JobId::new(format!("shell-{}", uuid::Uuid::new_v4().simple()))
                .map_err(|error| SessionError::error(error.to_string()))?;
            let job = {
                let shown = transcript.shown();
                let job = deps.jobs.start(JobSpec {
                    id: id.clone(),
                    kind: JobKind::Shell,
                    label: script.to_owned(),
                    truncation: api.truncation(),
                    written: shown.bounded.bytes(),
                    kill: {
                        let task = running.abort_handle();
                        Box::new(move |_| task.abort())
                    },
                });
                let _ = transcript.job.set(job.clone());
                job
            };
            let (partial, bounded) = transcript.projection();
            let sink = deps.job_settled.clone();
            let settled_id = id.clone();
            tokio::spawn(async move {
                let (status, event) = match running.await {
                    Ok(ran) => {
                        let (status, code) = settle(&ran, &transcript);
                        (status, JobEvent::Exited(i64::from(code)))
                    }
                    Err(error) if error.is_cancelled() => {
                        transcript.push("[killed: the job's kill stopped the script]\n", true);
                        (CellStatus::Killed, JobEvent::Killed)
                    }
                    Err(error) => {
                        transcript.push(&format!("[the script's task failed: {error}]\n"), true);
                        (CellStatus::Error, JobEvent::Exited(1))
                    }
                };
                let (text, bounded) = transcript.projection();
                let output = with_diagnostics(text, bounded.as_slice());
                tracing::debug!(job = %settled_id, status = status.label(), "detached script settled");
                job.record(event);
                if let Some(sink) = sink {
                    sink(JobSettled::Shell {
                        job: settled_id,
                        status,
                        output,
                    });
                }
            });
            return Ok(detached_result(&id, budget, partial, bounded));
        }
    };
    let refused = matches!(ran.end, End::Refused { .. });
    settle(&ran, &transcript);
    let (text, bounded) = transcript.projection();
    let steps: Vec<serde_json::Value> = ran
        .steps
        .iter()
        .map(|step| {
            serde_json::json!({
                "step": step.step,
                "command": step.command,
                "effect": step.effect.as_str(),
                "approval": match step.approval {
                    Approval::Auto => "auto",
                    Approval::Approved => "approved",
                },
                "status": step.status,
            })
        })
        .collect();
    let end = match &ran.end {
        End::Finished { status } => serde_json::json!({ "kind": "finished", "status": status }),
        End::Exited { status } => serde_json::json!({ "kind": "exited", "status": status }),
        End::Refused {
            step,
            command,
            effect,
            refusal,
        } => serde_json::json!({
            "kind": "refused",
            "step": step,
            "command": command,
            "effect": effect.as_str(),
            "refusal": match refusal {
                Refusal::Denied => "denied",
                Refusal::Unanswered => "unanswered",
            },
        }),
    };
    let details = serde_json::json!({ "version": VERSION, "steps": steps, "end": end });
    Ok(ToolExecutionResult {
        output: Some(vec![UserContentBlock::Text(TextContent::new(text))]),
        is_error: Some(refused),
        details: Some(JsonValue::from(details)),
        diagnostics: bounded.map(|diagnostic| vec![diagnostic]),
        ..ToolExecutionResult::default()
    })
}

/// Write how the script ended to its transcript: its job status and exit
/// code (a refused step: 1).
fn settle(ran: &Ran, transcript: &Transcript) -> (CellStatus, i32) {
    match &ran.end {
        End::Finished { status } | End::Exited { status } => (
            if *status == 0 {
                CellStatus::Ok
            } else {
                CellStatus::Error
            },
            *status,
        ),
        End::Refused {
            step,
            command,
            effect,
            refusal,
        } => {
            let why = match refusal {
                Refusal::Denied => "the user denied it",
                Refusal::Unanswered => "no one answered",
            };
            transcript.push(
                &format!(
                    "[stopped at step {step} ({}): `{command}` did not run: {why}; later steps did not run]\n",
                    effect.as_str()
                ),
                true,
            );
            (CellStatus::Error, 1)
        }
    }
}

/// The call of a script that outlived the blocking budget: the output so
/// far, and the job it became.
fn detached_result(
    job: &JobId,
    budget: Duration,
    partial: String,
    bounded: Option<ToolDiagnostic>,
) -> ToolExecutionResult {
    let budget_ms = u64::try_from(budget.as_millis()).unwrap_or(u64::MAX);
    let mut diagnostics: Vec<ToolDiagnostic> = bounded.into_iter().collect();
    diagnostics.push(ToolDiagnostic {
        severity: ToolDiagnosticSeverity::Info,
        code: Some("detached".to_owned()),
        message: format!(
            "The script outlived the {budget_ms} ms blocking budget, so this call settled as job {job}; \
             the script keeps running, and a step that needs approval still asks the user. Its end \
             reaches this session as a [job-settled job:{job}] message with its output, waking the \
             session if idle."
        ),
        omitted: None,
        artifact: None,
        lines: None,
    });
    ToolExecutionResult {
        output: Some(vec![UserContentBlock::Text(TextContent::new(partial))]),
        is_error: Some(false),
        details: Some(JsonValue::from(serde_json::json!({
            "version": VERSION,
            "status": "detached",
            "job": { "id": job.as_str(), "kind": JobKind::Shell.name() },
            "budgetMs": budget_ms,
        }))),
        diagnostics: Some(diagnostics),
        ..ToolExecutionResult::default()
    }
}
