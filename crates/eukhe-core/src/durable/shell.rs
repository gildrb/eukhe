//! `eukhe.shell`: the `bash` tool (`bash@1`). It runs
//! a script in process ([`eukhe_shell::Shell`]) in the agent's working
//! directory. Every step runs unasked but one that writes an own path
//! (eukhe's own config and credentials, the session record, a protected
//! file of a check under acceptance), or an irreversible step the editor
//! attached through ACP rejects ([`HostDeps::editor_permission`]): that
//! step and the steps after it do not run, and the model reads why.
//!
//! The tool obeys the S2 limits. Its output streams through one
//! [`BoundedOutput`] under the call's [`Truncation`](eukhe_durable::harness::Truncation):
//! kept within the cap, every dropped byte counted in the `output_bounded`
//! diagnostic, all of it kept under the opt-out. The call blocks at most
//! the blocking budget ([`HostDeps::blocking_budget`]): past it the call
//! settles `detached` with the output so far and the script runs on as a
//! [`Job`] of the session's [`JobTable`](super::jobs::JobTable). Its end
//! settles the job and reaches the session through
//! [`HostDeps::job_settled`]; its output names the workspace paths
//! written between the detach and the end ([`TreeStamp`]), so a check
//! that ran across edits says it judged no single tree state. The job's
//! kill stops the script and every process it started. External steps
//! get [`local_env`] over
//! [`session_env`]: the host environment less every credential name (laws
//! (G3)).
//!
//! A script that is one `git push` or one `git commit` records the ref it
//! moves before it runs ([`git_evidence`]): a restart that cut the call
//! adopts it when that ref holds its commit, and treats it as not run
//! otherwise.

mod git_evidence;
#[cfg(test)]
mod tests;

use std::collections::HashMap;
use std::future::Future;
use std::path::PathBuf;
use std::sync::{Arc, Mutex, MutexGuard, OnceLock, PoisonError};
use std::time::Duration;

use eukhe_chord::context::Context;
use eukhe_chord::json::JsonValue;
use eukhe_durable::env::Utf8Decoder;
use eukhe_durable::harness::define::{define_extension, define_tool};
use eukhe_durable::harness::effects::EffectKind;
use eukhe_durable::harness::types::{
    Extension, ToolDiagnostic, ToolDiagnosticSeverity, ToolExecutionApi, ToolExecutionMode,
    ToolExecutionResult, ToolRegistration, ToolReplay,
};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::ConversationId;
use eukhe_shell::{End, Ran, Shell, Sink, StepRun, Steps, Stream};
use eukhe_types::effects::{EffectClass, RanEffect, RanKind};
use eukhe_types::job::{CellStatus, JobId};
use eukhe_types::pi_ai::{JsonValue as PiJsonValue, TextContent, UserContentBlock};
use eukhe_types::platform::kill_point::kill_point;
use eukhe_types::shell::ShellEffect;

use super::bounded_output::BoundedOutput;
use super::editor_permission::{self, EDITOR_REFUSED};
use super::jobs::{self, Job, JobEvent, JobKind, JobResult, JobSpec, Wait};
use super::rlm::{aborted, call_aborted, session_env, with_diagnostics};
use super::HostDeps;
use crate::child_workspace::{ChildWorkspace, TreeStamp};
use crate::kernel::manager::local_env;

/// Whether `script` names the `git` program: a word `git` or a path
/// ending in `/git`.
fn names_git(script: &str) -> bool {
    script
        .split(|c: char| !(c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '-' | '/')))
        .any(|word| word.rsplit('/').next() == Some("git"))
}

/// What one script does around each step (spec I4, I12): the editor's
/// say before an irreversible step (each question's id is the script's
/// name and the step), and the ledger record of each irreversible step at
/// its own end, before the next step starts (a crash later in the script
/// keeps it recorded). A `bash` call and an autoresearch benchmark run
/// both run their steps through it.
pub(crate) struct CallSteps {
    deps: Arc<HostDeps>,
    conversation: ConversationId,
    /// Unique within the session: each step's question id and ledger key
    /// is `<call>:<step>`.
    call: String,
    /// The tool call that runs the script, named to the editor.
    tool_call: Option<String>,
    recorded: Mutex<Vec<RanEffect>>,
}

impl CallSteps {
    pub(crate) fn new(
        deps: Arc<HostDeps>,
        conversation: ConversationId,
        call: String,
        tool_call: Option<String>,
    ) -> Self {
        Self {
            deps,
            conversation,
            call,
            tool_call,
            recorded: Mutex::new(Vec::new()),
        }
    }

    /// The effects recorded so far, in step order (what the call's notes
    /// list).
    fn recorded(&self) -> Vec<RanEffect> {
        self.recorded
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }
}

impl Steps for CallSteps {
    fn allows(
        &self,
        step: u64,
        command: &str,
        effects: eukhe_types::shell::ShellEffects,
    ) -> impl Future<Output = bool> + Send {
        editor_permission::allows(
            self.deps.editor_permission.clone(),
            format!("{}:{step}", self.call),
            self.tool_call.clone(),
            command.to_owned(),
            EffectClass::of_shell(effects),
        )
    }

    fn ran(&self, ran: &StepRun) -> impl Future<Output = ()> + Send {
        let classes = EffectClass::of_shell(ran.effects);
        let draft = eukhe_bend::rules::irreversible::is_irreversible(&classes).then(|| {
            super::ran_effects::draft(
                &self.deps,
                &format!("{}:{}", self.call, ran.step),
                RanKind::ShellStep,
                ran.command.clone(),
                classes,
            )
        });
        async move {
            if let Some(draft) = draft {
                let recorded =
                    super::ran_effects::record_effects(&self.deps, self.conversation, vec![draft])
                        .await;
                self.recorded
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .extend(recorded);
            }
        }
    }
}

/// The extension's name.
pub const SHELL_EXTENSION: &str = "eukhe.shell";

/// The tool's name; the intent judge reads only this tool's results.
pub(crate) const NAME: &str = "bash";

/// The tool's durable identity, in each result's details; the intent
/// judge reads the runs whose details carry it.
pub(crate) const VERSION: &str = "bash@1";

const DESCRIPTION: &str = "Run a bash script in the cwd. Steps: simple commands joined by `;`, \
newlines, `&&`, `||`, `|`, with redirections. Every step runs at once; a step that writes \
eukhe's own config and credentials, the session record or a check's protected files is refused \
and stops the script. `git` commands that can run repo programs (status, diff, commit, ...) count \
as exec. cat, ls, head, tail, wc, echo, pwd, mkdir, rm, rmdir, touch, cp, mv, grep run in \
process; control flow, functions, subshells or `$(...)` run the whole script in bash as one exec \
step. A file you will edit: `read` it, since `edit` needs the `[path#TAG]` header `cat` does not \
print. No API keys or tokens in the environment. The result lists each step's exit status; \
output is bounded. A script outliving the blocking budget continues as a job; its end arrives as \
a `[job-settled]` message.";

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
    let schema =
        super::tool_contract::parameters(1, [("script", eukhe_ai::typebox::Type::string())]);
    let mut registration = ToolRegistration::new(
        NAME,
        DESCRIPTION,
        schema,
        move |args: PiJsonValue, api: Arc<dyn ToolExecutionApi>, cx: Context| {
            let deps = Arc::clone(&deps);
            async move { execute(&deps, args, api, &cx).await }
        },
    );
    // A step may have written before a crash: never replay. A git push or
    // commit is adopted when the ref it moves shows it landed.
    registration.execution_mode = Some(ToolExecutionMode::Sequential);
    registration.replay = Some(ToolReplay::Unsafe);
    registration.probe = Some(git_evidence::probe());
    registration.extra = Some(Arc::new(super::runner::Runner {
        caps: eukhe_types::shell::ShellEffects::of(&ShellEffect::ALL),
        gate: super::runner::Gate::EachStep,
    }));
    define_extension(Extension {
        tools: vec![define_tool(registration)],
        ..Extension::named(SHELL_EXTENSION)
    })
}

#[tracing::instrument(level = "debug", skip_all, fields(task = %api.task_id()))]
async fn execute(
    deps: &Arc<HostDeps>,
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
    let transcript = Arc::new(Transcript::new(BoundedOutput::in_session(
        deps.storage_dir.as_deref(),
        &api.task_id().to_string(),
        api.truncation(),
    )));
    // An isolated child's copy becomes a repository when a script first
    // names git.
    if names_git(script) {
        if let Some(workspace) = ChildWorkspace::of_tree(&cwd) {
            if let Err(error) = workspace.git_view().await {
                transcript.push(&format!("[no git view of this copy: {error:#}]\n"), true);
            }
        }
    }
    // Durable before the script starts: a restart that cuts the call looks
    // at the ref its git step moves.
    if let Some(record) = git_evidence::record(script, &cwd).await? {
        api.probe(record, cx).await?;
    }
    let workspace = cwd.clone();
    let paths = super::path_policy::call_policy(deps, Some(api.conversation_id()), &cwd, cx).await;
    let call_steps = Arc::new(CallSteps::new(
        Arc::clone(deps),
        api.conversation_id(),
        api.call_id().to_owned(),
        Some(api.call_id().to_owned()),
    ));
    let mut running = {
        let env = local_env(&session_env(deps));
        let (script, transcript, call_steps) = (
            script.to_owned(),
            Arc::clone(&transcript),
            Arc::clone(&call_steps),
        );
        tokio::spawn(async move {
            Shell::new(cwd, env, "bash")
                .run(&script, &paths, &*call_steps, &*transcript)
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
            // Stamped at the detach: until then the call blocked the
            // model, so a later change is an edit made while the job ran
            // (or the job's own write).
            let before = TreeStamp::take(&workspace).await;
            let id = JobId::new(format!("shell-{}", uuid::Uuid::new_v4().simple()))
                .map_err(|error| SessionError::error(error.to_string()))?;
            // The job's start is durable before its detach is reported: a
            // script whose start is not recorded is stopped by the guard,
            // never left running unrecorded.
            let record = deps
                .jobs
                .record_start(id.clone(), JobKind::Shell, script.to_owned())
                .await?;
            abort_unless_detached.0 = None;
            let job = {
                let shown = transcript.shown();
                let job = deps.jobs.start(
                    record,
                    JobSpec {
                        truncation: api.truncation(),
                        written: shown.bounded.bytes(),
                        kill: {
                            let task = running.abort_handle();
                            Box::new(move |_| task.abort())
                        },
                    },
                );
                let _ = transcript.job.set(job.clone());
                job
            };
            let (partial, bounded) = transcript.projection();
            let sink = deps.job_settled.clone();
            let settled_id = id.clone();
            let call_steps = Arc::clone(&call_steps);
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
                // Each irreversible step was recorded at its own end.
                transcript.push(
                    &super::ran_effects::tool_notes(&call_steps.recorded()),
                    true,
                );
                if let Some(drift) = before
                    .drift(&TreeStamp::take(&workspace).await)
                    .text("the job")
                {
                    transcript.push(&format!("[{drift}]\n"), true);
                }
                let (text, bounded) = transcript.projection();
                let output = with_diagnostics(text, bounded.as_slice());
                tracing::debug!(job = %settled_id, status = status.label(), "detached script settled");
                // The result goes to a watching wait or the notice before
                // the job reads ended.
                job.settle(JobResult { status, output }, sink.as_ref());
                job.record(event);
            });
            return Ok(detached_result(&id, budget, partial, bounded));
        }
    };
    // The script ran; its result is not durable yet.
    kill_point(EffectKind::Tool.name(), "ran");
    let refused = matches!(ran.end, End::Refused { .. } | End::Rejected { .. });
    settle(&ran, &transcript);
    transcript.push(
        &super::ran_effects::tool_notes(&call_steps.recorded()),
        true,
    );
    let (text, bounded) = transcript.projection();
    let steps: Vec<serde_json::Value> = ran
        .steps
        .iter()
        .map(|step| {
            serde_json::json!({
                "step": step.step,
                "command": step.command,
                "effects": step.effects,
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
            effects,
            own,
        } => serde_json::json!({
            "kind": "refused",
            "step": step,
            "command": command,
            "effects": effects,
            "own": own.path,
        }),
        End::Rejected {
            step,
            command,
            effects,
        } => serde_json::json!({
            "kind": "rejected",
            "step": step,
            "command": command,
            "effects": effects,
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
            effects,
            own,
        } => {
            transcript.push(
                &format!(
                    "[stopped at step {step} ({}): `{command}` and the steps after it did not run: {own}.]\n",
                    effects.names(),
                ),
                true,
            );
            (CellStatus::Error, 1)
        }
        End::Rejected {
            step,
            command,
            effects,
        } => {
            transcript.push(
                &format!(
                    "[stopped at step {step} ({}): `{command}` and the steps after it did not run: {EDITOR_REFUSED}.]\n",
                    effects.names(),
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
            "The script outlived the {budget_ms} ms blocking budget and continues as job {job}. \
             Its result arrives on its own as a \
             [job-settled job:{job}] message: never poll. Do the work that does not need this \
             result and edits no file it reads (a check judges only the tree it ran on); \
             `await jobs.wait(\"{job}\")` only when nothing else can proceed."
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
