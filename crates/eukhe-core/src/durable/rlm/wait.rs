//! `jobs.wait`: the agent's one blocking wait on its own work. It ends with
//! the first of the agent's work that settles: a detached cell or `bash`
//! tool script of the session ([`crate::durable::jobs`]), a `bash()` handle
//! of the calling kernel (the kernel reports it), or an input queued for
//! the conversation (a user steer, a peer's message, a subagent's report,
//! a job notice), which follows the wait's result. Running subagents count
//! as work, so a wait with them running is no refusal; their reports end
//! it. With nothing running and nothing ready it is refused; it lasts what
//! the caller asked, at most 30 minutes, and the user's abort ends it.
//!
//! The compiled Bend core decides each poll and the cap (`bend/wait_any.bend`,
//! entry `wait_any`; `laws/wait_any.bend`). The wait watches the jobs it
//! waits on, so a job settling meanwhile keeps its result for the wait
//! instead of its notice; the result it takes is delivered once
//! ([`crate::durable::jobs::JobResult`]), and the ones it leaves go to the
//! notice when it ends.
//!
//! A cell whose whole code is one `await jobs.wait(...)` with literal
//! arguments runs here, without the kernel, while a detached cell holds
//! the kernel ([`served`]): a wait needs nothing of the namespace.

use std::collections::HashMap;
use std::future::Future;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_bend::rules::wait_any::{self, Pick, Signals, Target, Targets};
use eukhe_durable::types::ConversationId;
use serde_json::{json, Value};
use tokio::sync::Notify;

use super::RlmRuntime;
use crate::durable::jobs::Job;
use crate::durable::JobSettledSink;

/// Why a wait answers no end.
#[derive(Debug, thiserror::Error)]
pub(crate) enum WaitError {
    #[error(
        "Nothing to wait for: no job, bash() handle, subagent or message of this session is pending"
    )]
    Nothing,
    #[error("jobs.wait: unknown job {0:?}")]
    UnknownJob(String),
    #[error("jobs.wait: {0}")]
    Malformed(&'static str),
}

/// What a wait was asked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Ask {
    /// The job ids the caller named; `None`: all of its work.
    pub(crate) named: Option<Vec<String>>,
    /// The calling kernel's `bash()` handles the wait covers, each settled
    /// or not when the wait began.
    pub(crate) local: Vec<bool>,
    /// The length asked, in seconds; `None`: the cap.
    pub(crate) timeout_secs: Option<u64>,
}

/// How a wait ended.
pub(crate) enum Ended {
    /// A job settled; its result is the job's ([`Job::result`]).
    Job(Job),
    /// The kernel's `bash()` handle at this index settled.
    Local(usize),
    /// An input for the conversation is queued: it follows the result.
    Message,
    /// Its length passed with nothing settled.
    TimedOut,
    /// The user's abort, or the kernel's cancel, ended it.
    Cancelled,
}

/// The events the kernel sends a wait in flight (`jobs.wait_event`): a
/// `bash()` handle of the wait settled, or the cell's wait was cancelled.
#[derive(Default)]
struct Events {
    state: Mutex<EventState>,
    notify: Notify,
}

#[derive(Default)]
struct EventState {
    settled: Vec<usize>,
    cancelled: bool,
}

/// The waits in flight that the kernel named, by their id.
#[derive(Default)]
pub(crate) struct Waits {
    open: Mutex<HashMap<String, Arc<Events>>>,
}

impl Waits {
    fn open(&self) -> std::sync::MutexGuard<'_, HashMap<String, Arc<Events>>> {
        self.open.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Note one event for the wait `id`; nothing once it ended.
    pub(crate) fn event(&self, id: &str, local: Option<usize>, cancel: bool) {
        let Some(events) = self.open().get(id).cloned() else {
            return;
        };
        {
            let mut state = events.state.lock().unwrap_or_else(PoisonError::into_inner);
            state.settled.extend(local);
            state.cancelled |= cancel;
        }
        events.notify.notify_one();
    }
}

/// A wait's registration under its id, withdrawn when the wait ends.
struct Registered<'a> {
    waits: &'a Waits,
    id: Option<String>,
    events: Arc<Events>,
}

impl<'a> Registered<'a> {
    fn new(waits: &'a Waits, id: Option<String>) -> Self {
        let events = Arc::new(Events::default());
        if let Some(id) = &id {
            waits.open().insert(id.clone(), Arc::clone(&events));
        }
        Self { waits, id, events }
    }
}

impl Drop for Registered<'_> {
    fn drop(&mut self) {
        if let Some(id) = &self.id {
            self.waits.open().remove(id);
        }
    }
}

/// The jobs a wait watches, unwatched when it ends however it ends: a
/// result no wait watches any more goes to the notice.
struct Watching {
    jobs: Vec<Job>,
    sink: Option<JobSettledSink>,
}

impl Watching {
    fn new(jobs: Vec<Job>, sink: Option<JobSettledSink>) -> Self {
        for job in &jobs {
            job.watch();
        }
        Self { jobs, sink }
    }
}

impl Drop for Watching {
    fn drop(&mut self) {
        for job in &self.jobs {
            job.unwatch(self.sink.as_ref());
        }
    }
}

/// Wait as `ask` says on the work of `conversation` (the wait `id` the
/// kernel gave it, if any) until the first of it settles, its length
/// passes, or `abort` resolves.
///
/// # Errors
///
/// [`WaitError::Nothing`] with nothing to wait for, [`WaitError::UnknownJob`]
/// for a named job the session does not hold.
#[tracing::instrument(skip_all)]
pub(crate) async fn wait(
    runtime: &RlmRuntime,
    conversation: ConversationId,
    ask: Ask,
    id: Option<String>,
    abort: impl Future<Output = ()>,
) -> Result<Ended, WaitError> {
    let deps = &runtime.deps;
    let (mode, jobs) = match &ask.named {
        None => (Targets::Any, deps.jobs.agent_jobs()),
        Some(ids) => (
            Targets::Named,
            ids.iter()
                .map(|job| {
                    deps.jobs
                        .agent_jobs()
                        .into_iter()
                        .find(|held| held.id().as_str() == job)
                        .ok_or_else(|| WaitError::UnknownJob(job.clone()))
                })
                .collect::<Result<Vec<Job>, WaitError>>()?,
        ),
    };
    let registered = Registered::new(&runtime.waits, id);
    let watching = Watching::new(jobs, deps.job_settled.clone());
    let length = Duration::from_secs(wait_any::timeout_secs(ask.timeout_secs));
    let deadline = tokio::time::Instant::now() + length;
    let mut pulse = deps.jobs.pulse();
    let mut local: Vec<bool> = ask.local.clone();
    let mut aborted = false;
    let abort = futures::FutureExt::fuse(abort);
    futures::pin_mut!(abort);
    loop {
        pulse.borrow_and_update();
        let cancelled = {
            let mut state = registered
                .events
                .state
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            for index in state.settled.drain(..) {
                if let Some(settled) = local.get_mut(index) {
                    *settled = true;
                }
            }
            state.cancelled
        };
        let children = match mode {
            Targets::Any => running_children(runtime, conversation).await,
            Targets::Named => 0,
        };
        let message = deps.jobs.queued_input(conversation);
        let mut targets: Vec<Target> = local
            .iter()
            .map(|settled| {
                if *settled {
                    Target::Ready
                } else {
                    Target::Running
                }
            })
            .collect();
        targets.extend(watching.jobs.iter().map(Job::target));
        targets.extend(std::iter::repeat_n(Target::Running, children));
        if message {
            targets.push(Target::Ready);
        }
        let signals = Signals {
            cancelled: cancelled || aborted,
            late: tokio::time::Instant::now() >= deadline,
        };
        match wait_any::poll(mode, signals, &targets) {
            Pick::Take(index) => {
                return Ok(match index.checked_sub(local.len()) {
                    None => Ended::Local(index),
                    Some(at) => match watching.jobs.get(at) {
                        Some(job) => {
                            let _taken = job.take();
                            Ended::Job(job.clone())
                        }
                        // Past the jobs only the queued input is ever
                        // ready: running children are never taken.
                        None => Ended::Message,
                    },
                });
            }
            Pick::Nothing => return Err(WaitError::Nothing),
            Pick::Capped => return Ok(Ended::TimedOut),
            Pick::Cancelled => return Ok(Ended::Cancelled),
            Pick::Wait => {}
        }
        tokio::select! {
            changed = pulse.changed() => {
                if changed.is_err() {
                    // The table went away: the session closed.
                    aborted = true;
                }
            }
            () = registered.events.notify.notified() => {}
            () = tokio::time::sleep_until(deadline) => {}
            () = &mut abort, if !aborted => aborted = true,
        }
    }
}

/// How many subagents of `conversation` still owe their run or report;
/// none when the session closed.
async fn running_children(runtime: &RlmRuntime, conversation: ConversationId) -> usize {
    let Some(harness) = runtime.deps.harness.get() else {
        return 0;
    };
    match crate::durable::children::unsettled_children(&harness, conversation, &super::background())
        .await
    {
        Ok(children) => children.count,
        Err(error) => {
            tracing::debug!(%error, "jobs.wait could not read the subagents");
            0
        }
    }
}

/// A job as `jobs.list` and `jobs.wait` answer it: `running` or how it
/// settled, and its output once it did.
pub(crate) fn job_json(job: &Job) -> Value {
    let mut entry = json!({
        "id": job.id().as_str(),
        "kind": job.kind().name(),
        "elapsed_ms": u64::try_from(job.elapsed().as_millis()).unwrap_or(u64::MAX),
        "state": "running",
    });
    if let Some(result) = job.result() {
        entry["state"] = json!(result.status.label());
        entry["output"] = json!(result.output);
    }
    entry
}

/// The kernel's reply for a wait's end.
pub(crate) fn ended_json(ended: &Ended) -> Value {
    match ended {
        Ended::Job(job) => json!({ "end": "job", "job": job_json(job) }),
        Ended::Local(index) => json!({ "end": "local", "index": index }),
        Ended::Message => json!({ "end": "message" }),
        Ended::TimedOut => json!({ "end": "timeout" }),
        Ended::Cancelled => json!({ "end": "cancelled" }),
    }
}

/// The text a wait served without the kernel settles its call with.
pub(crate) fn served_text(ended: &Ended, holder: &Job) -> String {
    let note = format!(
        "[served without the kernel: job {} still holds it, so this cell ran as the wait alone]",
        holder.id()
    );
    match ended {
        Ended::Job(job) => {
            let entry = job_json(job);
            format!(
                "{note}\nJob {} ({}) {} after {} ms:\n{}",
                job.id(),
                job.kind().name(),
                entry["state"].as_str().unwrap_or("running"),
                entry["elapsed_ms"],
                entry["output"].as_str().unwrap_or_default()
            )
        }
        Ended::Message => {
            format!("{note}\nA message arrived for this session; it follows this result.")
        }
        Ended::TimedOut => {
            format!("{note}\nNone: nothing settled before the wait's length passed.")
        }
        // A served wait has no kernel handles; the abort ends the call.
        Ended::Local(_) | Ended::Cancelled => format!("{note}\nNone: the wait was cancelled."),
    }
}

/// The ask of a `jobs.wait` host request: `targets` (null: all work; else
/// the named job ids, none when only kernel handles are named), `local` (the kernel handles: `ready` or `running`),
/// `timeout_s` (null or a non-negative integer).
///
/// # Errors
///
/// [`WaitError::Malformed`] for any other shape.
pub(crate) fn ask_of(data: &Value) -> Result<Ask, WaitError> {
    let named = match data.get("targets") {
        None | Some(Value::Null) => None,
        Some(Value::Array(items)) => Some(
            items
                .iter()
                .map(|item| {
                    item.as_str()
                        .filter(|id| !id.is_empty())
                        .map(str::to_owned)
                        .ok_or(WaitError::Malformed(
                            "targets must be non-empty job id strings",
                        ))
                })
                .collect::<Result<Vec<String>, WaitError>>()?,
        ),
        Some(_) => return Err(WaitError::Malformed("targets must be null or a list")),
    };
    let local = match data.get("local") {
        None | Some(Value::Null) => Vec::new(),
        Some(Value::Array(items)) => items
            .iter()
            .map(|item| match item.as_str() {
                Some("ready") => Ok(true),
                Some("running") => Ok(false),
                Some(_) | None => Err(WaitError::Malformed(
                    "local must list \"ready\" or \"running\"",
                )),
            })
            .collect::<Result<Vec<bool>, WaitError>>()?,
        Some(_) => return Err(WaitError::Malformed("local must be a list")),
    };
    let timeout_secs = match data.get("timeout_s") {
        None | Some(Value::Null) => None,
        Some(value) => Some(value.as_u64().ok_or(WaitError::Malformed(
            "timeout_s must be a non-negative integer",
        ))?),
    };
    Ok(Ask {
        named,
        local,
        timeout_secs,
    })
}

/// The wait a cell's whole code asks, when it is one `await jobs.wait(...)`
/// (or `rlm.jobs.wait`, optionally inside `print(...)`) whose arguments are
/// literals: a job id string or a list or tuple of them, and `timeout_s=`
/// a number. Blank and comment lines around it are allowed. Anything else
/// (a variable, an assignment, a second statement) needs the kernel.
pub(crate) fn served(code: &str) -> Option<Ask> {
    let mut lines = code
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'));
    let line = lines.next()?;
    if lines.next().is_some() {
        return None;
    }
    let call = match line.strip_prefix("print(") {
        Some(inner) => inner.strip_suffix(')')?.trim(),
        None => line,
    };
    let call = call.strip_prefix("await")?.trim_start();
    let call = call
        .strip_prefix("rlm.jobs.wait")
        .or_else(|| call.strip_prefix("jobs.wait"))?
        .trim_start();
    let args = call.strip_prefix('(')?.strip_suffix(')')?;
    let mut ask = Ask {
        named: None,
        local: Vec::new(),
        timeout_secs: None,
    };
    let mut positional = false;
    for arg in split_top(args)? {
        let arg = arg.trim();
        if arg.is_empty() {
            continue;
        }
        if let Some(value) = arg.strip_prefix("timeout_s") {
            let value = value.trim_start().strip_prefix('=')?.trim();
            ask.timeout_secs = Some(seconds(value)?);
        } else if let Some(value) = arg.strip_prefix("targets") {
            if positional {
                return None;
            }
            positional = true;
            ask.named = targets(value.trim_start().strip_prefix('=')?.trim())?.named();
        } else {
            if positional || ask.timeout_secs.is_some() {
                return None;
            }
            positional = true;
            ask.named = targets(arg)?.named();
        }
    }
    Some(ask)
}

/// `args` split at its top-level commas; `None` when a bracket or quote
/// does not close.
fn split_top(args: &str) -> Option<Vec<&str>> {
    let mut parts = Vec::new();
    let mut depth = 0usize;
    let mut quote: Option<char> = None;
    let mut start = 0;
    for (at, ch) in args.char_indices() {
        match (quote, ch) {
            (Some(open), _) if ch == open => quote = None,
            (None, '\'' | '"') => quote = Some(ch),
            (None, '[' | '(') => depth += 1,
            (None, ']' | ')') => depth = depth.checked_sub(1)?,
            (None, ',') if depth == 0 => {
                parts.push(&args[start..at]);
                start = at + 1;
            }
            (Some(_) | None, _) => {}
        }
    }
    if quote.is_some() || depth != 0 {
        return None;
    }
    parts.push(&args[start..]);
    Some(parts)
}

/// What a literal target selects.
enum Selection {
    /// `None`: all of the agent's work.
    All,
    /// The job ids named.
    Ids(Vec<String>),
}

impl Selection {
    fn named(self) -> Option<Vec<String>> {
        match self {
            Self::All => None,
            Self::Ids(ids) => Some(ids),
        }
    }
}

/// A literal target: `None` (all work), a job id string, or a list or
/// tuple of them.
fn targets(value: &str) -> Option<Selection> {
    if value == "None" {
        return Some(Selection::All);
    }
    let inner = value
        .strip_prefix('[')
        .and_then(|rest| rest.strip_suffix(']'))
        .or_else(|| {
            value
                .strip_prefix('(')
                .and_then(|rest| rest.strip_suffix(')'))
        });
    let ids = match inner {
        Some(inner) => split_top(inner)?
            .into_iter()
            .map(str::trim)
            .filter(|item| !item.is_empty())
            .map(string)
            .collect::<Option<Vec<String>>>()?,
        None => vec![string(value)?],
    };
    (!ids.is_empty()).then_some(Selection::Ids(ids))
}

/// A quoted string literal without escapes.
fn string(value: &str) -> Option<String> {
    let quote = value.chars().next().filter(|ch| matches!(ch, '\'' | '"'))?;
    let body = value.strip_prefix(quote)?.strip_suffix(quote)?;
    (!body.is_empty() && !body.contains(['\\', '\'', '"'])).then(|| body.to_owned())
}

/// A non-negative number literal as whole seconds, rounded up.
fn seconds(value: &str) -> Option<u64> {
    let secs: f64 = value.parse().ok()?;
    (secs.is_finite() && secs >= 0.0).then(|| {
        #[expect(
            clippy::cast_possible_truncation,
            clippy::cast_sign_loss,
            reason = "a finite non-negative length, rounded up; the core caps it at 30 minutes"
        )]
        let whole = secs.ceil().min(u64::MAX as f64) as u64;
        whole
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ask(named: Option<&[&str]>, timeout_secs: Option<u64>) -> Ask {
        Ask {
            named: named.map(|ids| ids.iter().map(|id| (*id).to_owned()).collect()),
            local: Vec::new(),
            timeout_secs,
        }
    }

    /// Only a lone wait with literal arguments runs without the kernel.
    #[test]
    fn a_lone_literal_wait_is_served() {
        assert_eq!(
            [
                served("await jobs.wait()"),
                served("# wait\nawait rlm.jobs.wait('cell-1')\n"),
                served("print(await jobs.wait([\"cell-1\", 'shell-2'], timeout_s=90.5))"),
                served("await jobs.wait(targets=('cell-1',))"),
                served("await jobs.wait(None, timeout_s=0)"),
                served("job = await jobs.wait()"),
                served("await jobs.wait(h)"),
                served("await jobs.wait()\nprint(1)"),
                served("await jobs.wait('a\\'b')"),
                served("await jobs.wait(timeout_s=-1)"),
            ],
            [
                Some(ask(None, None)),
                Some(ask(Some(&["cell-1"]), None)),
                Some(ask(Some(&["cell-1", "shell-2"]), Some(91))),
                Some(ask(Some(&["cell-1"]), None)),
                Some(ask(None, Some(0))),
                None,
                None,
                None,
                None,
                None,
            ]
        );
    }
}
