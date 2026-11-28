//! Spawns: every child is a node of the agent tree
//! (requirements T1-T16 of `spec/README.md`).
//!
//! - `rlm.split` admits a split of this session's crown and spawns both
//!   children, each in its own copy-on-write workspace over its scope.
//! - `rlm.run` (`rlm.spawn`) asks a read-only help leaf in the shared
//!   workspace; with a `node` kwarg it spawns a node of a crown the caller
//!   keeps itself (a workflow's batch).
//! - Main's `worker_assign` creates the tree's root (one at a time).
//! - `rlm.tree_facts`, `rlm.tree_lend` and `rlm.tree_return` serve a
//!   caller that keeps its own crown.
//!
//! The compiled core decides each admission
//! (`eukhe_bend::rules::agent_tree::step`) in the commit that creates the
//! child tasks, their registry rows and their budget carves: a refusal
//! admits nothing. A child the core gives a limit is carved that limit
//! out of this session's account ([`super::budget`]); its unspent part
//! returns when it settles.

use std::borrow::Cow;
use std::sync::{Arc, Mutex, PoisonError};

use anyhow::{anyhow, bail};
use eukhe_bend::rules::agent_tree::{Dir, Lim};
use eukhe_chord::json::to_json;
use eukhe_durable::harness::types::{
    SubmissionDraft, ToolExecutionApi, ToolExecutionApiExt, WriteSubmissionDraft,
};
use eukhe_durable::harness::Harness;
use eukhe_durable::session::SessionError;
use eukhe_durable::types::{
    ConversationId, DocumentObserverExt, TaskId, TaskOptions, TaskOutcome, TaskOwnership, TaskState,
};
use eukhe_types::acceptance::{AcceptanceSeed, CheckSpec};
use eukhe_types::budget::{BudgetAmounts, BudgetDimension, BudgetLimits, BudgetReport};
use eukhe_types::custom_type::SPAWN_FAILED_NOTICE_CUSTOM_TYPE;
use eukhe_types::daemon::agent_tree::{TreePlace, TreeRole};
use futures::FutureExt;
use serde::Deserialize;
use serde_json::{json, Map, Value};
use tokio::sync::Notify;

use super::budget::{allot, give_back, named_budget, Allotment};
use super::depth::read_max_depth_override;
use super::host::{ChildMessageKind, RlmChildVerdict};
use super::notice::rlm_child_label;
use super::registry::{
    child_identity, read_children, tx_children, tx_put_row, ChildRow, ChildStatus, ChildrenState,
    CHILDREN_DOC,
};
use super::requests::{commit, conversation_of, cx, now_ms, session_error};
use super::task::{ChildTaskInput, ReportMode, TreeSpawn};
use super::tree::{self, Half, Local, Slot, SplitRequest};
use super::wire::RlmSpawnHandle;
use super::Children;
use crate::agent_messaging::assert_direct_agent_message_target;
use crate::durable::deps::HostCall;
use crate::durable::rlm::CustomNotice;
use crate::kernel::rlm_runtime::{
    create_default_rlm_subagent_session_name, kwargs_from_payload,
    normalize_requested_rlm_subagent_model, normalize_requested_rlm_subagent_session_name,
    normalize_requested_rlm_subagent_thinking_level,
};

pub(super) const NO_SPAWN_RUNTIME: &str =
    "rlm.spawn requires a daemon-backed session: this session has no RLM child runtime";

/// The kwargs every spawn takes.
const SPAWN_KEYS: [&str; 8] = [
    "name",
    "model",
    "thinking",
    "label",
    "accept",
    "accept_intent",
    "accept_returns",
    "phase",
];

/// Validated spawn kwargs.
pub(super) struct SpawnKwargs {
    pub(super) name: Option<String>,
    pub(super) model: Option<String>,
    pub(super) thinking: Option<String>,
    /// The roster label; `None`: derived from the prompt.
    pub(super) label: Option<String>,
    /// The workflow phase the child serves.
    pub(super) phase: Option<String>,
    pub(super) report: ReportMode,
    /// The budget the spawn names (`budget`): a help leaf's limit, or a
    /// node of a caller's crown carved that budget; a split child's limit
    /// is the core's.
    pub(super) budget: Option<BudgetLimits>,
    /// The checks the child's task starts with, this parent their owner
    /// (`accept`, `accept_intent`, `accept_returns`); `None`: no checks.
    pub(super) accept: Option<AcceptanceSeed>,
}

/// Validate `kwargs` of `operation`, which takes the common keys and
/// `more`. Name, model and thinking normalize through the pure helpers.
fn spawn_kwargs(
    kwargs: &Map<String, Value>,
    operation: &str,
    more: &[&str],
) -> anyhow::Result<SpawnKwargs> {
    let supported: Vec<&str> = SPAWN_KEYS.iter().chain(more).copied().collect();
    reject_unsupported_kwargs(kwargs, operation, &supported)?;
    let name = optional_string_kwarg(kwargs, "name", operation)?;
    let name = normalize_requested_rlm_subagent_session_name(name, operation)?;
    if let Some(name) = &name {
        assert_direct_agent_message_target(name)?;
    }
    let model = optional_string_kwarg(kwargs, "model", operation)?;
    let model = normalize_requested_rlm_subagent_model(model, operation)?;
    let thinking = optional_string_kwarg(kwargs, "thinking", operation)?;
    let thinking =
        normalize_requested_rlm_subagent_thinking_level(thinking, operation)?.map(String::from);
    let text = |key: &str| -> anyhow::Result<Option<String>> {
        Ok(optional_string_kwarg(kwargs, key, operation)?
            .map(str::trim)
            .filter(|value| !value.is_empty())
            .map(str::to_owned))
    };
    let report = match optional_string_kwarg(kwargs, "report", operation)? {
        None | Some("inbox") => ReportMode::Inbox,
        Some("silent") => ReportMode::Silent,
        Some(_) => bail!("{operation} report must be \"inbox\" or \"silent\""),
    };
    Ok(SpawnKwargs {
        name,
        model,
        thinking,
        label: text("label")?,
        phase: text("phase")?,
        report,
        budget: named_budget(kwargs, operation)?,
        accept: spawn_acceptance(kwargs, operation)?,
    })
}

/// A node of a crown its spawner keeps itself (`node` of `rlm.run`).
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
struct NodeKwarg {
    role: TreeRole,
    path: String,
    units: Vec<String>,
    scope: Vec<bool>,
    allowance: u64,
    #[serde(default)]
    deadline_ms: Option<u64>,
}

impl NodeKwarg {
    fn spawn(self) -> anyhow::Result<TreeSpawn> {
        if self.units.len() != self.scope.len() {
            bail!("rlm.spawn node scope must hold one bool per unit");
        }
        let units: Vec<String> = self
            .units
            .iter()
            .map(|unit| tree::unit_path(unit))
            .collect();
        Ok(TreeSpawn {
            place: TreePlace {
                role: self.role,
                scope: tree::paths(&units, &self.scope),
                path: self.path,
                allowance: self.allowance,
                deadline: self.deadline_ms,
            },
            units,
            scope: self.scope,
            slot: Slot::External,
        })
    }
}

/// One validated spawn.
pub(super) struct SpawnSpec {
    pub(super) prompt: String,
    pub(super) kwargs: SpawnKwargs,
    /// More details of the task prompt's row (`userMessages`, `note`).
    pub(super) details: Option<Map<String, Value>>,
    /// Main's user entries the prompt hands over (their images go along).
    pub(super) user_entries: Vec<u64>,
    /// The child is a worker of a main session.
    pub(super) worker: bool,
    /// The items of the child's work list (a split half's `items`).
    pub(super) items: Vec<String>,
}

/// What a spawn is in the tree.
pub(super) enum Admission {
    /// One read-only help leaf of this session's crown.
    Help,
    /// A split of this session's crown: the specs are left, then right.
    Split(SplitRequest),
    /// Main's root: one at a time; `forward_cursor`: the user messages
    /// its task carries are handed over in the same commit.
    Root { forward_cursor: u64 },
    /// A node of a crown the caller keeps.
    External(TreeSpawn),
}

/// The children an admission places, with their carves, and the crown
/// that holds them (`None`: this session's crown does not change).
struct Placed {
    trees: Vec<TreeSpawn>,
    limits: Vec<Option<BudgetLimits>>,
    local: Option<Local>,
}

/// The refusal of a second root while one runs.
pub(super) fn root_running(name: &str) -> String {
    format!(
        "the agent tree's root {name} is still running: one root per workspace at a time; worker_forward reaches it"
    )
}

/// The crown of a session at `place` before its first split or help.
fn open_local(place: &TreePlace, report: Option<&BudgetReport>) -> Local {
    let dimension = report.and_then(|report| tree::dimension(&report.limits));
    let limit = match (report, dimension) {
        (Some(report), Some(dimension)) => Lim::Value(report.free.get(dimension)),
        (None, _) | (_, None) => Lim::Unlimited,
    };
    Local::open(place, limit, dimension)
}

/// The facts a spawn's decision reads, gathered before its commit.
struct Gathered {
    place: Option<TreePlace>,
    report: Option<BudgetReport>,
    keep: BudgetAmounts,
    /// Unix ms.
    now: u64,
}

impl Gathered {
    /// The carve of a child the core gave `limit` up to `deadline`;
    /// `named`: the spawn's own budget, carved when the crown is
    /// unlimited.
    fn carve(
        &self,
        local: &Local,
        limit: Lim,
        deadline: Lim,
        named: Option<BudgetLimits>,
    ) -> Option<BudgetLimits> {
        match (limit, local.dimension, &self.report) {
            (Lim::Value(amount), Some(dimension), Some(report)) => {
                let time_left = match deadline {
                    Lim::Value(at) => Some(at.saturating_sub(self.now)),
                    Lim::Unlimited => None,
                };
                Some(tree::child_limits(report, dimension, amount, time_left))
            }
            _ => named,
        }
    }

    /// The amount `named` gives in the crown's dimension.
    fn named_amount(local: &Local, named: Option<&BudgetLimits>) -> Option<u64> {
        let dimension: BudgetDimension = local.dimension?;
        let named = named?;
        match dimension {
            BudgetDimension::Cost => named.cost_micros,
            BudgetDimension::Tokens => named.tokens,
            BudgetDimension::Requests => named.requests,
            BudgetDimension::ToolCalls => named.tool_calls,
            BudgetDimension::Time => named.time_ms,
        }
    }

    fn place(&self) -> Result<&TreePlace, String> {
        self.place
            .as_ref()
            .ok_or_else(|| tree::OUTSIDE_TREE.to_owned())
    }

    /// The place of child `dir` of this session.
    fn child_place(&self, dir: Dir, half: &Half) -> Result<TreePlace, String> {
        let place = self.place()?;
        let (role, step) = match dir {
            Dir::Left => (TreeRole::Left, 'L'),
            Dir::Right => (TreeRole::Right, 'R'),
        };
        Ok(TreePlace {
            role,
            scope: half.scope.clone(),
            path: format!("{}{step}", place.path),
            allowance: half.allowance,
            deadline: Local::deadline_of(half.deadline),
        })
    }
}

/// Place the children `admission` spawns: the core's decision on this
/// session's crown `local` (opened at the session's place when it has
/// none yet), and each child's place and carve. `named`: each spec's own
/// budget.
fn place_children(
    admission: &Admission,
    local: Option<&Local>,
    facts: &Gathered,
    rows: &ChildrenState,
    named: &[Option<BudgetLimits>],
) -> Result<Placed, String> {
    let local = || -> Result<Local, String> {
        Ok(match local.cloned() {
            Some(local) => local,
            None => open_local(facts.place()?, facts.report.as_ref()),
        })
    };
    match admission {
        Admission::Help => {
            let local = local()?;
            let named_budget = named.first().copied().flatten();
            let amount = Gathered::named_amount(&local, named_budget.as_ref())
                .unwrap_or_else(|| local.help_amount());
            let (local, index) = local
                .help(amount)
                .map_err(|refusal| refusal.text().to_owned())?;
            let help = local.crown().helps[index].clone();
            let place = facts.place()?;
            let tree = TreeSpawn {
                place: TreePlace {
                    role: TreeRole::Help,
                    scope: Vec::new(),
                    path: place.path.clone(),
                    allowance: 1,
                    deadline: Local::deadline_of(help.deadline),
                },
                units: Vec::new(),
                scope: Vec::new(),
                slot: Slot::Help { index },
            };
            Ok(Placed {
                limits: vec![facts.carve(&local, help.limit, help.deadline, named_budget)],
                trees: vec![tree],
                local: Some(local),
            })
        }
        Admission::Split(request) => {
            let local = local()?;
            let worst = local
                .dimension
                .map_or(0, |dimension| facts.keep.get(dimension));
            let (local, halves) = local
                .split(request, worst)
                .map_err(|refusal| refusal.text().to_owned())?;
            let mut trees = Vec::with_capacity(2);
            let mut limits = Vec::with_capacity(2);
            for (dir, half) in [(Dir::Left, &halves.left), (Dir::Right, &halves.right)] {
                trees.push(TreeSpawn {
                    place: facts.child_place(dir, half)?,
                    units: local.units.clone(),
                    scope: half.mask.clone(),
                    slot: Slot::side(dir),
                });
                limits.push(facts.carve(&local, half.limit, half.deadline, None));
            }
            Ok(Placed {
                trees,
                limits,
                local: Some(local),
            })
        }
        Admission::Root { .. } => {
            if let Some(root) = rows
                .children
                .values()
                .find(|row| row.worker && !row.is_deleted() && !row.status.is_terminal())
            {
                return Err(root_running(&root.session_name));
            }
            Ok(Placed {
                trees: vec![TreeSpawn::root()],
                limits: named.to_vec(),
                local: None,
            })
        }
        Admission::External(tree) => Ok(Placed {
            trees: vec![tree.clone()],
            limits: named.to_vec(),
            local: None,
        }),
    }
}

/// Admit `specs` as `eukhe.rlm.child` tasks of the calling tool's
/// conversation as `admission` places them, in one commit with their
/// registry rows, the crown that holds them and their carves; then wait
/// for each task's `spawn` phase to create its child. Names are unique
/// among the conversation's live children.
pub(super) async fn admit_spawns(
    children: &Arc<Children>,
    call: &HostCall,
    specs: Vec<SpawnSpec>,
    admission: Admission,
) -> anyhow::Result<Vec<RlmSpawnHandle>> {
    if !children.has_runtime {
        bail!("{NO_SPAWN_RUNTIME}");
    }
    let Some(api) = call.call.clone() else {
        bail!("rlm.spawn must run inside a tool call");
    };
    let harness = children.harness.require().map_err(session_error)?;
    let conversation_id = api.conversation_id();
    // The runtime bound (`set_rlm_max_depth`) of the calling conversation
    // overrides the configured one; the child inherits it.
    let max_depth = read_max_depth_override(&harness, conversation_id, &cx())
        .await
        .map_err(session_error)?
        .unwrap_or(children.services.rlm_max_depth);
    let child_depth = children.services.rlm_depth + 1;
    let gate = Arc::clone(&children.services.budget);
    let facts = Gathered {
        place: children.services.place.clone(),
        report: gate.report(),
        keep: gate.keep(),
        now: epoch_ms(),
    };
    // The spawn anchors to the parent's in-flight model request; the tool
    // call id stands in when no recorder carries one.
    let spawned_by_request_id = children
        .services
        .semantic_edges
        .as_ref()
        .and_then(|recorder| recorder.last_turn_request_id())
        .or_else(|| Some(api.call_id().to_owned()));
    let task = children.task.as_definition_ref();
    let parent_session_id = children.services.parent_session_id.clone();
    let started_at = now_ms();
    // What the commit carved out of this session's budget: it returns
    // when the commit does not land.
    let carved = Arc::new(Mutex::new(Vec::new()));
    let taken = Arc::clone(&carved);
    let committed = api
        .commit(
            move |tx| async move {
                let state = tx_children(&tx, conversation_id).await?;
                let mut batch_names: Vec<&str> = Vec::new();
                for name in specs.iter().filter_map(|spec| spec.kwargs.name.as_deref()) {
                    let taken = batch_names.contains(&name)
                        || state
                            .children
                            .values()
                            .any(|row| !row.is_deleted() && row.session_name == name);
                    if taken {
                        return Err(SessionError::error(spawn_name_unavailable(
                            name,
                            child_depth,
                        )));
                    }
                    batch_names.push(name);
                }
                let named: Vec<Option<BudgetLimits>> =
                    specs.iter().map(|spec| spec.kwargs.budget).collect();
                let local = tree::tx_local(&tx, conversation_id).await?;
                let placed = place_children(&admission, local.as_ref(), &facts, &state, &named)
                    .map_err(SessionError::error)?;
                let mut local = placed.local;
                let mut task_ids = Vec::with_capacity(specs.len());
                let mut allotments = Vec::with_capacity(specs.len());
                for ((spec, tree), limits) in specs.into_iter().zip(placed.trees).zip(placed.limits)
                {
                    let slot = tree.slot;
                    let input = ChildTaskInput {
                        prompt: spec.prompt,
                        model: spec.kwargs.model,
                        thinking: spec.kwargs.thinking,
                        spawned_by_request_id: spawned_by_request_id.clone(),
                        max_depth: Some(max_depth),
                        tree: Some(tree),
                        owed: None,
                        report: spec.kwargs.report,
                        child: None,
                        kind: ChildMessageKind::Task,
                        details: spec.details,
                        user_entries: spec.user_entries,
                        worker: spec.worker,
                        accept: spec.kwargs.accept,
                        items: spec.items,
                    };
                    let task_id = tx
                        .create_task(
                            Arc::clone(&task),
                            to_json(&input)?,
                            TaskOptions {
                                ownership: TaskOwnership::Conversation,
                                conversation_id: Some(conversation_id),
                                background: Some(true),
                                abandon_on_restart: None,
                            },
                        )
                        .await?;
                    if let Some(local) = local.as_mut() {
                        match slot {
                            Slot::Side { dir } => match Dir::from(dir) {
                                Dir::Left => local.left = Some(task_id.get()),
                                Dir::Right => local.right = Some(task_id.get()),
                            },
                            Slot::Help { .. } => local.helps.push(task_id.get()),
                            Slot::Root | Slot::External => {}
                        }
                    }
                    let identity = child_identity(&parent_session_id, task_id);
                    let session_name = spec.kwargs.name.unwrap_or_else(|| {
                        create_default_rlm_subagent_session_name(
                            &input.prompt,
                            &identity.rlm_child_id,
                        )
                    });
                    let row = ChildRow {
                        task_id: task_id.get(),
                        rlm_child_id: identity.rlm_child_id,
                        session_id: identity.session_id,
                        session_name,
                        label: spec
                            .kwargs
                            .label
                            .unwrap_or_else(|| rlm_child_label(&input.prompt)),
                        started_at,
                        status: ChildStatus::Spawning,
                        active_session_id: None,
                        session_dir: None,
                        model: None,
                        answer_preview: None,
                        error: None,
                        failure: None,
                        replied_since_task: false,
                        deletion: None,
                        settled: false,
                        read: false,
                        report_submission: None,
                        usage: None,
                        progress: None,
                        reporter: None,
                        handback: None,
                        phase: spec.kwargs.phase,
                        answer: None,
                        task: None,
                        worker: input.worker,
                        acceptance: input
                            .accept
                            .as_ref()
                            .map(|seed| RlmChildVerdict::pending(seed.specs().len())),
                        patch: None,
                        stopped: None,
                    };
                    tx_put_row(&tx, conversation_id, &row).await?;
                    if let Some(limits) = limits {
                        allotments.push(Allotment {
                            session_id: row.session_id,
                            limits,
                        });
                    }
                    task_ids.push(task_id);
                }
                if let Some(local) = &local {
                    tree::tx_put_local(&tx, conversation_id, local).await?;
                }
                if let Admission::Root { forward_cursor } = admission {
                    super::worker::tx_hand_over(&tx, conversation_id, forward_cursor).await?;
                }
                // Each carve leaves the account here, all of them or none,
                // before the commit that starts the children: a refusal
                // admits nothing, and no child starts without its carve on
                // disk.
                let allotted = allot(&gate, allotments).await?;
                *taken.lock().unwrap_or_else(PoisonError::into_inner) = allotted;
                Ok(task_ids)
            },
            &cx(),
        )
        .await;
    let task_ids = match committed {
        Ok(task_ids) => task_ids,
        Err(error) => {
            // No child was admitted: what the commit carved returns now
            // (after a failure here, at this session's next open).
            let carved =
                std::mem::take(&mut *carved.lock().unwrap_or_else(PoisonError::into_inner));
            for child in carved {
                if let Err(failure) = give_back(&children.services.budget, &child).await {
                    tracing::warn!(
                        %child,
                        error = %failure,
                        "returning the allotment of a spawn that was not admitted"
                    );
                }
            }
            return Err(anyhow!("{error}"));
        }
    };
    // Every task is admitted; each child is waited for, so a failure names
    // every child that did not start and every one that did (it stays
    // admitted and listed), never a success with fewer children.
    let mut handles = Vec::with_capacity(task_ids.len());
    let mut failures = Vec::new();
    for task_id in task_ids {
        match wait_for_admission(&harness, conversation_id, task_id).await {
            Ok(row) => handles.push(RlmSpawnHandle {
                rlm_child_id: row.rlm_child_id,
                name: row.session_name,
                session_dir: row.session_dir.unwrap_or_default(),
                model: row.model.unwrap_or_default(),
            }),
            Err(error) => failures.push(format!("{error:#}")),
        }
    }
    if failures.is_empty() {
        return Ok(handles);
    }
    let failed = failures.join("; ");
    if handles.is_empty() {
        return Err(anyhow!(failed));
    }
    let started: Vec<&str> = handles.iter().map(|handle| handle.name.as_str()).collect();
    Err(anyhow!(
        "{failed}; started anyway: {} (rlm.list_subagents lists them)",
        started.join(", ")
    ))
}

/// The wall clock in Unix milliseconds.
pub(super) fn epoch_ms() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |elapsed| {
            u64::try_from(elapsed.as_millis()).unwrap_or(u64::MAX)
        })
}

// ---------------------------------------------------------------------------
// rlm.run / rlm.split
// ---------------------------------------------------------------------------

/// `rlm.spawn`: a read-only help leaf of this session's node, or (with
/// `node`) a node of a crown the caller keeps.
pub(super) async fn run(children: Arc<Children>, call: HostCall) -> anyhow::Result<Value> {
    const OPERATION: &str = "rlm.spawn";
    let Some(prompt) = call.data.get("prompt").and_then(Value::as_str) else {
        bail!("{OPERATION} prompt must be a string");
    };
    let kwargs = kwargs_from_payload(&call.data);
    let node = match kwargs.get("node") {
        None | Some(Value::Null) => None,
        Some(node) => Some(
            serde_json::from_value::<NodeKwarg>(node.clone())
                .map_err(|error| anyhow!("{OPERATION} node: {error}"))?
                .spawn()?,
        ),
    };
    let spec = SpawnSpec {
        prompt: prompt.to_owned(),
        kwargs: spawn_kwargs(&kwargs, OPERATION, &["report", "budget", "node", "items"])?,
        details: None,
        user_entries: Vec::new(),
        worker: false,
        items: item_list(kwargs.get("items"), OPERATION)?,
    };
    let admission = node.map_or(Admission::Help, Admission::External);
    let handles = admit_spawns(&children, &call, vec![spec], admission).await?;
    let handle = handles
        .into_iter()
        .next()
        .ok_or_else(|| anyhow!("{OPERATION} admitted no child"))?;
    Ok(serde_json::to_value(&handle)?)
}

/// The paths of a split half's or own scope.
fn scope_paths(value: Option<&Value>, what: &str) -> anyhow::Result<Vec<String>> {
    let Some(Value::Array(items)) = value else {
        bail!("rlm.split {what} must be a non-empty list of paths");
    };
    let paths = items
        .iter()
        .map(|item| {
            item.as_str()
                .map(tree::unit_path)
                .ok_or_else(|| anyhow!("rlm.split {what} must be a list of path strings"))
        })
        .collect::<anyhow::Result<Vec<_>>>()?;
    if paths.is_empty() {
        bail!("rlm.split {what} must be a non-empty list of paths");
    }
    Ok(paths)
}

/// The items of a task's work list (`items` of a split half, a spawn or
/// a worker's task): distinct non-empty ids.
pub(super) fn item_list(value: Option<&Value>, operation: &str) -> anyhow::Result<Vec<String>> {
    let items = match value {
        None | Some(Value::Null) => return Ok(Vec::new()),
        Some(Value::Array(items)) => items,
        Some(_) => bail!("{operation} items must be a list of item ids"),
    };
    let ids = items
        .iter()
        .map(|item| {
            item.as_str()
                .map(str::trim)
                .filter(|id| !id.is_empty())
                .map(str::to_owned)
                .ok_or_else(|| anyhow!("{operation} items must be non-empty strings"))
        })
        .collect::<anyhow::Result<Vec<_>>>()?;
    if let Some(twice) = ids
        .iter()
        .enumerate()
        .find_map(|(at, id)| ids[..at].contains(id).then_some(id))
    {
        bail!("{operation} items name {twice} twice");
    }
    Ok(ids)
}

/// One half of `rlm.split`: `{scope, task, items?, name?, model?,
/// thinking?, label?, accept?, ...}`.
fn half_spec(data: &Value, side: &str) -> anyhow::Result<(Vec<String>, SpawnSpec)> {
    let operation = format!("rlm.split {side}");
    let Some(half) = data.get(side).and_then(Value::as_object) else {
        bail!("{operation} must be a dict {{\"scope\": [paths], \"task\": str}}");
    };
    let Some(task) = half.get("task").and_then(Value::as_str) else {
        bail!("{operation} task must be a string");
    };
    let scope = scope_paths(half.get("scope"), &format!("{side} scope"))?;
    let spec = SpawnSpec {
        prompt: task.to_owned(),
        kwargs: spawn_kwargs(half, &operation, &["scope", "task", "items"])?,
        details: None,
        user_entries: Vec::new(),
        worker: false,
        items: item_list(half.get("items"), &operation)?,
    };
    Ok((scope, spec))
}

/// `rlm.split`: split this session's node into two children, each over
/// its scope in its own workspace; `own` (default: the rest of the scope)
/// stays this session's, `hold` (default: two worst-case requests or a
/// tenth of the room) stays free for it.
pub(super) async fn split(children: Arc<Children>, call: HostCall) -> anyhow::Result<Value> {
    let data = &call.data;
    let (left, left_spec) = half_spec(data, "left")?;
    let (right, right_spec) = half_spec(data, "right")?;
    let own = match data.get("own") {
        None | Some(Value::Null) => None,
        Some(Value::Array(items)) => Some(
            items
                .iter()
                .map(|item| {
                    item.as_str()
                        .map(tree::unit_path)
                        .ok_or_else(|| anyhow!("rlm.split own must be a list of path strings"))
                })
                .collect::<anyhow::Result<Vec<_>>>()?,
        ),
        Some(_) => bail!("rlm.split own must be a list of paths or None"),
    };
    let hold = match data.get("hold") {
        None | Some(Value::Null) => None,
        Some(value) => Some(
            value
                .as_u64()
                .ok_or_else(|| anyhow!("rlm.split hold must be a non-negative integer"))?,
        ),
    };
    let request = SplitRequest {
        left,
        right,
        own,
        hold,
    };
    let handles = admit_spawns(
        &children,
        &call,
        vec![left_spec, right_spec],
        Admission::Split(request),
    )
    .await?;
    let [left, right]: [RlmSpawnHandle; 2] = handles
        .try_into()
        .map_err(|_| anyhow!("rlm.split admitted other than two children"))?;
    Ok(json!({ "left": left, "right": right }))
}

/// Show the user, once, that a spawn the model asked for failed
/// (`operation`: `rlm.split` or `rlm.spawn`): a display-only row in the
/// calling conversation, placed at its next boundary, while the model reads
/// the error as the tool's result and decides what to do. The row's request
/// id is the tool call's, so a replayed call shows no second row. A closing
/// session takes none; a row that cannot be written is logged.
#[tracing::instrument(skip_all, fields(operation = %operation))]
pub(super) async fn show_spawn_failure(
    children: &Children,
    api: Option<Arc<dyn ToolExecutionApi>>,
    operation: &str,
    error: &anyhow::Error,
) {
    let (Some(api), Some(harness)) = (api, children.harness.get()) else {
        return;
    };
    let notice = CustomNotice::new(
        SPAWN_FAILED_NOTICE_CUSTOM_TYPE,
        format!("{operation} failed: {error:#}"),
        true,
        None,
    );
    let submitted = children
        .services
        .closing
        .admit(|| async {
            let entry = notice.draft()?;
            let conversation = harness
                .conversation(api.conversation_id(), &cx())
                .await?
                .ok_or_else(|| anyhow!("the calling conversation does not exist"))?;
            conversation
                .submit(
                    SubmissionDraft::Write(WriteSubmissionDraft {
                        request_id: Some(format!("spawn-failed:{}", api.call_id())),
                        entry,
                    }),
                    &cx(),
                )
                .await?;
            anyhow::Ok(())
        })
        .await;
    if let Some(Err(failure)) = submitted {
        tracing::warn!(error = %failure, operation, "spawn failure notice not delivered");
    }
}

// ---------------------------------------------------------------------------
// rlm.tree_facts / rlm.tree_lend / rlm.tree_return
// ---------------------------------------------------------------------------

/// This session's crown as committed, or opened at its place.
async fn session_local(
    children: &Children,
    harness: &Harness,
    conversation_id: ConversationId,
) -> anyhow::Result<Local> {
    let Some(place) = &children.services.place else {
        bail!("{}", tree::OUTSIDE_TREE);
    };
    Ok(
        match tree::read_local(harness, conversation_id, &cx())
            .await
            .map_err(session_error)?
        {
            Some(local) => local,
            None => open_local(place, children.services.budget.report().as_ref()),
        },
    )
}

/// An amount of `dimension` as the `budget` kwarg names it.
#[expect(
    clippy::cast_precision_loss,
    reason = "micro-dollars below 2^53 convert exactly"
)]
fn budget_kwarg(dimension: BudgetDimension, amount: u64) -> Value {
    match dimension {
        BudgetDimension::Cost => json!({ "cost_usd": amount as f64 / 1_000_000.0 }),
        BudgetDimension::Tokens => json!({ "tokens": amount }),
        BudgetDimension::Requests => json!({ "requests": amount }),
        BudgetDimension::ToolCalls => json!({ "tool_calls": amount }),
        BudgetDimension::Time => json!({ "time_s": amount / 1000 }),
    }
}

/// `rlm.tree_facts`: this session's write scope, path, depth, the nodes it
/// may still hold, what it may still spend (as a `budget` kwarg) and its
/// deadline.
pub(super) async fn tree_facts(children: Arc<Children>, call: HostCall) -> anyhow::Result<Value> {
    let harness = children.harness.require().map_err(session_error)?;
    let local = session_local(&children, &harness, conversation_of(&call)).await?;
    let facts = local.facts();
    let free = match (facts.free, local.dimension) {
        (Lim::Value(amount), Some(dimension)) => {
            json!({ "budget": budget_kwarg(dimension, amount) })
        }
        (Lim::Value(_) | Lim::Unlimited, _) => Value::Null,
    };
    Ok(json!({
        "writeScope": facts.write_scope,
        "path": children.services.place.as_ref().map(|place| place.path.as_str()),
        "depth": facts.depth,
        "remaining": facts.remaining,
        "free": free,
        "deadlineMs": Local::deadline_of(facts.deadline),
    }))
}

fn lend_key(data: &Value, operation: &str) -> anyhow::Result<String> {
    data.get("key")
        .and_then(Value::as_str)
        .filter(|key| !key.is_empty())
        .map(str::to_owned)
        .ok_or_else(|| anyhow!("{operation} key must be a non-empty string"))
}

/// `rlm.tree_lend`: lend `nodes` of this session's allowance under `key`
/// to a crown the caller keeps (once per key).
pub(super) async fn tree_lend(children: Arc<Children>, call: HostCall) -> anyhow::Result<Value> {
    let key = lend_key(&call.data, "rlm.tree_lend")?;
    let Some(nodes) = call.data.get("nodes").and_then(Value::as_u64) else {
        bail!("rlm.tree_lend nodes must be a non-negative integer");
    };
    let harness = children.harness.require().map_err(session_error)?;
    let conversation_id = conversation_of(&call);
    let local = session_local(&children, &harness, conversation_id).await?;
    commit(&harness, conversation_id, move |tx| async move {
        let local = tree::tx_local(&tx, conversation_id).await?.unwrap_or(local);
        let lent = local
            .lend(&key, nodes)
            .map_err(|refusal| SessionError::error(refusal.text()))?;
        tree::tx_put_local(&tx, conversation_id, &lent).await
    })
    .await?;
    Ok(json!({ "lent": nodes }))
}

/// `rlm.tree_return`: the nodes lent under `key` come back (once).
pub(super) async fn tree_return(children: Arc<Children>, call: HostCall) -> anyhow::Result<Value> {
    let key = lend_key(&call.data, "rlm.tree_return")?;
    let harness = children.harness.require().map_err(session_error)?;
    let conversation_id = conversation_of(&call);
    let local = session_local(&children, &harness, conversation_id).await?;
    commit(&harness, conversation_id, move |tx| async move {
        let local = tree::tx_local(&tx, conversation_id).await?.unwrap_or(local);
        tree::tx_put_local(&tx, conversation_id, &local.take_back(&key)).await
    })
    .await?;
    Ok(json!({ "returned": true }))
}

// ---------------------------------------------------------------------------
// checks, names, admission waits
// ---------------------------------------------------------------------------

/// The keys a check of `kind` takes (the `CheckSpec` wire shape); `None`
/// for a kind that is no check.
fn check_keys(kind: &str) -> Option<&'static [&'static str]> {
    let keys: &'static [&'static str] = match kind {
        "command" => &["kind", "command", "expect", "timeoutMs", "protect"],
        "judge" => &["kind", "condition", "evidence", "model"],
        "until" => &["kind", "command", "timeoutMs"],
        "intent" => &["kind", "model"],
        _ => return None,
    };
    Some(keys)
}

/// One check of `accept`: a `CheckSpec` object. A kernel's `snake_case`
/// `timeout_ms` reads as the wire's `timeoutMs`; an unknown key, an
/// unknown kind, or a check with no command or condition is refused.
fn spawn_check(index: usize, item: &Value, operation: &str) -> anyhow::Result<CheckSpec> {
    let what = format!("{operation} accept[{index}]");
    let Value::Object(fields) = item else {
        bail!("{what} must be a check object, e.g. {{\"kind\": \"command\", \"command\": \"pytest -q\", \"expect\": 0}}");
    };
    let fields: Cow<'_, Map<String, Value>> = if fields.contains_key("timeout_ms") {
        Cow::Owned(
            fields
                .iter()
                .map(|(key, value)| {
                    let key = if key == "timeout_ms" {
                        "timeoutMs"
                    } else {
                        key.as_str()
                    };
                    (key.to_owned(), value.clone())
                })
                .collect(),
        )
    } else {
        Cow::Borrowed(fields)
    };
    let kind = fields
        .get("kind")
        .and_then(Value::as_str)
        .unwrap_or_default();
    let Some(keys) = check_keys(kind) else {
        bail!("{what} kind must be \"command\", \"judge\", \"until\" or \"intent\"");
    };
    if let Some(key) = fields.keys().find(|key| !keys.contains(&key.as_str())) {
        bail!(
            "{what} has the unknown key {key:?}; a {kind} check takes {}",
            keys.join(", ")
        );
    }
    let check = CheckSpec::deserialize(&*fields)
        .map_err(|error| anyhow!("{what} is not a {kind} check: {error}"))?;
    let blank = match &check {
        CheckSpec::Command { command, .. } | CheckSpec::Until { command, .. } => {
            command.trim().is_empty().then_some("a command")
        }
        CheckSpec::Judge { condition, .. } => condition.trim().is_empty().then_some("a condition"),
        CheckSpec::Intent { .. } => None,
    };
    if let Some(missing) = blank {
        bail!("{what} needs {missing}");
    }
    Ok(check)
}

/// The checks `accept` (a list of `CheckSpec` objects), `accept_intent`
/// (whether the intent check joins them; default true) and
/// `accept_returns` (the most returns in a row to the child's worker)
/// give the child's task; `None` without `accept`.
fn spawn_acceptance(
    kwargs: &Map<String, Value>,
    operation: &str,
) -> anyhow::Result<Option<AcceptanceSeed>> {
    let given = |key: &str| kwargs.get(key).filter(|value| !value.is_null());
    let Some(accept) = given("accept") else {
        if let Some(key) = ["accept_intent", "accept_returns"]
            .into_iter()
            .find(|key| given(key).is_some())
        {
            bail!("{operation} {key} needs accept (the child's acceptance checks)");
        }
        return Ok(None);
    };
    let Value::Array(items) = accept else {
        bail!("{operation} accept must be a list of checks, e.g. [{{\"kind\": \"command\", \"command\": \"pytest -q\", \"expect\": 0}}]");
    };
    let checks = items
        .iter()
        .enumerate()
        .map(|(index, item)| spawn_check(index, item, operation))
        .collect::<anyhow::Result<Vec<_>>>()?;
    let intent = match given("accept_intent") {
        None => true,
        Some(Value::Bool(intent)) => *intent,
        Some(_) => bail!("{operation} accept_intent must be a bool"),
    };
    let max_returns =
        match given("accept_returns") {
            None => None,
            Some(value) => Some(value.as_u64().ok_or_else(|| {
                anyhow!("{operation} accept_returns must be a non-negative integer")
            })?),
        };
    let seed = AcceptanceSeed {
        checks,
        max_returns,
        intent,
    };
    if seed.specs().is_empty() {
        bail!("{operation} accept names no check: give a check, or leave accept_intent true");
    }
    Ok(Some(seed))
}
/// The spawn-name-unavailability error (TS
/// `formatAgentSessionNameUnavailable`).
pub(super) fn spawn_name_unavailable(name: &str, depth: u32) -> String {
    format!(
        "Agent name \"{name}\" is unavailable: an agent of that name already exists at depth {depth} under this parent"
    )
}
/// The message of a terminal child task that left no admitted child.
fn admission_failure(task_id: TaskId, state: &TaskState) -> Option<anyhow::Error> {
    let TaskState::Terminal { outcome } = state else {
        return None;
    };
    Some(match outcome {
        TaskOutcome::Failed { error, .. } | TaskOutcome::Faulted { error } => {
            anyhow!("{}", error.message)
        }
        TaskOutcome::Orphaned { reason } => anyhow!("{reason}"),
        TaskOutcome::Completed { .. } | TaskOutcome::Aborted { .. } => {
            anyhow!("RLM child task {task_id} ended before its child was created")
        }
    })
}

/// Wait until the `spawn` phase of `task_id` admitted its child (the row
/// leaves `spawning`) or the task ended without one.
async fn wait_for_admission(
    harness: &Harness,
    conversation_id: ConversationId,
    task_id: TaskId,
) -> anyhow::Result<ChildRow> {
    let changed = Arc::new(Notify::new());
    let watch = harness
        .watch_doc(&CHILDREN_DOC, conversation_id, &cx())
        .await
        .map_err(session_error)?;
    if let Some(watch) = &watch {
        let changed = Arc::clone(&changed);
        watch
            .start(Arc::new(move |_value, _ops, _cx| {
                changed.notify_one();
                futures::future::ready(Ok(())).boxed()
            }))
            .map_err(session_error)?;
    }
    let key = task_id.to_string();
    let outcome = loop {
        let mut state = read_children(harness, conversation_id, &cx())
            .await
            .map_err(session_error)?;
        if let Some(row) = state
            .children
            .swap_remove(&key)
            .filter(|row| row.status != ChildStatus::Spawning)
        {
            break Ok(row);
        }
        let record = harness
            .get_task(task_id, &cx())
            .await
            .map_err(session_error)?;
        if let Some(failure) = record.and_then(|record| admission_failure(task_id, &record.state)) {
            break Err(failure);
        }
        tokio::select! {
            () = changed.notified() => {}
            settled = harness.wait_for_task(task_id, &cx()) => {
                settled.map_err(session_error)?;
            }
        }
    };
    if let Some(watch) = watch {
        watch.stop().await;
    }
    outcome
}

// ---------------------------------------------------------------------------
// kwargs helpers
// ---------------------------------------------------------------------------

/// Present-but-non-string kwargs fail like the TS normalizers do.
fn optional_string_kwarg<'a>(
    kwargs: &'a Map<String, Value>,
    key: &str,
    operation: &str,
) -> anyhow::Result<Option<&'a str>> {
    match kwargs.get(key) {
        None | Some(Value::Null) => Ok(None),
        Some(Value::String(value)) => Ok(Some(value)),
        Some(_) => bail!("{operation} {key} must be a string"),
    }
}

fn reject_unsupported_kwargs(
    kwargs: &Map<String, Value>,
    operation: &str,
    supported: &[&str],
) -> anyhow::Result<()> {
    let mut unsupported: Vec<&str> = kwargs
        .keys()
        .map(String::as_str)
        .filter(|key| !supported.contains(key))
        .collect();
    if unsupported.is_empty() {
        return Ok(());
    }
    unsupported.sort_unstable();
    bail!("Unsupported {operation} kwargs: {}", unsupported.join(", "));
}
