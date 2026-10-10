//! Out-of-band kernel activity for the daemon's session lanes: the
//! `list/tail/kill_kernel_bash` commands (the kernel's bash handle
//! registry) and the `/factory` view's `factory_activity` lane. Both reach
//! a conversation's already-booted kernel without queueing behind a running
//! cell and never boot an idle one (the old session engine's
//! `bash_activity` / `factory_activity`).

use eukhe_chord::context::Context;
use eukhe_durable::harness::Conversation;
use eukhe_durable::types::ConversationId;
use eukhe_types::daemon::KERNEL_NOT_RUNNING_MESSAGE;
use serde_json::Value;

use super::super::HostDeps;
use crate::kernel::manager::ReplKernelManager;
use crate::refinement::{get_global_harness_state_dir, get_local_harness_state_dir};
use crate::session_engine::factory_host::{FactoryActivityRequest, FactoryHost, FactoryHostConfig};

/// One kernel bash activity action.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BashActivityAction {
    /// The kernel's bash handle catalog.
    List,
    /// The last `lines` output lines of one handle.
    Tail,
    /// Stop one handle.
    Kill,
}

impl BashActivityAction {
    /// The kernel frame's action name.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::List => "list",
            Self::Tail => "tail",
            Self::Kill => "kill",
        }
    }
}

/// A kernel bash activity request (`activity_id` names the handle for
/// `tail`/`kill`; `lines` bounds a `tail`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BashActivityRequest {
    pub action: BashActivityAction,
    pub activity_id: Option<String>,
    pub lines: usize,
}

/// Why a kernel activity request failed.
#[derive(Debug, thiserror::Error)]
pub enum KernelActivityError {
    /// The conversation has no booted kernel (or the session closed); the
    /// lanes answer this definitively, never booting one.
    #[error("{KERNEL_NOT_RUNNING_MESSAGE}")]
    NotRunning,
    /// The kernel refused or failed the request (validation, kernel reply,
    /// settle timeout).
    #[error("{0:#}")]
    Failed(anyhow::Error),
}

/// The running kernel manager of `conversation`, if its kernel booted.
fn running_manager(
    deps: &HostDeps,
    conversation: ConversationId,
) -> Result<ReplKernelManager, KernelActivityError> {
    deps.rlm_kernels
        .get()
        .and_then(std::sync::Weak::upgrade)
        .and_then(|pool| pool.existing(conversation))
        .and_then(|kernel| kernel.provisioner.manager())
        .ok_or(KernelActivityError::NotRunning)
}

/// Release `conversation`'s settled kernel (TS #2483's
/// `canPassivateSettledSession`, worker-side): the kernel is disposed with
/// a namespace snapshot, and the conversation's next kernel use revives it
/// from that snapshot. `false` when the conversation has no kernel or the
/// session closed. Best-effort by design: the roster, collect, and delete
/// surfaces stay untouched.
pub async fn release_settled_kernel(deps: &HostDeps, conversation: ConversationId) -> bool {
    match deps.rlm_kernels.get().and_then(std::sync::Weak::upgrade) {
        Some(pool) => pool.release(conversation).await,
        None => false,
    }
}

/// The manager's "Kernel is not running" (a kernel that died since the
/// lookup) stays the definitive refusal; anything else is a failure.
fn classify(error: anyhow::Error) -> KernelActivityError {
    if error.to_string() == KERNEL_NOT_RUNNING_MESSAGE {
        KernelActivityError::NotRunning
    } else {
        KernelActivityError::Failed(error)
    }
}

/// Run one bash activity request on `conversation`'s kernel.
///
/// # Errors
///
/// [`KernelActivityError::NotRunning`] without a booted kernel, else the
/// kernel's own refusal or failure.
pub async fn kernel_bash_activity(
    deps: &HostDeps,
    conversation: ConversationId,
    request: BashActivityRequest,
) -> Result<Value, KernelActivityError> {
    let manager = running_manager(deps, conversation)?;
    manager
        .bash_activity(
            request.action.as_str(),
            request.activity_id.as_deref(),
            request.lines,
        )
        .await
        .map_err(classify)
}

/// Run one validated factory activity request on `conversation`'s kernel.
/// A `run` is preflighted first, as the old session engine did: every
/// model its spec declares must resolve through the credential-backed
/// catalog, sit inside the allowlist pin, and carry request auth, so a
/// doomed run fails before any child spawns.
///
/// # Errors
///
/// The `run` preflight's refusal, [`KernelActivityError::NotRunning`]
/// without a booted kernel, else the kernel's own refusal or failure.
pub async fn kernel_factory_activity(
    deps: &HostDeps,
    conversation: &Conversation,
    request: FactoryActivityRequest,
    cx: &Context,
) -> Result<Value, KernelActivityError> {
    if request.action == "run" {
        let spec_id = request.spec_id.clone().ok_or_else(|| {
            KernelActivityError::Failed(anyhow::anyhow!("factory activity run requires specId"))
        })?;
        let host = factory_host(deps, conversation, cx)
            .await
            .map_err(KernelActivityError::Failed)?;
        // The preflight reads harness states, the model catalog, and auth
        // caches from disk: blocking work off the executor.
        tokio::task::spawn_blocking(move || host.preflight_run(&spec_id))
            .await
            .map_err(|join| {
                KernelActivityError::Failed(anyhow::anyhow!(
                    "factory run preflight join failed: {join}"
                ))
            })?
            .map_err(KernelActivityError::Failed)?;
    }
    let manager = running_manager(deps, conversation.id())?;
    manager
        .factory_activity(
            request.action,
            request.run_id.as_deref(),
            request.spec_id.as_deref(),
            request.timeout_ms,
        )
        .await
        .map_err(classify)
}

/// The factory preflight host of `conversation`: the session's harness
/// directories, the conversation's current model, and the allowlist pin.
async fn factory_host(
    deps: &HostDeps,
    conversation: &Conversation,
    cx: &Context,
) -> anyhow::Result<FactoryHost> {
    let agent = conversation.agent(cx).await?;
    let session_model = agent
        .model
        .as_ref()
        .and_then(|model| deps.models.get_model(&model.provider, &model.model_id))
        .map(|model| descriptor(&model));
    Ok(FactoryHost::new(FactoryHostConfig {
        agent_dir: deps.agent_dir.clone(),
        global_harness_dir: get_global_harness_state_dir(&deps.agent_dir),
        local_harness_dir: get_local_harness_state_dir(deps.storage_dir.as_deref()),
        session_model,
        allowed_models: deps.settings.manager().get_allowed_models(),
    }))
}

/// The agent-side model descriptor the preflight's session-model fallback
/// reads (provider and id select it; the rest is carried over field by
/// field).
fn descriptor(model: &eukhe_types::pi_ai::Model) -> eukhe_agent::types::Model {
    eukhe_agent::types::Model {
        id: model.id.clone(),
        name: model.name.clone(),
        api: model.api.clone(),
        provider: model.provider.clone(),
        base_url: model.base_url.clone(),
        reasoning: model.reasoning,
        cost: eukhe_agent::types::UsageCost {
            input: model.cost.input,
            output: model.cost.output,
            cache_read: model.cost.cache_read,
            cache_write: model.cost.cache_write,
            ..eukhe_agent::types::UsageCost::default()
        },
        context_window: model.context_window,
        max_tokens: model.max_tokens,
        // pi-ai models carry no explicit flag (pi-ai applies no output
        // ceiling); this descriptor never sizes a request.
        max_tokens_explicit: false,
    }
}
