//! One Python kernel per conversation: the provisioner pool, its namespace
//! snapshot directories under the session storage, the boot notices
//! (`ipython_state_restored`, `python_skills_unavailable`) a boot owes the
//! model, and the per-request host dispatch with the durable call context.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::{Arc, Mutex, PoisonError, Weak};

use eukhe_durable::harness::types::{SubmissionDraft, WriteSubmissionDraft};
use eukhe_durable::types::ConversationId;
use serde_json::{json, Value};

use super::super::{HostCall, HostDeps};
use super::CustomNotice;
use crate::kernel::bootstrap::UnavailablePythonSkills;
use crate::kernel::provisioner::{
    IpythonKernelProvisioner, IpythonKernelProvisionerOptions, RestoreCallback,
    UnavailableSkillsCallback,
};
use crate::kernel::shared::{
    host_request_unavailable, HostHandlerFuture, HostRequestHandlers, HostRequestPayload,
    KernelHostDispatch, KernelHostRequest, KernelShutdownOptions,
};
use crate::kernel::state_snapshot::{snapshot_path_in, RestoreResult};
use crate::session_engine::{skills_unavailable_notice, state_restore_notice};

/// Bound on the background MCP settle after a prewarm boot (one wedged
/// server must not keep the settle task alive forever).
const MCP_SETTLE_PER_SERVER_TIMEOUT_MS: u64 = 10_000;

/// Directory under the session storage holding each conversation's kernel
/// snapshot (`kernel-state.dill` + manifest) and stderr log.
const KERNELS_DIR: &str = "kernels";

/// The kernel interpreter of this crate's tests (the old kernel tests pass
/// `EUKHE_KERNEL_PYTHON` to their own processes; the lib test binary is
/// shared, so its sessions take the interpreter from here instead of the
/// process environment).
#[cfg(test)]
pub(crate) static TEST_KERNEL_PYTHON: std::sync::OnceLock<PathBuf> = std::sync::OnceLock::new();

/// The kernel interpreter: the auto-bootstrapped kernel venv (or the
/// `EUKHE_KERNEL_PYTHON` override) in product builds.
fn kernel_python() -> Option<PathBuf> {
    #[cfg(test)]
    {
        TEST_KERNEL_PYTHON.get().cloned()
    }
    #[cfg(not(test))]
    {
        None
    }
}

fn lock<T>(mutex: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// The kernel of one conversation and the boot notices it still owes.
#[derive(Clone)]
pub(crate) struct ConversationKernel {
    pub(crate) provisioner: IpythonKernelProvisioner,
    notices: Arc<Mutex<Vec<CustomNotice>>>,
}

impl ConversationKernel {
    /// Take the boot notices not delivered yet (each is delivered once).
    pub(crate) fn take_notices(&self) -> Vec<CustomNotice> {
        std::mem::take(&mut *lock(&self.notices))
    }
}

/// The `ipython_state_restored` row for a boot that revived a snapshot
/// (the old engine's `state_restore_notice::notice_message`).
fn restored_notice(result: &RestoreResult) -> CustomNotice {
    CustomNotice::new(
        state_restore_notice::IPYTHON_STATE_RESTORED_CUSTOM_TYPE,
        state_restore_notice::notice_content(result),
        true,
        Some(json!({ "restored": !result.restored.is_empty() })),
    )
}

/// The `python_skills_unavailable` row for a boot whose skill imports
/// failed (the old engine's `skills_unavailable_notice::notice_message`).
fn skills_notice(errors: &UnavailablePythonSkills) -> CustomNotice {
    let message = skills_unavailable_notice::notice_message(errors);
    CustomNotice::new(
        message.custom_type,
        skills_unavailable_notice::notice_content(errors),
        message.display,
        message.details,
    )
}

/// The per-conversation kernels of one session.
pub(crate) struct KernelPool {
    deps: Weak<HostDeps>,
    kernels: Mutex<HashMap<ConversationId, ConversationKernel>>,
}

impl KernelPool {
    pub(crate) fn new(deps: &Arc<HostDeps>) -> Self {
        Self {
            deps: Arc::downgrade(deps),
            kernels: Mutex::new(HashMap::new()),
        }
    }

    /// The snapshot directory of `conversation_id`'s kernel; `None` for
    /// memory storage (nothing to revive from).
    pub(crate) fn snapshot_dir(
        deps: &HostDeps,
        conversation_id: ConversationId,
    ) -> Option<PathBuf> {
        deps.storage_dir
            .as_ref()
            .map(|dir| dir.join(KERNELS_DIR).join(conversation_id.to_string()))
    }

    /// The kernel of `conversation_id` when one was created (never creates
    /// or boots one).
    pub(crate) fn existing(&self, conversation_id: ConversationId) -> Option<ConversationKernel> {
        lock(&self.kernels).get(&conversation_id).cloned()
    }

    /// The kernel of `conversation_id`, created (not booted) on first use in
    /// `cwd`.
    ///
    /// # Errors
    ///
    /// The session closed, or the snapshot directory cannot be created.
    pub(crate) fn kernel(
        &self,
        conversation_id: ConversationId,
        cwd: PathBuf,
    ) -> anyhow::Result<ConversationKernel> {
        let mut kernels = lock(&self.kernels);
        if let Some(kernel) = kernels.get(&conversation_id) {
            return Ok(kernel.clone());
        }
        let deps = self
            .deps
            .upgrade()
            .ok_or_else(|| anyhow::anyhow!("the session is closed"))?;
        let snapshot_dir = Self::snapshot_dir(&deps, conversation_id);
        if let Some(dir) = &snapshot_dir {
            std::fs::create_dir_all(dir).map_err(|error| {
                anyhow::anyhow!("cannot create kernel directory {}: {error}", dir.display())
            })?;
        }
        let notices: Arc<Mutex<Vec<CustomNotice>>> = Arc::default();
        let on_restore: RestoreCallback = {
            let notices = Arc::clone(&notices);
            Arc::new(move |result: &RestoreResult| {
                lock(&notices).push(restored_notice(result));
            })
        };
        let on_unavailable_skills: UnavailableSkillsCallback = {
            let notices = Arc::clone(&notices);
            Arc::new(move |errors: &UnavailablePythonSkills| {
                lock(&notices).push(skills_notice(errors));
            })
        };
        let mut env = HashMap::with_capacity(2);
        env.insert(
            "EUKHE_CODING_AGENT_DIR".to_string(),
            deps.agent_dir.to_string_lossy().to_string(),
        );
        // A chat-memory session remembers through the chat: the kernel's
        // `rlm.harness` holds tools only.
        if deps.memory.is_some() {
            env.insert("EUKHE_CHAT_MEMORY".to_string(), "1".to_string());
        }
        let dispatch = Arc::new(RegistryDispatch {
            registry: deps.host_requests.clone(),
            extra: deps.extra_host_handlers.clone(),
        });
        let provisioner = IpythonKernelProvisioner::new(
            cwd,
            IpythonKernelProvisionerOptions {
                python: kernel_python(),
                env,
                session_id: Some(deps.session_id.clone()),
                host_handlers: HostRequestHandlers::with_dispatch(dispatch),
                python_skills: deps.python_skills.clone(),
                snapshot_dir,
                on_restore: Some(on_restore),
                on_unavailable_skills: Some(on_unavailable_skills),
                ..IpythonKernelProvisionerOptions::default()
            },
        );
        let kernel = ConversationKernel {
            provisioner,
            notices,
        };
        kernels.insert(conversation_id, kernel.clone());
        Ok(kernel)
    }

    /// Boot `conversation_id`'s kernel in the background when its snapshot
    /// exists (a resumed session revives its namespace before the first
    /// turn), then settle the generic MCP servers and hand the boot notices
    /// to the conversation as write submissions (placed at once when idle,
    /// otherwise at the next boundary).
    pub(crate) fn prewarm(self: &Arc<Self>, conversation_id: ConversationId) {
        let Some(deps) = self.deps.upgrade() else {
            return;
        };
        let has_snapshot = Self::snapshot_dir(&deps, conversation_id)
            .is_some_and(|dir| snapshot_path_in(&dir).exists());
        if !has_snapshot {
            return;
        }
        let Ok(kernel) = self.kernel(conversation_id, deps.cwd.clone()) else {
            return;
        };
        let servers = deps.generic_mcp_servers.clone();
        let harness = deps.harness.clone();
        drop(deps);
        tokio::spawn(async move {
            // A failed boot surfaces on the next ipython call's ensure().
            if kernel.provisioner.ensure(None, None).await.is_err() {
                return;
            }
            let cx = eukhe_chord::context::BACKGROUND_CONTEXT.clone();
            if let Some(harness) = harness.get() {
                for notice in kernel.take_notices() {
                    if let Err(error) = submit_notice(&harness, conversation_id, &notice, &cx).await
                    {
                        tracing::warn!(%error, "kernel boot notice not delivered");
                    }
                }
            }
            if let Some(manager) = kernel.provisioner.manager() {
                let _ = manager
                    .mcp_tool_listing(&servers, MCP_SETTLE_PER_SERVER_TIMEOUT_MS)
                    .await;
            }
        });
    }

    /// Dispose every kernel, flushing a final namespace snapshot (session
    /// close).
    pub(crate) async fn dispose_all(&self) {
        let kernels: Vec<ConversationKernel> =
            lock(&self.kernels).drain().map(|(_, k)| k).collect();
        for kernel in kernels {
            kernel
                .provisioner
                .dispose(Some(KernelShutdownOptions {
                    snapshot: true,
                    drain_host_requests: true,
                }))
                .await;
        }
    }
}

async fn submit_notice(
    harness: &eukhe_durable::harness::Harness,
    conversation_id: ConversationId,
    notice: &CustomNotice,
    cx: &eukhe_chord::context::Context,
) -> anyhow::Result<()> {
    let entry = notice.draft()?;
    let Some(conversation) = harness.conversation(conversation_id, cx).await? else {
        anyhow::bail!("conversation {conversation_id} does not exist");
    };
    conversation
        .submit(
            SubmissionDraft::Write(WriteSubmissionDraft {
                request_id: None,
                entry,
            }),
            cx,
        )
        .await?;
    Ok(())
}

/// Kernel host requests answered through the session's
/// [`super::super::HostRequestRegistry`] (looked up per request, with the
/// durable call), then the embedding's extra handlers.
struct RegistryDispatch {
    registry: super::super::HostRequestRegistry,
    extra: Option<HostRequestHandlers>,
}

impl KernelHostDispatch for RegistryDispatch {
    fn dispatch(&self, request: KernelHostRequest) -> HostHandlerFuture {
        let KernelHostRequest {
            request_type,
            data,
            cell_source_code,
            call,
        } = request;
        if let Some(handler) = self.registry.get(&request_type) {
            return handler(HostCall {
                data,
                cell_source_code,
                call,
            });
        }
        if let Some(handler) = self
            .extra
            .as_ref()
            .and_then(|extra| extra.get(&request_type))
        {
            return handler(HostRequestPayload {
                data,
                cell_source_code: None,
            });
        }
        let error = host_request_unavailable(&request_type);
        Box::pin(async move { Err::<Value, _>(error) })
    }
}
