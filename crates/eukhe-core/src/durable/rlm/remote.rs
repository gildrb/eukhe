//! `@remote` (docs/runtime.md S3): a Python function of the kernel that the
//! host offers as a dynamic tool.
//!
//! The runtime's `@remote` decorator announces the function with the
//! `remote.register` host request: its tool name, the module and qualified
//! name the kernel calls it by, its docstring and the JSON schema of its
//! keyword arguments. The session joins it to the tool surface as
//! `remote/<name>`, reached only through `dyn` (S7: a dynamic tool never
//! enters the roster). A call resolves the calling conversation's kernel
//! and sends it a `call` request ([`ReplKernelManager::remote_call`]),
//! bounded by the session's blocking budget (S2); the `dyn` call's result
//! keeps S2's output limits. A function that fails, hangs or is not in that
//! kernel answers a typed error, and the kernel keeps serving.
//!
//! [`ReplKernelManager::remote_call`]: crate::kernel::ReplKernelManager::remote_call

use std::sync::{Arc, Weak};

use eukhe_durable::harness::types::{ToolExecutionResult, ToolRegistration};
use eukhe_types::pi_ai::{TextContent, ToolSchema, UserContentBlock};
use futures::FutureExt;
use serde::Deserialize;
use serde_json::{json, Value};

use super::super::{HostCall, HostDeps};
use super::RlmRuntime;
use crate::durable::tool_surface::kernel_manager;

/// The name prefix of a `@remote` function's dynamic tool.
pub(crate) const REMOTE_PREFIX: &str = "remote/";

/// The identity of a `@remote` tool's result details.
const REMOTE_VERSION: &str = "remote@1";

/// One `remote.register` request: the runtime's announcement of a
/// function.
#[derive(Debug, Clone, Deserialize)]
struct Announcement {
    name: String,
    module: String,
    function: String,
    description: String,
    parameters: Value,
}

/// Register `remote.register`: each announced function joins the tool
/// surface (replacing a same-named one).
pub(super) fn register(runtime: &Arc<RlmRuntime>) {
    let weak: Weak<HostDeps> = Arc::downgrade(&runtime.deps);
    runtime.deps.host_requests.register(
        "remote.register",
        Arc::new(move |call: HostCall| {
            let weak = weak.clone();
            async move {
                let deps = weak.upgrade().ok_or_else(|| {
                    anyhow::anyhow!("the session ended before the request could be served")
                })?;
                let announcement: Announcement = serde_json::from_value(call.data)
                    .map_err(|error| anyhow::anyhow!("remote.register: {error}"))?;
                anyhow::ensure!(
                    announcement.parameters.get("type").and_then(Value::as_str) == Some("object"),
                    "remote.register: parameters must be an object schema"
                );
                let tool = remote_tool(Arc::downgrade(&deps), announcement);
                let name = tool.name.clone();
                deps.tool_surface.join(Arc::new(tool));
                Ok(json!({ "tool": name }))
            }
            .boxed()
        }),
    );
}

/// The dynamic tool of one announced function.
fn remote_tool(deps: Weak<HostDeps>, announcement: Announcement) -> ToolRegistration {
    let Announcement {
        name,
        module,
        function,
        description,
        parameters,
    } = announcement;
    let tool_name = format!("{REMOTE_PREFIX}{name}");
    let description = if description.trim().is_empty() {
        format!("The kernel's Python function {module}.{function} (@remote).")
    } else {
        format!("{description} (the kernel's Python function {module}.{function}, @remote)")
    };
    let called = tool_name.clone();
    ToolRegistration::new(
        tool_name,
        description,
        ToolSchema::from(parameters),
        move |args: Value, api, cx| {
            let deps = deps.clone();
            let module = module.clone();
            let function = function.clone();
            let called = called.clone();
            async move {
                let details = json!({ "version": REMOTE_VERSION, "name": called });
                let Some(deps) = deps.upgrade() else {
                    return Ok(result(
                        format!("{called} failed: the session is closed"),
                        details,
                        Outcome::Failed,
                    ));
                };
                let budget_ms =
                    u64::try_from(deps.blocking_budget().as_millis()).unwrap_or(u64::MAX);
                let called_back = match kernel_manager(&deps, &*api, &cx).await {
                    Ok(manager) => manager
                        .remote_call(&module, &function, &args, budget_ms)
                        .await
                        .map_err(|error| error.to_string()),
                    Err(error) => Err(error),
                };
                Ok(match called_back {
                    Ok(Value::String(text)) => result(text, details, Outcome::Done),
                    Ok(value) => result(value.to_string(), details, Outcome::Done),
                    Err(error) => result(
                        format!("{called} failed: {error}"),
                        details,
                        Outcome::Failed,
                    ),
                })
            }
        },
    )
}

/// How a `@remote` call ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Outcome {
    Done,
    Failed,
}

fn result(text: String, details: Value, outcome: Outcome) -> ToolExecutionResult {
    ToolExecutionResult {
        output: Some(vec![UserContentBlock::Text(TextContent::new(text))]),
        is_error: match outcome {
            Outcome::Done => None,
            Outcome::Failed => Some(true),
        },
        details: Some(details.into()),
        ..ToolExecutionResult::default()
    }
}
