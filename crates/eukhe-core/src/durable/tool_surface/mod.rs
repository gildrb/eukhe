//! The tool surface: the session's roster of tools is
//! fixed when it opens ([`eukhe_durable::harness::registry::Registry::fix_roster`]);
//! a tool that comes later (an MCP server's tool, a host tool that joins)
//! is reached through the one roster tool `dyn`, which lists the dynamic
//! tools and calls one by name with arguments. `report_issue`, the `AutoQA`
//! path, is one of them: an agent reports a tool that failed or did not do
//! what its description says, and the report is stored in the session as a
//! display-only row the user sees.

#[cfg(test)]
mod bridge;
#[cfg(test)]
mod tests;

use std::path::PathBuf;
use std::sync::{Arc, Mutex, PoisonError, Weak};

use eukhe_ai::typebox::{Options, TSchema, Type};
use eukhe_ai::utils::validation::validate_tool_arguments;
use eukhe_chord::context::Context;
use eukhe_durable::harness::define::define_tool;
use eukhe_durable::harness::types::{
    Extension, SubmissionDraft, ToolExecutionApi, ToolExecutionResult, ToolRegistration,
    WriteSubmissionDraft,
};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_types::pi_ai::{IndexMap, TextContent, ToolCall, UserContent, UserContentBlock};
use serde_json::{json, Value};

use super::entries::custom_entry_draft;
use super::tool_contract;
use super::HostDeps;
use crate::kernel::ReplKernelManager;

/// The extension name.
pub const DYN_EXTENSION: &str = "eukhe.dyn";

/// The roster tool that reaches the dynamic tools.
pub const DYN_TOOL_NAME: &str = "dyn";

/// The durable identity of `dyn`'s contract.
const DYN_VERSION: &str = "dyn@1";

/// The dynamic tool an agent reports a tool problem with.
pub const REPORT_ISSUE: &str = "report_issue";

/// The custom type of a reported tool issue's row (display-only).
pub const TOOL_ISSUE_CUSTOM_TYPE: &str = "eukhe.tool_issue";

/// The name prefix of an MCP server's tool: `mcp/<server>/<tool>`.
const MCP_PREFIX: &str = "mcp/";

/// How long one server may take to list or run a tool.
const MCP_TIMEOUT_MS: u64 = 30_000;

const DYN_DESCRIPTION: &str = "Reach the tools that are not in your tool list: \
the tools of the MCP servers the user configured (`mcp/<server>/<tool>`), tools \
that joined the session after it started, and `report_issue`. Call with no \
`name` to list them with their descriptions; call with `name` and `arguments` \
(an object) to run one. When a tool fails or does not do what its description \
says, call `report_issue` with arguments `tool` (its name) and `description` \
(what went wrong): the user sees the report.";

const REPORT_ISSUE_DESCRIPTION: &str = "Report a problem with a tool: it failed, \
or it did not do what its description says. Arguments: `tool` (the tool's name), \
`description` (what went wrong). The user sees the report.";

/// The session's dynamic tools: the host tools that joined after the roster
/// was fixed, by name, in join order. They are reached only through `dyn`;
/// none ever joins the roster.
#[derive(Clone, Default)]
pub struct ToolSurface {
    joined: Arc<Mutex<IndexMap<String, Arc<ToolRegistration>>>>,
}

impl ToolSurface {
    /// Make `tool` reachable through `dyn`; a joined tool with its name is
    /// replaced.
    pub fn join(&self, tool: Arc<ToolRegistration>) {
        self.joined
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .insert(tool.name.clone(), tool);
    }

    /// `dyn` no longer reaches the tool named `name`.
    pub fn quit(&self, name: &str) {
        self.joined
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .shift_remove(name);
    }

    /// The joined tool named `name`.
    #[must_use]
    pub fn tool(&self, name: &str) -> Option<Arc<ToolRegistration>> {
        self.joined
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .get(name)
            .cloned()
    }

    /// The joined tools, in join order.
    #[must_use]
    pub fn joined(&self) -> Vec<Arc<ToolRegistration>> {
        self.joined
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .values()
            .cloned()
            .collect()
    }
}

/// How a `dyn` call ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Outcome {
    Done,
    Failed,
}

/// A text result of `dyn` with `details`.
fn text_result(text: String, details: Value, outcome: Outcome) -> ToolExecutionResult {
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

/// The booted kernel manager of the calling conversation (booting it): the
/// session's MCP client runs in the kernel.
#[tracing::instrument(name = "dyn.kernel", skip_all)]
pub(crate) async fn kernel_manager(
    deps: &HostDeps,
    api: &dyn ToolExecutionApi,
    cx: &Context,
) -> Result<ReplKernelManager, String> {
    let pool = deps
        .rlm_kernels
        .get()
        .and_then(Weak::upgrade)
        .ok_or_else(|| "the session has no kernel".to_owned())?;
    let cwd = api
        .agent(cx)
        .await
        .map_err(|error| error.to_string())?
        .cwd
        .clone()
        .map_or_else(|| deps.cwd.clone(), PathBuf::from);
    let kernel = pool
        .kernel(api.conversation_id(), cwd)
        .map_err(|error| format!("{error:#}"))?;
    kernel
        .provisioner
        .ensure(None, None)
        .await
        .map_err(|error| format!("{error:#}"))
}

/// One `dyn` call: list the dynamic tools, or run the one named.
#[tracing::instrument(name = "dyn.call", skip_all)]
async fn call(
    deps: Arc<HostDeps>,
    params: Value,
    api: Arc<dyn ToolExecutionApi>,
    cx: Context,
) -> SessionResult<ToolExecutionResult> {
    let name = params.get("name").and_then(Value::as_str);
    let arguments = params
        .get("arguments")
        .and_then(Value::as_object)
        .cloned()
        .unwrap_or_default();
    let Some(name) = name else {
        let mut lines = vec![format!("{REPORT_ISSUE}: {REPORT_ISSUE_DESCRIPTION}")];
        let mut names = vec![REPORT_ISSUE.to_owned()];
        for tool in deps.tool_surface.joined() {
            lines.push(format!(
                "{}: {} Arguments: {}",
                tool.name,
                tool.description,
                tool.parameters.json()
            ));
            names.push(tool.name.clone());
        }
        if !deps.generic_mcp_servers.is_empty() {
            match kernel_manager(&deps, &*api, &cx).await {
                Ok(manager) => {
                    let listing = manager
                        .mcp_tool_listing(&deps.generic_mcp_servers, MCP_TIMEOUT_MS)
                        .await
                        .unwrap_or_default();
                    for connection in listing {
                        let server = connection["server"].as_str().unwrap_or_default();
                        if let Some(error) = connection["error"].as_str() {
                            lines.push(format!("MCP server {server} is unavailable: {error}"));
                        }
                        for tool in connection["tools"].as_array().into_iter().flatten() {
                            let name = format!(
                                "{MCP_PREFIX}{server}/{}",
                                tool["name"].as_str().unwrap_or_default()
                            );
                            lines.push(format!(
                                "{name}: {}",
                                tool["description"].as_str().unwrap_or_default()
                            ));
                            names.push(name);
                        }
                    }
                }
                Err(error) => lines.push(format!("The MCP servers are unavailable: {error}")),
            }
        }
        return Ok(text_result(
            lines.join("\n"),
            json!({ "version": DYN_VERSION, "tools": names }),
            Outcome::Done,
        ));
    };
    let details = json!({ "version": DYN_VERSION, "name": name });
    if name == REPORT_ISSUE {
        let field = |key: &str| {
            arguments
                .get(key)
                .and_then(Value::as_str)
                .map(str::trim)
                .filter(|text| !text.is_empty())
        };
        let (Some(tool), Some(description)) = (field("tool"), field("description")) else {
            return Ok(text_result(
                format!("{REPORT_ISSUE} needs the arguments `tool` and `description`, both text."),
                details,
                Outcome::Failed,
            ));
        };
        let entry = custom_entry_draft(
            TOOL_ISSUE_CUSTOM_TYPE,
            UserContent::Text(format!("Tool issue reported for {tool}: {description}")),
            true,
            Some(json!({ "tool": tool, "description": description })),
            super::rlm::now_millis(),
        )?;
        let harness = deps
            .harness
            .get()
            .ok_or_else(|| SessionError::error("the session is not open"))?;
        let Some(conversation) = harness.conversation(api.conversation_id(), &cx).await? else {
            return Err(SessionError::error(
                "the calling conversation does not exist",
            ));
        };
        conversation
            .submit(
                SubmissionDraft::Write(WriteSubmissionDraft {
                    request_id: None,
                    entry,
                }),
                &cx,
            )
            .await?;
        return Ok(text_result(
            format!("Recorded the issue with {tool}; the user sees it in the session."),
            details,
            Outcome::Done,
        ));
    }
    if let Some(path) = name.strip_prefix(MCP_PREFIX) {
        let Some((server, tool)) = path
            .split_once('/')
            .filter(|(server, _)| deps.generic_mcp_servers.iter().any(|known| known == server))
        else {
            return Ok(text_result(
                format!("No MCP server of this session has the tool {name}; call {DYN_TOOL_NAME} without a name to list them."),
                details,
                Outcome::Failed,
            ));
        };
        let called = match kernel_manager(&deps, &*api, &cx).await {
            Ok(manager) => {
                manager
                    .mcp_tool_call(server, tool, &Value::Object(arguments), MCP_TIMEOUT_MS)
                    .await
            }
            Err(error) => Err(error),
        };
        return Ok(match called {
            Ok(Value::String(text)) => text_result(text, details, Outcome::Done),
            Ok(value) => text_result(value.to_string(), details, Outcome::Done),
            Err(error) => text_result(format!("{name} failed: {error}"), details, Outcome::Failed),
        });
    }
    let Some(tool) = deps.tool_surface.tool(name) else {
        return Ok(text_result(
            format!("No dynamic tool is named {name}; call {DYN_TOOL_NAME} without a name to list them."),
            details,
            Outcome::Failed,
        ));
    };
    let declared = tool.tool();
    let arguments = match &tool.prepare_arguments {
        Some(prepare) => prepare(Value::Object(arguments))?,
        None => Value::Object(arguments),
    };
    let checked = validate_tool_arguments(
        &declared,
        &ToolCall {
            name: declared.name.clone(),
            arguments: arguments.as_object().cloned().unwrap_or_default(),
            ..ToolCall::default()
        },
    );
    match checked {
        Ok(arguments) => (tool.execute)(arguments, api, cx).await,
        Err(error) => Ok(text_result(
            format!("Invalid arguments for {name}: {error}"),
            details,
            Outcome::Failed,
        )),
    }
}

/// The `eukhe.dyn` extension: the `dyn` tool.
pub(crate) fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    let deps = Arc::downgrade(deps);
    let tool = ToolRegistration::new(
        DYN_TOOL_NAME,
        DYN_DESCRIPTION,
        tool_contract::parameters(
            1,
            [
                (
                    "name",
                    Type::optional(Type::string_with(
                        Options::new()
                            .set("description", "The dynamic tool to run; omit to list them."),
                    )),
                ),
                (
                    "arguments",
                    Type::optional(Type::object_with(
                        std::iter::empty::<(&str, TSchema)>(),
                        Options::new()
                            .set("additionalProperties", true)
                            .set("description", "The tool's arguments."),
                    )),
                ),
            ],
        ),
        move |params, api, cx| {
            let deps = deps.upgrade();
            async move {
                let deps = deps.ok_or_else(|| SessionError::error("the session is closed"))?;
                call(deps, params, api, cx).await
            }
        },
    );
    Arc::new(Extension {
        tools: vec![define_tool(tool)],
        ..Extension::named(DYN_EXTENSION)
    })
}
