//! Port of `test/harness-support.ts`, plus the registry and models every
//! harness test opens (`createRegistry()`, `createModels()`).

use std::sync::{Arc, LazyLock};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_pi_ai::models::{create_models as create_pi_models, CreateModelsOptions, Models};
use eukhe_pi_ai::typebox::{TSchema, Type};
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, IndexMap, Message, StopReason, SystemContent,
    SystemMessage, TextContent, ToolCall, ToolResultMessage, Usage, UserContent, UserContentBlock,
    UserMessage,
};
use futures::future::BoxFuture;

use crate::harness::define::{define_extension, define_tool, hook, section};
pub(crate) use crate::harness::registry::create_registry;
use crate::harness::registry::Registry;
use crate::harness::types::{
    BuiltinTasks, Extension, HarnessOptions, PromptInput, ReportFn, ToolExecutionResult,
    ToolRegistration,
};
use crate::harness::Harness;
use crate::session::SessionResult;
use crate::tasks::{AnyTask, Task, TaskValue};
use crate::types::Storage;

static CONTEXT: LazyLock<Context> = LazyLock::new(|| BACKGROUND_CONTEXT.clone());

/// The shared background context of every test (TS `session-support.ts`
/// `context`).
pub(crate) fn context() -> &'static Context {
    &CONTEXT
}

/// `GenerationTask` of the tests.
pub(crate) fn generation_task() -> &'static crate::harness::generation::GenerationTask {
    &crate::harness::generation::GENERATION_TASK
}

/// `ToolTask` of the tests.
pub(crate) fn tool_task() -> &'static crate::harness::tool::ToolTask {
    &crate::harness::tool::TOOL_TASK
}

/// `CompactionTask` of the tests.
pub(crate) fn compaction_task() -> &'static crate::harness::compaction::CompactionTask {
    &crate::harness::compaction::COMPACTION_TASK
}

/// The built-in tasks every test registry holds.
pub(crate) fn builtins() -> BuiltinTasks {
    BuiltinTasks::new()
}

/// TS `createModels()` without options.
pub(crate) fn create_models() -> Models {
    create_pi_models(CreateModelsOptions::default())
}

/// TS `Type.Object({})`.
pub(crate) fn empty_object_schema() -> TSchema {
    Type::object(Vec::<(String, TSchema)>::new())
}

/// TS `tool(name, description = `${name} tool`)`.
pub(crate) fn tool_described(name: &str, description: &str) -> Arc<ToolRegistration> {
    define_tool(ToolRegistration::new(
        name,
        description,
        empty_object_schema(),
        |_, _, _| async {
            Ok(ToolExecutionResult {
                output: Some(Vec::new()),
                ..ToolExecutionResult::default()
            })
        },
    ))
}

/// TS `tool(name)`.
pub(crate) fn tool(name: &str) -> Arc<ToolRegistration> {
    tool_described(name, &format!("{name} tool"))
}

/// Options of [`open_harness`].
#[derive(Default)]
pub(crate) struct OpenHarnessOptions {
    pub(crate) registry: Option<Registry>,
    pub(crate) on_report: Option<ReportFn>,
}

/// Open a Harness with a fresh registry holding the named tools.
pub(crate) async fn open_harness(
    storage: Arc<dyn Storage>,
    tool_names: &[&str],
    options: OpenHarnessOptions,
) -> SessionResult<(Harness, Registry)> {
    let registry = options.registry.unwrap_or_else(create_registry);
    if !tool_names.is_empty() {
        registry.install(define_extension(Extension {
            tools: tool_names.iter().map(|name| tool(name)).collect(),
            ..Extension::named("tools")
        }))?;
    }
    let mut harness_options = HarnessOptions::new(create_models(), Arc::new(registry.clone()));
    harness_options.on_report = options.on_report;
    let harness = Harness::open(storage, harness_options, context()).await?;
    Ok((harness, registry))
}

pub(crate) fn user(text: &str) -> UserMessage {
    UserMessage {
        content: UserContent::Text(text.to_owned()),
        timestamp: 1,
    }
}

/// Options of [`assistant`].
#[derive(Clone, Copy, Default)]
pub(crate) struct AssistantOptions<'a> {
    pub(crate) calls: &'a [&'a str],
    pub(crate) stop_reason: Option<StopReason>,
}

pub(crate) fn assistant(text: &str, options: AssistantOptions<'_>) -> AssistantMessage {
    let mut content = vec![AssistantContentBlock::Text(TextContent::new(text))];
    content.extend(options.calls.iter().map(|id| {
        AssistantContentBlock::ToolCall(ToolCall {
            id: (*id).to_owned(),
            name: format!("tool-{id}"),
            arguments: eukhe_types::pi_ai::JsonObject::new(),
            thought_signature: None,
            namespace: None,
        })
    }));
    AssistantMessage {
        content,
        api: "faux".to_owned(),
        provider: "faux".to_owned(),
        model: "faux".to_owned(),
        response_model: None,
        response_id: None,
        provider_thinking_level: None,
        thinking_level: None,
        diagnostics: None,
        usage: Usage::default(),
        stop_reason: options.stop_reason.unwrap_or(if options.calls.is_empty() {
            StopReason::Stop
        } else {
            StopReason::ToolUse
        }),
        deferred: None,
        error_message: None,
        raw_stop_reason: None,
        end_turn: None,
        timestamp: 2,
        duration_ms: None,
    }
}

pub(crate) fn tool_result(id: &str, text: Option<&str>) -> ToolResultMessage {
    let text = text.map_or_else(|| format!("result {id}"), str::to_owned);
    ToolResultMessage {
        tool_call_id: id.to_owned(),
        tool_name: format!("tool-{id}"),
        content: vec![UserContentBlock::Text(TextContent::new(text))],
        details: None,
        usage: None,
        nested_calls: None,
        is_error: false,
        timestamp: 3,
        duration_ms: None,
    }
}

pub(crate) fn system(sections: IndexMap<String, Option<String>>) -> SystemMessage {
    SystemMessage {
        content: SystemContent::from(""),
        sections: Some(sections),
        tools_added: None,
        tools_removed: None,
        timestamp: 4,
    }
}

fn first_text(blocks: &[UserContentBlock]) -> &str {
    blocks
        .iter()
        .find_map(|block| match block {
            UserContentBlock::Text(text) => Some(text.text.as_str()),
            UserContentBlock::Image(_) => None,
        })
        .unwrap_or("")
}

/// Compact message rendering for assertions.
pub(crate) fn describe_message(message: &Message) -> String {
    match message {
        Message::User(message) => match &message.content {
            UserContent::Text(text) => format!("user:{text}"),
            // TS `message.content as string` of an array: its `String()`.
            UserContent::Blocks(_) => "user:[object Object]".to_owned(),
        },
        Message::Assistant(message) => {
            let text = message
                .content
                .iter()
                .find_map(|block| match block {
                    AssistantContentBlock::Text(text) => Some(text.text.as_str()),
                    AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
                })
                .unwrap_or("");
            format!("assistant:{text}")
        }
        Message::ToolResult(message) => {
            let text = if message.is_error {
                "error"
            } else {
                first_text(&message.content)
            };
            format!("result:{}:{text}", message.tool_call_id)
        }
        Message::System(message) => {
            let keys: Vec<&str> = message
                .sections
                .iter()
                .flat_map(IndexMap::keys)
                .map(String::as_str)
                .collect();
            format!("system:{}", keys.join(","))
        }
    }
}

/// Uninstalls what one of the helpers below installed.
pub(crate) struct Installed {
    registry: Registry,
    extension: Arc<Extension>,
}

impl Installed {
    pub(crate) fn dispose(&self) {
        self.registry.uninstall(&self.extension);
    }
}

fn install_one(registry: &Registry, extension: Arc<Extension>) -> SessionResult<Installed> {
    registry.install(Arc::clone(&extension))?;
    Ok(Installed {
        registry: registry.clone(),
        extension,
    })
}

/// Install a one-tool extension named after the tool.
pub(crate) fn add_tool(
    registry: &Registry,
    tool: Arc<ToolRegistration>,
    name: Option<&str>,
) -> SessionResult<Installed> {
    let name = name.map_or_else(|| format!("tool:{}", tool.name), str::to_owned);
    install_one(
        registry,
        define_extension(Extension {
            tools: vec![tool],
            ..Extension::named(name)
        }),
    )
}

/// Install a one-task extension named after the task.
pub(crate) fn add_task(
    registry: &Registry,
    task: AnyTask,
    name: Option<&str>,
) -> SessionResult<Installed> {
    let name = name.map_or_else(|| format!("task:{}", task.name()), str::to_owned);
    install_one(
        registry,
        define_extension(Extension {
            tasks: vec![task],
            ..Extension::named(name)
        }),
    )
}

static HOOK_EXTENSIONS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// Install an extension with one hook registration for `task`.
pub(crate) fn add_hooks<I, S, R, H>(
    registry: &Registry,
    task: &Task<I, S, R, H>,
    handlers: H,
    name: Option<&str>,
) -> SessionResult<Installed>
where
    I: TaskValue,
    S: TaskValue,
    R: TaskValue,
    H: Send + Sync + 'static,
{
    let name = name.map_or_else(
        || {
            let next = HOOK_EXTENSIONS.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
            format!("hooks:{next}")
        },
        str::to_owned,
    );
    install_one(
        registry,
        define_extension(Extension {
            hooks: vec![hook(task, handlers)],
            ..Extension::named(name)
        }),
    )
}

/// Install a one-section extension named after the section.
pub(crate) fn add_section<F>(
    registry: &Registry,
    key: &str,
    render: F,
    tag: Option<bool>,
    name: Option<&str>,
) -> SessionResult<Installed>
where
    F: Fn(&PromptInput, &Context) -> BoxFuture<'static, SessionResult<Option<String>>>
        + Send
        + Sync
        + 'static,
{
    let name = name.map_or_else(|| format!("section:{key}"), str::to_owned);
    install_one(
        registry,
        define_extension(Extension {
            sections: vec![section(key, render, tag)],
            ..Extension::named(name)
        }),
    )
}
