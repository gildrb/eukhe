//! Port of `test/spec-usage.test.ts`: the usage examples of `docs/spec.md`,
//! compile-checked. Each block is copied as written apart from Rust
//! spelling, with the names the spec leaves to the application supplied by
//! [`App`]. `examples` is never called: the test only requires it to
//! compile, as the TS test only type-checks it.

use std::sync::{Arc, LazyLock, OnceLock};
use std::time::Instant;

use eukhe_chord::context::Context;
use eukhe_chord::json::JsonValue;
use eukhe_chord::Draft;
use eukhe_durable::documents::{ConversationDoc, DocDefinition};
use eukhe_durable::env::ExecutionEnv;
use eukhe_durable::harness::agent::configure;
use eukhe_durable::harness::define::{define_extension, define_tool, hook, section, wrap_tool};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    AgentChange, BeforeToolDecision, ConversationStreamOptions, EnvFactory, EnvTarget, Extension,
    ExtensionsChange, FieldChange, GenerationHooks, HarnessOptions, HarnessSettings,
    HarnessSettingsSource, HookApi, HookFuture, InputSubmissionDraft, LiveSettings, ModelRef,
    PartialCompactionPolicy, ToolExecutionApi, ToolExecutionApiExt, ToolExecutionResult, ToolHooks,
    ToolRegistration, ToolReplay, ToolsChange, YieldContinuation,
};
use eukhe_durable::harness::{Harness, RootOptions, GENERATION_TASK, LIVE_DOC, TOOL_TASK};
use eukhe_durable::session::{Session, SessionError, SessionResult, Tx};
use eukhe_durable::tasks::{define_task, NextTaskState, Task, TaskDefinition};
use eukhe_durable::tools::{
    create_bash_tool, create_edit_tool, create_read_tool, BashToolOptions, CODING_TOOLS,
};
use eukhe_durable::types::{
    ConversationId, ConversationOwnership, ConversationQuery, DocumentReaderExt, EntryDraft,
    EntryId, InputSubmission, LatestFork, Storage, SubmissionState, TaskId, TaskOptions,
    TaskOutcome, TaskOwnership,
};
use eukhe_pi_ai::models::Models;
use eukhe_pi_ai::typebox::Type;
use eukhe_types::pi_ai::{AssistantMessage, TextContent, ToolCall, UserContentBlock};
use futures::future::{BoxFuture, FutureExt};
use serde::{Deserialize, Serialize};

// ─── Names the spec leaves to the application ────────────────────────────────

/// A payment receipt (`payments.charge()` result).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
struct Receipt {
    id: String,
}

/// The user's settings store (TS `SettingsManager`; its overloaded `get` by
/// key is one method per key). Implementations read and write live values.
trait SettingsManager: Send + Sync {
    fn get_timeout_ms(&self) -> f64;
    fn get_auto_compact(&self) -> bool;
    fn set_auto_compact(&self, value: bool);
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase")]
enum Hold {
    #[serde(rename = "hold")]
    Hold,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase")]
enum Report {
    #[serde(rename = "report")]
    Report,
}

/// The values and functions the spec declares but never defines (TS
/// `declare const` / `declare function`). Implementations are the host
/// application's.
trait App: Send + Sync + 'static {
    fn context(&self) -> Context;
    fn storage(&self) -> Arc<dyn Storage>;
    fn models(&self) -> Models;
    fn session(&self) -> Session;
    fn conversation_id(&self) -> ConversationId;
    fn message(&self) -> EntryDraft;
    fn haiku(&self) -> ModelRef;
    fn sonnet(&self) -> ModelRef;
    fn worktree(&self) -> String;
    fn name(&self) -> String;
    fn local_env(&self, cwd: &str) -> Arc<dyn ExecutionEnv>;
    fn container_env(
        &self,
        image: &str,
        cwd: &str,
        context: &Context,
    ) -> BoxFuture<'static, SessionResult<Arc<dyn ExecutionEnv>>>;
    fn render_agents_md(&self) -> Option<String>;
    fn render_skills(&self) -> Option<String>;
    fn is_dangerous(&self, call: &ToolCall) -> bool;
    fn writes(&self, call: &ToolCall) -> bool;
    fn request_second_pass(
        &self,
        answer: &AssistantMessage,
        api: &HookApi,
        context: &Context,
    ) -> HookFuture<YieldContinuation>;
    fn record_metric(&self, name: &str, ms: f64);
    fn answer_text(
        &self,
        api: Arc<dyn ToolExecutionApi>,
        entry: EntryId,
        context: &Context,
    ) -> BoxFuture<'static, SessionResult<String>>;
    fn charge(&self, key: &str) -> BoxFuture<'static, SessionResult<Receipt>>;
    fn cancel(&self, checkpoint: &Charge) -> BoxFuture<'static, SessionResult<()>>;
    fn new_key(&self) -> String;
    fn receipt_entry(&self, receipt: &Receipt) -> EntryDraft;
    fn manager(&self) -> Arc<dyn SettingsManager>;
    fn anchor(&self) -> Task<(), Hold, (), ()>;
    fn reporter(&self) -> Task<(), Report, (), ()>;
    fn subagent_tool(&self) -> Arc<ToolRegistration>;
}

/// TS `section(key, () => text)`.
fn text_section(
    key: &str,
    render: impl Fn() -> Option<String> + Send + Sync + 'static,
    tag: Option<bool>,
) -> Arc<eukhe_durable::harness::types::PromptSection> {
    section(
        key,
        move |_input, _context| {
            let text = render();
            async move { Ok(text) }.boxed()
        },
        tag,
    )
}

fn current_dir() -> SessionResult<String> {
    Ok(std::env::current_dir()
        .map_err(SessionError::other)?
        .to_string_lossy()
        .into_owned())
}

// ─── Section 5.1 types ───────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
enum Charge {
    Prepare,
    Charge { key: String },
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct PaymentResult {
    entry_id: EntryId,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase")]
enum Follow {
    #[serde(rename = "follow")]
    Follow,
}

/// TS `object` input `{}`.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
struct EmptyObject {}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
struct PlanModeState {
    enabled: bool,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
struct ContainerState {
    image: String,
}

static PLAN_MODE_DOC: LazyLock<ConversationDoc<PlanModeState>> = LazyLock::new(|| {
    ConversationDoc::define(
        DocDefinition {
            kind: "app.plan-mode",
            version: 1,
            initial: || PlanModeState { enabled: false },
            migrate: None,
            checkpoint_when: None,
        },
        LatestFork::Current,
    )
    .expect("a valid definition")
});

// ─── Sequences ───────────────────────────────────────────────────────────────

/// One sequence of the spec: an async block over its arguments.
type Sequence<A, T> = Box<dyn Fn(A) -> BoxFuture<'static, SessionResult<T>> + Send + Sync>;

struct Sequences {
    /// Section 2.2: a tool's commit creates a configured child.
    child_in_tool_commit: Sequence<(Tx, TaskId), ()>,
    /// Section 2.2: settings read live through getters.
    live_settings: Box<dyn Fn() -> Arc<dyn HarnessSettingsSource> + Send + Sync>,
    /// Section 2.2: an environment per conversation.
    container_env: Sequence<(), Harness>,
    /// Sections 2.2 and 7.1: host setup, tool filters, extension selection, plan mode, and reload.
    host: Sequence<(), Harness>,
    /// Section 7.3: a named subagent's spawn commit.
    spawn: Sequence<Tx, ()>,
    /// Section 4: table reads before the first table write; documents stay usable.
    table_rules: Sequence<(), ()>,
    /// Section 3.4: drafts are revoked after their commit.
    revoked_draft: Sequence<(), ()>,
}

struct Examples {
    sequences: Sequences,
    payment: Task<(), Charge, PaymentResult, ()>,
}

/// The user's settings, read live through getters.
struct UserSettings {
    manager: Arc<dyn SettingsManager>,
}

impl HarnessSettingsSource for UserSettings {
    fn current(&self) -> Arc<HarnessSettings> {
        Arc::new(HarnessSettings {
            stream: Some(ConversationStreamOptions {
                timeout_ms: Some(self.manager.get_timeout_ms()),
                ..ConversationStreamOptions::default()
            }),
            compaction: Some(PartialCompactionPolicy {
                enabled: Some(self.manager.get_auto_compact()),
                ..PartialCompactionPolicy::default()
            }),
            ..HarnessSettings::default()
        })
    }
}

/// Never called: the declared names have no values.
#[expect(clippy::too_many_lines, reason = "one TS function, ported whole")]
fn examples(app: &Arc<dyn App>) -> Examples {
    let app = Arc::clone(app);
    let read_tool = create_read_tool();
    let edit_tool = create_edit_tool();
    let bash_tool = create_bash_tool(BashToolOptions::default());

    // ─── Section 7.1: extensions and host setup ──────────────────────────────────

    let context_files = {
        let app = Arc::clone(&app);
        define_extension(Extension {
            name: "context-files".to_owned(),
            sections: vec![text_section(
                "agents-md",
                move || app.render_agents_md(),
                None,
            )],
            ..Extension::default()
        })
    };
    let skills = {
        let app = Arc::clone(&app);
        define_extension(Extension {
            name: "skills".to_owned(),
            sections: vec![text_section("skills", move || app.render_skills(), None)],
            ..Extension::default()
        })
    };
    let skills_v2 = {
        let app = Arc::clone(&app);
        define_extension(Extension {
            name: "skills".to_owned(),
            sections: vec![text_section("skills", move || app.render_skills(), None)],
            ..Extension::default()
        })
    };
    let coding = define_extension(Extension {
        name: "coding".to_owned(),
        sections: vec![
            text_section(
                "preamble",
                || Some("You are an expert coding assistant.".to_owned()),
                Some(false),
            ),
            // The environment the host built for this conversation, in the conversation's directory.
            section(
                "cwd",
                |input, _context| {
                    let text = input
                        .env
                        .as_ref()
                        .map(|env| format!("Working directory: {}", env.cwd()));
                    async move { Ok(text) }.boxed()
                },
                None,
            ),
        ],
        ..Extension::default()
    });
    let permissions = {
        let app = Arc::clone(&app);
        define_extension(Extension {
            name: "permissions".to_owned(),
            hooks: vec![hook(
                &TOOL_TASK,
                ToolHooks {
                    before_tool: Some(Arc::new(move |call, _api, _context| {
                        let decision = app.is_dangerous(call).then(|| BeforeToolDecision {
                            block: Some("Needs approval".to_owned()),
                            ..BeforeToolDecision::default()
                        });
                        async move { Ok(decision) }.boxed()
                    })),
                    ..ToolHooks::default()
                },
            )],
            ..Extension::default()
        })
    };
    // A role and a review loop, for conversations that select it.
    let reviewer = {
        let app = Arc::clone(&app);
        define_extension(Extension {
            name: "reviewer".to_owned(),
            sections: vec![text_section(
                "role",
                || {
                    Some(
                        "You review diffs. Report problems as a list. Never edit files.".to_owned(),
                    )
                },
                None,
            )],
            hooks: vec![hook(
                &GENERATION_TASK,
                GenerationHooks {
                    on_yield: Some(Arc::new(move |answer, api, context| {
                        app.request_second_pass(answer, api, context)
                    })),
                    ..GenerationHooks::default()
                },
            )],
            ..Extension::default()
        })
    };

    let timing = {
        let app = Arc::clone(&app);
        define_extension(Extension {
            name: "timing".to_owned(),
            wraps: vec![wrap_tool(&bash_tool, move |tool| {
                let (execute, app) = (Arc::clone(&tool.execute), Arc::clone(&app));
                Ok(Arc::new(ToolRegistration {
                    execute: Arc::new(move |args, api, context| {
                        let (execute, app) = (Arc::clone(&execute), Arc::clone(&app));
                        async move {
                            let start = Instant::now();
                            let result = execute(args, api, context).await;
                            app.record_metric("bash", start.elapsed().as_secs_f64() * 1000.0);
                            result
                        }
                        .boxed()
                    }),
                    ..(**tool).clone()
                }))
            })],
            ..Extension::default()
        })
    };
    // A bash inside a Python virtualenv for one conversation: it replaces CodingTools' bash in place,
    // and Timing, if selected, wraps it.
    let venv = define_extension(Extension {
        name: "venv".to_owned(),
        tools: vec![create_bash_tool(BashToolOptions {
            command_prefix: Some("source .venv/bin/activate".to_owned()),
            ..BashToolOptions::default()
        })],
        ..Extension::default()
    });

    // ─── Section 7.2: hooks reading extension state ──────────────────────────────

    let plan_mode = {
        let app = Arc::clone(&app);
        define_extension(Extension {
            name: "plan-mode".to_owned(),
            hooks: vec![hook(
                &TOOL_TASK,
                ToolHooks {
                    // An absent document means plan mode is off.
                    before_tool: Some(Arc::new(move |call, api, context| {
                        let snapshot =
                            api.snapshot(&*PLAN_MODE_DOC, api.conversation_id(), context);
                        let writes = app.writes(call);
                        async move {
                            let enabled = snapshot.await?.is_some_and(|value| {
                                value.get("enabled").and_then(JsonValue::as_bool) == Some(true)
                            });
                            Ok((enabled && writes).then(|| BeforeToolDecision {
                                block: Some("Plan mode: read-only".to_owned()),
                                ..BeforeToolDecision::default()
                            }))
                        }
                        .boxed()
                    })),
                    ..ToolHooks::default()
                },
            )],
            ..Extension::default()
        })
    };

    // ─── Section 7.3: subagents ──────────────────────────────────────────────────

    // The tool removes its own extension from the child: the extension is set once defined.
    let subagent_extension: Arc<OnceLock<Arc<Extension>>> = Arc::default();
    let subagent = {
        let (app, itself) = (Arc::clone(&app), Arc::clone(&subagent_extension));
        define_extension(Extension {
            name: "subagent".to_owned(),
            tools: vec![define_tool(ToolRegistration {
                replay: Some(ToolReplay::Safe),
                ..ToolRegistration::new(
                    "subagent",
                    "Delegate a self-contained task to a subagent and get its answer back.",
                    Type::object([("task", Type::string())]),
                    move |args, api, context| {
                        let (app, itself) = (Arc::clone(&app), Arc::clone(&itself));
                        async move {
                            let task = args["task"].as_str().unwrap_or_default().to_owned();
                            let task_id = api.task_id();
                            let child = api
                                .commit(
                                    move |tx| async move {
                                        let existing = tx
                                            .scan_conversations(
                                                ConversationQuery {
                                                    owner_task_id: Some(task_id),
                                                    ..ConversationQuery::default()
                                                },
                                                1,
                                                None,
                                            )
                                            .await?;
                                        if let Some(existing) = existing.items.first() {
                                            return Ok(existing.id);
                                        }
                                        // Starts as a copy of this conversation's agent: model, thinking level, cwd, extensions, tools.
                                        let created = tx
                                            .create_conversation(ConversationOwnership::Task {
                                                task_id,
                                            })
                                            .await?;
                                        // Without this extension, the child is not offered this tool.
                                        configure(
                                            &tx,
                                            created.id,
                                            &AgentChange {
                                                extensions: FieldChange::Set(
                                                    ExtensionsChange::Edit {
                                                        add: None,
                                                        remove: Some(
                                                            itself
                                                                .get()
                                                                .cloned()
                                                                .into_iter()
                                                                .collect(),
                                                        ),
                                                    },
                                                ),
                                                ..AgentChange::default()
                                            },
                                        )
                                        .await?;
                                        Ok(created.id)
                                    },
                                    &context,
                                )
                                .await?;
                            api.details(
                                JsonValue::from(
                                    serde_json::json!({ "conversationId": child.get() }),
                                ),
                                &context,
                            )
                            .await?;
                            let handle =
                                api.conversation(child, &context).await?.ok_or_else(|| {
                                    SessionError::error("the child conversation exists")
                                })?;
                            let request = InputSubmissionDraft {
                                request_id: Some(format!("subagent:{task_id}")),
                                ..InputSubmissionDraft::new(task)
                            };
                            let settled = handle
                                .submit(request, &context)
                                .await?
                                .wait(&context)
                                .await?;
                            let SubmissionState::Input(InputSubmission::Done { answer, .. }) =
                                settled.state
                            else {
                                let status = serde_json::to_value(settled.state.status())
                                    .map_err(SessionError::other)?;
                                return Err(SessionError::error(format!(
                                    "Subagent failed: {}",
                                    status.as_str().unwrap_or_default()
                                )));
                            };
                            let text = app.answer_text(Arc::clone(&api), answer, &context).await?;
                            Ok(ToolExecutionResult {
                                content: Some(vec![UserContentBlock::Text(TextContent::new(text))]),
                                ..ToolExecutionResult::default()
                            })
                        }
                    },
                )
            })],
            ..Extension::default()
        })
    };
    subagent_extension
        .set(Arc::clone(&subagent))
        .expect("set once");

    let subagent_tools = define_extension(Extension {
        name: "subagent-tools".to_owned(),
        tasks: vec![app.anchor().erase(), app.reporter().erase()],
        tools: vec![app.subagent_tool()],
        ..Extension::default()
    });

    // ─── Section 7.4 ─────────────────────────────────────────────────────────────

    let chat = define_extension(Extension {
        name: "chat".to_owned(),
        sections: vec![text_section(
            "preamble",
            || Some("You are a helpful assistant.".to_owned()),
            Some(false),
        )],
        ..Extension::default()
    });

    // ─── Section 5.1: a task with intent, effect, outcome ────────────────────────

    let payment = {
        let (prepare_app, charge_app, abort_app) =
            (Arc::clone(&app), Arc::clone(&app), Arc::clone(&app));
        define_task(
            TaskDefinition::<(), Charge, PaymentResult, ()>::new(
                "app.payment",
                1,
                |(): &()| Ok(Charge::Prepare),
                // The abort handler decides the outcome; returning without one faults the task.
                move |task, runtime, context: Context| {
                    let cancelled = abort_app.cancel(&task.checkpoint);
                    async move {
                        cancelled.await?;
                        runtime
                            .commit(
                                |_tx, _current| async {
                                    Ok(Some(NextTaskState::Terminal {
                                        outcome: TaskOutcome::Aborted {
                                            reason: Some("user".to_owned()),
                                            result: None,
                                        },
                                    }))
                                },
                                &context,
                            )
                            .await
                    }
                },
            )
            // Intent, effect, outcome.
            .phase("prepare", move |_task, runtime, context: Context| {
                let key = prepare_app.new_key();
                async move {
                    runtime
                        .commit(
                            |_tx, _current| async {
                                Ok(Some(NextTaskState::Running {
                                    checkpoint: Charge::Charge { key },
                                }))
                            },
                            &context,
                        )
                        .await
                }
            })
            .phase("charge", move |task, runtime, context: Context| {
                let app = Arc::clone(&charge_app);
                async move {
                    // Rust has no per-phase narrowing: the handler checks its checkpoint.
                    let Charge::Charge { key } = &task.checkpoint else {
                        return Err(SessionError::error("charge runs the charge checkpoint"));
                    };
                    let receipt = app.charge(key).await?; // idempotent by key
                    runtime
                        .commit(
                            move |tx, current| async move {
                                let entry = tx
                                    .append_entry(
                                        current.conversation_id,
                                        app.receipt_entry(&receipt),
                                    )
                                    .await?;
                                Ok(Some(NextTaskState::Terminal {
                                    outcome: TaskOutcome::Completed {
                                        result: PaymentResult { entry_id: entry.id },
                                    },
                                }))
                            },
                            &context,
                        )
                        .await
                }
            }),
        )
    };

    let follow = define_task(
        TaskDefinition::<EmptyObject, Follow, (), ()>::new(
            "app.follow",
            1,
            |_: &EmptyObject| Ok(Follow::Follow),
            |_task, _runtime, _context| async { Ok(()) },
        )
        .phase("follow", |_task, _runtime, _context| async { Ok(()) }),
    );

    // ─── Sequences ───────────────────────────────────────────────────────────────

    let sequences = Sequences {
        child_in_tool_commit: {
            let (app, read_tool) = (Arc::clone(&app), Arc::clone(&read_tool));
            Box::new(move |(tx, task_id): (Tx, TaskId)| {
                let (app, read_tool) = (Arc::clone(&app), Arc::clone(&read_tool));
                async move {
                    // In a tool's commit. The child starts as a copy of this conversation's agent: model, extensions, tools, cwd.
                    let child = tx
                        .create_conversation(ConversationOwnership::Task { task_id })
                        .await?;
                    // A cheaper model, only the read tool, and its own worktree; everything else stays as copied.
                    configure(
                        &tx,
                        child.id,
                        &AgentChange {
                            model: FieldChange::Set(app.haiku()),
                            tools: FieldChange::Set(ToolsChange::Exactly(vec![read_tool])),
                            cwd: FieldChange::Set(app.worktree()),
                            ..AgentChange::default()
                        },
                    )
                    .await
                }
                .boxed()
            })
        },

        live_settings: {
            let app = Arc::clone(&app);
            Box::new(move || {
                let manager = app.manager();
                // No Session write; every conversation follows at its next threshold check.
                manager.set_auto_compact(false);
                Arc::new(UserSettings { manager })
            })
        },

        container_env: {
            let app = Arc::clone(&app);
            Box::new(move |()| {
                let app = Arc::clone(&app);
                async move {
                    // Absent: the conversation runs locally. Only conversations with this document run in a container.
                    // Subagents do not copy it: their creator writes it too when they should run in the container.
                    static CONTAINER_DOC: LazyLock<ConversationDoc<ContainerState>> =
                        LazyLock::new(|| {
                            ConversationDoc::define(
                                DocDefinition {
                                    kind: "app.container",
                                    version: 1,
                                    initial: || ContainerState {
                                        image: "node:22".to_owned(),
                                    },
                                    migrate: None,
                                    checkpoint_when: None,
                                },
                                LatestFork::Current,
                            )
                            .expect("a valid definition")
                        });
                    let registry = create_registry();
                    let env_app = Arc::clone(&app);
                    let env: EnvFactory = Arc::new(move |target: EnvTarget, context: &Context| {
                        let app = Arc::clone(&env_app);
                        let container =
                            target
                                .read
                                .snapshot(&*CONTAINER_DOC, target.conversation_id, context);
                        let context = context.clone();
                        async move {
                            Ok(Some(match container.await? {
                                Some(container) => {
                                    let image = container
                                        .get("image")
                                        .and_then(JsonValue::as_str)
                                        .unwrap_or_default()
                                        .to_owned();
                                    let cwd = target.cwd.unwrap_or_else(|| "/work".to_owned());
                                    app.container_env(&image, &cwd, &context).await?
                                }
                                // Cached NodeExecutionEnv per directory.
                                None => app.local_env(&match target.cwd {
                                    Some(cwd) => cwd,
                                    None => current_dir()?,
                                }),
                            }))
                        }
                        .boxed()
                    });
                    let options = HarnessOptions {
                        env: Some(env),
                        ..HarnessOptions::new(app.models(), Arc::new(registry))
                    };
                    Harness::open(app.storage(), options, &app.context()).await
                }
                .boxed()
            })
        },

        host: {
            let app = Arc::clone(&app);
            Box::new(move |()| {
                let app = Arc::clone(&app);
                let (coding, context_files, skills, permissions, reviewer) = (
                    Arc::clone(&coding),
                    Arc::clone(&context_files),
                    Arc::clone(&skills),
                    Arc::clone(&permissions),
                    Arc::clone(&reviewer),
                );
                let (timing, venv, plan_mode, subagent, chat, skills_v2) = (
                    Arc::clone(&timing),
                    Arc::clone(&venv),
                    Arc::clone(&plan_mode),
                    Arc::clone(&subagent),
                    Arc::clone(&chat),
                    Arc::clone(&skills_v2),
                );
                let (edit_tool, bash_tool) = (Arc::clone(&edit_tool), Arc::clone(&bash_tool));
                async move {
                    let context = app.context();
                    let registry = create_registry();
                    for extension in [
                        Arc::clone(&CODING_TOOLS),
                        Arc::clone(&coding),
                        Arc::clone(&context_files),
                        Arc::clone(&skills),
                        Arc::clone(&permissions),
                        reviewer,
                    ] {
                        registry.install(extension)?;
                    }
                    let local_app = Arc::clone(&app);
                    let env: EnvFactory = Arc::new(move |target: EnvTarget, _context: &Context| {
                        // Cached NodeExecutionEnv per directory.
                        let env = match target.cwd {
                            Some(cwd) => Ok(local_app.local_env(&cwd)),
                            None => current_dir().map(|cwd| local_app.local_env(&cwd)),
                        };
                        async move { env.map(Some) }.boxed()
                    });
                    let options = HarnessOptions {
                        // Reviewer is installed but not selected by default: only conversations that select it get its role and hooks.
                        settings: Some(Arc::new(LiveSettings::new(HarnessSettings {
                            extensions: Some(vec![
                                Arc::clone(&CODING_TOOLS),
                                coding,
                                context_files,
                                Arc::clone(&skills),
                                permissions,
                            ]),
                            ..HarnessSettings::default()
                        }))),
                        env: Some(env),
                        ..HarnessOptions::new(app.models(), Arc::new(registry.clone()))
                    };
                    let harness = Harness::open(app.storage(), options, &context).await?;
                    // The conversation remembers its model and directory; a restart elsewhere keeps both.
                    let root = harness
                        .root(
                            RootOptions {
                                agent: Some(AgentChange {
                                    model: FieldChange::Set(app.sonnet()),
                                    cwd: FieldChange::Set(current_dir()?),
                                    ..AgentChange::default()
                                }),
                                ..RootOptions::default()
                            },
                            &context,
                        )
                        .await?;

                    root.configure(
                        AgentChange {
                            tools: FieldChange::Set(ToolsChange::Remove(vec![edit_tool])),
                            ..AgentChange::default()
                        },
                        &context,
                    )
                    .await?;
                    // edit is offered again
                    root.configure(
                        AgentChange {
                            tools: FieldChange::Set(ToolsChange::Remove(vec![bash_tool])),
                            ..AgentChange::default()
                        },
                        &context,
                    )
                    .await?;
                    // every tool of the selected extensions again
                    root.configure(
                        AgentChange {
                            tools: FieldChange::Clear,
                            ..AgentChange::default()
                        },
                        &context,
                    )
                    .await?;

                    registry.install(timing)?;
                    registry.install(Arc::clone(&venv))?; // installed, but not in the default selection
                    let conversation = &root;
                    conversation
                        .configure(
                            AgentChange {
                                extensions: FieldChange::Set(ExtensionsChange::Edit {
                                    add: Some(vec![venv]),
                                    remove: None,
                                }),
                                ..AgentChange::default()
                            },
                            &context,
                        )
                        .await?;

                    registry.install(plan_mode)?;
                    // PlanMode is in the default selection; /plan toggles this conversation's state.
                    let root_id = root.id();
                    root.commit(
                        move |tx| async move {
                            tx.doc(&*PLAN_MODE_DOC, root_id)
                                .await?
                                .set("enabled", true)?;
                            Ok(())
                        },
                        &context,
                    )
                    .await?;

                    registry.install(subagent)?;
                    registry.install(chat)?;
                    registry.install(skills_v2)?; // same name: conversations selecting skills render v2 at their next request
                    registry.uninstall(&skills); // selecting conversations get a system delta removing its section; nothing is rewritten
                                                 // Restart: the host installs its extensions again; stored names resolve against them.
                    Ok(harness)
                }
                .boxed()
            })
        },

        spawn: {
            let app = Arc::clone(&app);
            Box::new(move |tx: Tx| {
                let (app, subagent_tools) = (Arc::clone(&app), Arc::clone(&subagent_tools));
                async move {
                    // In subagentTool's spawn commit, after the name checks:
                    let anchor = tx
                        .create_task(
                            app.anchor().as_definition_ref(),
                            JsonValue::Null,
                            TaskOptions {
                                ownership: TaskOwnership::Conversation,
                                conversation_id: None,
                                background: Some(true),
                            },
                        )
                        .await?;
                    // Owned by a task of the parent: starts as a copy of the parent's agent.
                    let child = tx
                        .create_conversation(ConversationOwnership::Task { task_id: anchor })
                        .await?;
                    configure(
                        &tx,
                        child.id,
                        &AgentChange {
                            extensions: FieldChange::Set(ExtensionsChange::Edit {
                                add: None,
                                remove: Some(vec![subagent_tools]),
                            }),
                            instructions: FieldChange::Set(format!(
                                "You are the subagent \"{}\". Answer the main agent's requests.",
                                app.name()
                            )),
                            ..AgentChange::default()
                        },
                    )
                    .await
                }
                .boxed()
            })
        },

        table_rules: {
            let app = Arc::clone(&app);
            Box::new(move |()| {
                let (app, follow) = (Arc::clone(&app), follow.clone());
                async move {
                    let conversation_id = app.conversation_id();
                    let message = app.message();
                    app.session()
                        .commit(
                            move |tx| async move {
                                let conversation = tx.conversation(conversation_id).await?; // table read
                                let live = tx.doc(&LIVE_DOC, conversation_id).await?;

                                tx.append_entry(conversation_id, message).await?; // first table write
                                live.delete("generation")?; // document mutation remains valid
                                tx.create_task(
                                    follow.as_definition_ref(),
                                    JsonValue::from(serde_json::json!({})),
                                    TaskOptions {
                                        ownership: TaskOwnership::Conversation,
                                        conversation_id: Some(conversation_id),
                                        background: None,
                                    },
                                )
                                .await?; // further table writes are fine
                                let _ = conversation;
                                Ok(())
                            },
                            &app.context(),
                        )
                        .await
                }
                .boxed()
            })
        },

        revoked_draft: {
            let app = Arc::clone(&app);
            Box::new(move |()| {
                let app = Arc::clone(&app);
                async move {
                    let conversation_id = app.conversation_id();
                    let escaped: Draft = app
                        .session()
                        .commit(
                            move |tx| async move { tx.doc(&LIVE_DOC, conversation_id).await },
                            &app.context(),
                        )
                        .await?;
                    // TS `escaped.generation = undefined`; fails: the draft was revoked.
                    escaped.delete("generation")?;
                    Ok(())
                }
                .boxed()
            })
        },
    };
    Examples { sequences, payment }
}

#[test]
fn compiles_the_specs_usage_examples() {
    let compiled: fn(&Arc<dyn App>) -> Examples = examples;
    // TS `expectTypeOf(examples).returns.toHaveProperty("sequences")`: the
    // returned value carries the sequences (and `Payment`).
    let parts: fn(Examples) -> _ = |examples| {
        let Examples {
            sequences:
                Sequences {
                    child_in_tool_commit,
                    live_settings,
                    container_env,
                    host,
                    spawn,
                    table_rules,
                    revoked_draft,
                },
            payment,
        } = examples;
        (
            (child_in_tool_commit, live_settings, container_env, host),
            (spawn, table_rules, revoked_draft),
            payment,
        )
    };
    // TS `expect(examples).toBeTypeOf("function")`.
    let _ = (compiled, parts);
}
