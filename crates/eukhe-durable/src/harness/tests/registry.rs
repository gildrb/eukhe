//! Port of `test/harness-registry.test.ts`.
//!
//! The TS app tool type (`ToolRegistration & { snippet? }`) is a tool with
//! [`Snippet`] application data. `GenerationTask`, `ToolTask`, and
//! `CompactionTask` are the support module's built-ins.

use std::cell::RefCell;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::Context;
use eukhe_chord::json::JsonValue;
use eukhe_types::pi_ai::{IndexMap, ModelThinkingLevel};
use futures::future::BoxFuture;
use futures::FutureExt;

use super::support::{
    compaction_task, context, create_registry, generation_task, tool_described, tool_task,
};
use crate::documents::{AnyDocDefinition, ResolvedAddress};
use crate::harness::agent::{agent_hooks, resolve_agent, resolve_settings};
use crate::harness::define::{define_extension, hook, section, wrap_section, wrap_tool};
use crate::harness::types::{
    Agent, AgentState, Extension, ExtensionSelection, GenerationHooks, HarnessSettings,
    HookRegistration, ModelRef, PartialProgressPolicy, ProgressPolicy, PromptInput, PromptSection,
    RegistryReader, RegistrySnapshot, ToolFilter, ToolHooks, ToolRegistration,
};
use crate::session::{SessionError, SessionResult};
use crate::tasks::{define_task, AnyTask, TaskDefinition};
use crate::types::{ConversationId, DocumentReader, EntryId, JsonObject};

/// The app tool's extra field.
struct Snippet(&'static str);

fn tool(name: &str) -> Arc<ToolRegistration> {
    tool_described(name, &format!("{name} tool"))
}

fn tool_with(
    name: &str,
    edit: impl FnOnce(ToolRegistration) -> ToolRegistration,
) -> Arc<ToolRegistration> {
    Arc::new(edit((*tool(name)).clone()))
}

fn task(name: &str, version: u64) -> AnyTask {
    define_task(
        TaskDefinition::<(), JsonValue, (), ()>::new(
            name,
            version,
            |()| Ok(JsonValue::parse(r#"{"phase":"run"}"#)?),
            |_, _, _| async { Ok(()) },
        )
        .phase("run", |_, _, _| async { Ok(()) }),
    )
    .erase()
}

fn names(extensions: &[Arc<Extension>]) -> Vec<&str> {
    extensions
        .iter()
        .map(|extension| extension.name.as_str())
        .collect()
}

fn tool_names(tools: &[Arc<ToolRegistration>]) -> Vec<&str> {
    tools.iter().map(|tool| tool.name.as_str()).collect()
}

fn text_section(key: &str, text: &'static str, tag: Option<bool>) -> Arc<PromptSection> {
    section(
        key,
        move |_, _| futures::future::ready(Ok(Some(text.to_owned()))).boxed(),
        tag,
    )
}

fn extension(name: &str, edit: impl FnOnce(&mut Extension)) -> Arc<Extension> {
    let mut extension = Extension::named(name);
    edit(&mut extension);
    define_extension(extension)
}

/// Resolve `state` against `snapshot` and `settings`, collecting reports.
fn resolve(
    state: Option<&AgentState>,
    snapshot: &RegistrySnapshot,
    settings: &HarnessSettings,
    reports: &RefCell<Vec<SessionError>>,
) -> Agent {
    resolve_agent(
        state,
        snapshot,
        &resolve_settings(Some(settings)),
        &|error| {
            reports.borrow_mut().push(error);
        },
    )
}

fn resolve_quiet(state: Option<&AgentState>, snapshot: &RegistrySnapshot) -> Agent {
    resolve(
        state,
        snapshot,
        &HarnessSettings::default(),
        &RefCell::default(),
    )
}

/// TS `{ snapshot: async () => undefined, snapshotAsOf: async () => undefined }`.
struct NoDocuments;

impl DocumentReader for NoDocuments {
    fn snapshot_definition(
        &self,
        _definition: Arc<dyn AnyDocDefinition>,
        _resolved: ResolvedAddress,
        _cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        futures::future::ready(Ok(None)).boxed()
    }

    fn snapshot_as_of_definition(
        &self,
        _definition: Arc<dyn AnyDocDefinition>,
        _resolved: ResolvedAddress,
        _at: EntryId,
        _cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        futures::future::ready(Ok(None)).boxed()
    }
}

async fn rendered(agent: Agent) -> Vec<(String, Option<String>)> {
    let sections = agent.sections.clone();
    let input = PromptInput {
        conversation_id: ConversationId::from_number(1),
        agent: Arc::new(agent),
        env: None,
        shown: IndexMap::new(),
        read: Arc::new(NoDocuments),
    };
    let mut rendered = Vec::new();
    for item in sections {
        let text = (item.render)(&input, context()).await.ok().flatten();
        rendered.push((item.key.clone(), text));
    }
    rendered
}

fn messages(reports: &RefCell<Vec<SessionError>>) -> Vec<String> {
    reports.borrow().iter().map(ToString::to_string).collect()
}

// ─── registry ───────────────────────────────────────────────────────────

#[test]
fn installs_replaces_in_place_and_uninstalls_extensions_by_name() {
    let registry = create_registry();
    let listener = Arc::new(Mutex::new(Vec::<String>::new()));
    let seen = Arc::clone(&listener);
    let observed = registry.clone();
    let _subscription = registry.subscribe(Arc::new(move || {
        let snapshot = observed.snapshot();
        seen.lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(names(snapshot.installed()).join(","));
    }));
    let a = extension("a", |a| {
        a.tools = vec![tool_with("read", |tool| {
            tool.with_extra(Snippet("Read files"))
        })];
    });
    let b = extension("b", |b| b.tools = vec![tool("read"), tool("bash")]);
    registry.install(Arc::clone(&a)).unwrap();
    registry.install(Arc::clone(&b)).unwrap();
    let before = registry.snapshot();
    // A new object with an installed name replaces it at its position.
    let a2 = extension("a", |a2| a2.tools = vec![tool("grep")]);
    registry.install(Arc::clone(&a2)).unwrap();
    assert_eq!(names(registry.snapshot().installed()), ["a", "b"]);
    assert!(Arc::ptr_eq(
        registry.snapshot().extension("a").unwrap(),
        &a2
    ));
    assert_eq!(
        registry
            .snapshot()
            .tools()
            .iter()
            .map(|entry| format!("{}@{}", entry.tool.name, entry.extension.name))
            .collect::<Vec<_>>(),
        ["grep@a", "read@b", "bash@b"]
    );
    // Old snapshots stay as they were.
    assert!(Arc::ptr_eq(before.extension("a").unwrap(), &a));
    assert_eq!(
        before.tools()[0]
            .tool
            .extra::<Snippet>()
            .map(|snippet| snippet.0),
        Some("Read files")
    );
    // Uninstall matches the name, whichever object; a later install appends.
    registry.uninstall(&a);
    registry.uninstall(&a);
    assert_eq!(names(registry.snapshot().installed()), ["b"]);
    registry.install(Arc::clone(&a)).unwrap();
    assert_eq!(names(registry.snapshot().installed()), ["b", "a"]);
    assert_eq!(
        *listener.lock().unwrap_or_else(PoisonError::into_inner),
        ["a", "a,b", "a,b", "b", "b,a"]
    );
}

#[test]
fn validates_the_registry_as_it_would_be_after_an_install_and_publishes_nothing_when_invalid() {
    let registry = create_registry();
    let tasks = extension("tasks", |tasks| tasks.tasks = vec![task("app.index", 1)]);
    registry.install(tasks).unwrap();
    let published = Arc::new(Mutex::new(Vec::<u32>::new()));
    let count = Arc::clone(&published);
    let _subscription = registry.subscribe(Arc::new(move || {
        count.lock().unwrap_or_else(PoisonError::into_inner).push(1);
    }));
    let before = registry.snapshot();
    let invalid = [
        (
            extension("x", |x| x.tools = vec![tool("read"), tool("read")]),
            "two tools named read",
        ),
        (
            extension("x", |x| {
                x.sections = vec![text_section("a", "1", None), text_section("a", "2", None)];
            }),
            "two sections",
        ),
        (
            extension("x", |x| {
                x.sections = vec![text_section("Bad Key", "", None)];
            }),
            "must match",
        ),
        (
            extension("x", |x| {
                x.sections = vec![text_section("instructions", "", None)];
            }),
            "reserved",
        ),
        (
            extension("x", |x| x.tasks = vec![task("pi.generation", 1)]),
            "already installed",
        ),
        (
            extension("x", |x| x.tasks = vec![task("app.index", 1)]),
            "already installed",
        ),
    ];
    for (extension, message) in invalid {
        let error = registry.install(extension).unwrap_err().to_string();
        assert!(error.contains(message), "{error:?} contains {message:?}");
    }
    assert!(RegistrySnapshot::ptr_eq(&registry.snapshot(), &before));
    assert!(published
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .is_empty());
    // Replacing the extension that holds a task name is valid: the check runs
    // on the state after replacement.
    registry
        .install(extension("tasks", |tasks| {
            tasks.tasks = vec![task("app.index", 2)];
        }))
        .unwrap();
    assert_eq!(
        registry.snapshot().task("app.index").map(AnyTask::version),
        Some(2)
    );
}

#[test]
fn always_holds_the_built_in_tasks_which_are_not_an_extension() {
    let builtins = vec![
        generation_task().erase(),
        tool_task().erase(),
        compaction_task().erase(),
    ];
    let registry = create_registry();
    assert!(registry.snapshot().installed().is_empty());
    assert_eq!(registry.snapshot().tasks(), builtins);
    let custom = task("app.custom", 1);
    registry
        .install(extension("custom", |extension| {
            extension.tasks = vec![custom.clone()];
        }))
        .unwrap();
    let mut with_custom = builtins;
    with_custom.push(custom);
    assert_eq!(registry.snapshot().tasks(), with_custom);
    assert_eq!(registry.snapshot().task("app.custom"), with_custom.last());
    registry.uninstall(&Extension::named("custom"));
    assert_eq!(registry.snapshot().task("app.custom"), None);
}

// ─── settings ───────────────────────────────────────────────────────────

#[test]
fn keeps_the_default_of_a_progress_interval_given_as_undefined() {
    let settings = HarnessSettings {
        progress: Some(PartialProgressPolicy {
            partial_interval_ms: None,
            output_interval_ms: Some(250.0),
        }),
        ..HarnessSettings::default()
    };
    assert_eq!(
        resolve_settings(Some(&settings)).progress,
        ProgressPolicy {
            partial_interval_ms: 100.0,
            output_interval_ms: 250.0,
        }
    );
}

// ─── agent resolution ───────────────────────────────────────────────────

struct Fixture {
    read: Arc<ToolRegistration>,
    bash: Arc<ToolRegistration>,
    edit: Arc<ToolRegistration>,
    coding: Arc<Extension>,
    skills: Arc<Extension>,
    snapshot: RegistrySnapshot,
}

fn fixture() -> Fixture {
    let read = tool("read");
    let bash = tool("bash");
    let edit = tool("edit");
    let coding = extension("coding", |coding| {
        coding.tools = vec![Arc::clone(&read), Arc::clone(&bash), Arc::clone(&edit)];
        coding.sections = vec![
            text_section("preamble", "You code.", Some(false)),
            text_section("cwd", "/repo", None),
        ];
    });
    let skills = extension("skills", |skills| {
        skills.sections = vec![text_section("skills", "S", None)];
    });
    let reviewer = extension("reviewer", |reviewer| {
        reviewer.sections = vec![text_section("role", "Review.", None)];
    });
    let registry = create_registry();
    for extension in [&coding, &skills, &reviewer] {
        registry.install(Arc::clone(extension)).unwrap();
    }
    let snapshot = registry.snapshot();
    Fixture {
        read,
        bash,
        edit,
        coding,
        skills,
        snapshot,
    }
}

fn selection(names: &[&str]) -> AgentState {
    AgentState {
        extensions: Some(ExtensionSelection::Exactly(
            names.iter().map(|name| (*name).to_owned()).collect(),
        )),
        ..AgentState::default()
    }
}

fn strings(names: &[&str]) -> Vec<String> {
    names.iter().map(|name| (*name).to_owned()).collect()
}

#[test]
fn selects_the_default_an_array_or_the_default_edited_by_add_and_remove() {
    let Fixture {
        coding,
        skills,
        snapshot,
        ..
    } = fixture();
    let reports = RefCell::default();
    assert_eq!(
        names(&resolve_quiet(None, &snapshot).extensions),
        ["coding", "skills", "reviewer"]
    );
    let settings = HarnessSettings {
        extensions: Some(vec![Arc::clone(&coding), Arc::clone(&skills)]),
        ..HarnessSettings::default()
    };
    assert_eq!(
        names(&resolve(Some(&AgentState::default()), &snapshot, &settings, &reports).extensions),
        ["coding", "skills"]
    );
    assert_eq!(
        names(
            &resolve(
                Some(&selection(&["reviewer", "coding"])),
                &snapshot,
                &settings,
                &reports
            )
            .extensions
        ),
        ["reviewer", "coding"]
    );
    // Add appends, remove drops, duplicates keep their first position,
    // uninstalled names are skipped.
    let edited = AgentState {
        extensions: Some(ExtensionSelection::Edit {
            add: Some(strings(&["reviewer", "coding", "gone"])),
            remove: Some(strings(&["skills"])),
        }),
        ..AgentState::default()
    };
    assert_eq!(
        names(&resolve(Some(&edited), &snapshot, &settings, &reports).extensions),
        ["coding", "reviewer"]
    );
    // An old object stands for its name: the installed extension is selected.
    let stale = HarnessSettings {
        extensions: Some(vec![
            define_extension(Extension::named("skills")),
            Arc::clone(&skills),
        ]),
        ..HarnessSettings::default()
    };
    let selected = resolve(Some(&AgentState::default()), &snapshot, &stale, &reports).extensions;
    assert_eq!(selected.len(), 1);
    assert!(Arc::ptr_eq(&selected[0], &skills));
}

#[test]
fn skips_uninstalled_names_and_resolves_them_again_once_they_are_installed() {
    let Fixture { coding, skills, .. } = fixture();
    let local = create_registry();
    local.install(coding).unwrap();
    let state = selection(&["coding", "skills"]);
    assert_eq!(
        names(&resolve_quiet(Some(&state), &local.snapshot()).extensions),
        ["coding"]
    );
    local.install(skills).unwrap();
    assert_eq!(
        names(&resolve_quiet(Some(&state), &local.snapshot()).extensions),
        ["coding", "skills"]
    );
}

fn redescribe(
    suffix: &'static str,
) -> impl Fn(&Arc<ToolRegistration>) -> SessionResult<Arc<ToolRegistration>> {
    move |inner| {
        Ok(Arc::new(ToolRegistration {
            description: format!("{}{suffix}", inner.description),
            ..(**inner).clone()
        }))
    }
}

#[test]
fn replaces_same_name_tools_in_place_wraps_the_winner_then_applies_the_filter() {
    let Fixture { bash, coding, .. } = fixture();
    let local = create_registry();
    let venv_bash = tool_described("bash", "venv bash");
    let calls = Arc::new(Mutex::new(Vec::<&str>::new()));
    let venv = extension("venv", |venv| venv.tools = vec![venv_bash]);
    let grep_calls = Arc::clone(&calls);
    let timing = extension("timing", |timing| {
        timing.wraps = vec![
            wrap_tool(&bash, redescribe(" (timed)")),
            wrap_tool(&bash, redescribe(" [2]")),
            // No `grep` is selected: the wrapper does nothing and reports
            // nothing.
            wrap_tool(&tool("grep"), move |_| {
                grep_calls
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push("grep");
                Ok(tool("grep"))
            }),
        ];
    });
    for extension in [coding, venv, timing] {
        local.install(extension).unwrap();
    }
    let reports = RefCell::default();
    let agent = resolve(
        None,
        &local.snapshot(),
        &HarnessSettings::default(),
        &reports,
    );
    assert_eq!(
        agent
            .tools
            .iter()
            .map(|each| (each.name.as_str(), each.description.as_str()))
            .collect::<Vec<_>>(),
        [
            ("read", "read tool"),
            ("bash", "venv bash (timed) [2]"),
            ("edit", "edit tool"),
        ]
    );
    assert!(reports.borrow().is_empty());
    assert!(calls
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .is_empty());

    // An array keeps exactly these names in its order, a repeated name at its
    // first position.
    let filtered = resolve_quiet(
        Some(&AgentState {
            tools: Some(ToolFilter::Exactly(strings(&[
                "edit", "missing", "read", "edit",
            ]))),
            ..AgentState::default()
        }),
        &local.snapshot(),
    );
    assert_eq!(tool_names(&filtered.tools), ["edit", "read"]);
    let removed = resolve_quiet(
        Some(&AgentState {
            tools: Some(ToolFilter::Remove {
                remove: strings(&["bash"]),
            }),
            ..AgentState::default()
        }),
        &local.snapshot(),
    );
    assert_eq!(tool_names(&removed.tools), ["read", "edit"]);
}

#[test]
fn drops_a_tool_or_section_whose_wrapper_throws_or_renames_it_and_reports_the_failure() {
    let Fixture {
        read, edit, coding, ..
    } = fixture();
    let local = create_registry();
    let broken = extension("broken", |broken| {
        broken.wraps = vec![
            wrap_tool(&read, |_| Err(SessionError::error("wrapper failed"))),
            wrap_tool(&edit, |inner| {
                Ok(Arc::new(ToolRegistration {
                    name: "renamed".to_owned(),
                    ..(**inner).clone()
                }))
            }),
            wrap_section("cwd", |_| {
                Err(SessionError::error("section wrapper failed"))
            }),
        ];
    });
    local.install(coding).unwrap();
    local.install(broken).unwrap();
    let reports = RefCell::default();
    let agent = resolve(
        None,
        &local.snapshot(),
        &HarnessSettings::default(),
        &reports,
    );
    assert_eq!(tool_names(&agent.tools), ["bash"]);
    assert_eq!(
        agent
            .sections
            .iter()
            .map(|each| each.key.as_str())
            .collect::<Vec<_>>(),
        ["preamble"]
    );
    assert_eq!(
        messages(&reports),
        [
            "wrapper failed",
            "Wrapper renamed edit to renamed",
            "section wrapper failed",
        ]
    );
}

#[tokio::test]
async fn orders_sections_by_extension_replaces_same_keys_in_place_and_renders_instructions_last_and_unwrapped(
) {
    let Fixture { coding, skills, .. } = fixture();
    let local = create_registry();
    let over = extension("override", |over| {
        over.sections = vec![text_section("preamble", "You review.", Some(false))];
        over.wraps = vec![
            wrap_section("cwd", |inner| {
                let wrapped = Arc::clone(inner);
                Ok(Arc::new(PromptSection {
                    render: Arc::new(move |input, cx| {
                        let rendered = (wrapped.render)(input, cx);
                        async move {
                            // TS template literal of the awaited value.
                            let text = rendered.await?.unwrap_or_else(|| "undefined".to_owned());
                            Ok(Some(format!("{text}!")))
                        }
                        .boxed()
                    }),
                    ..(**inner).clone()
                }))
            }),
            // Instructions are not wrapped.
            wrap_section("instructions", |_| Err(SessionError::error("never"))),
        ];
    });
    for extension in [coding, skills, over] {
        local.install(extension).unwrap();
    }
    let reports = RefCell::default();
    let state = AgentState {
        instructions: Some("Be terse.".to_owned()),
        ..AgentState::default()
    };
    let agent = resolve(
        Some(&state),
        &local.snapshot(),
        &HarnessSettings::default(),
        &reports,
    );
    let last_tag = agent.sections.last().and_then(|section| section.tag);
    assert_eq!(
        rendered(agent).await,
        [
            ("preamble".to_owned(), Some("You review.".to_owned())),
            ("cwd".to_owned(), Some("/repo!".to_owned())),
            ("skills".to_owned(), Some("S".to_owned())),
            ("instructions".to_owned(), Some("Be terse.".to_owned())),
        ]
    );
    assert_eq!(last_tag, None);
    assert!(reports.borrow().is_empty());
}

fn same_handlers(
    actual: &[crate::harness::types::HookHandlers],
    expected: &[&HookRegistration],
) -> bool {
    actual.len() == expected.len()
        && actual
            .iter()
            .zip(expected)
            .all(|(actual, expected)| Arc::ptr_eq(actual, &expected.handlers))
}

#[test]
fn collects_hooks_of_the_selected_extensions_in_extension_order_and_applies_field_defaults() {
    let local = create_registry();
    let before_tool = || -> ToolHooks {
        ToolHooks {
            before_tool: Some(Arc::new(|_, _, _| futures::future::ready(Ok(None)).boxed())),
            after_tool: None,
        }
    };
    let first = hook(tool_task(), before_tool());
    let second = hook(tool_task(), before_tool());
    let on_yield = hook(
        generation_task(),
        GenerationHooks {
            on_yield: Some(Arc::new(|_, _, _| futures::future::ready(Ok(None)).boxed())),
            ..GenerationHooks::default()
        },
    );
    local
        .install(extension("a", |a| {
            a.hooks = vec![first.clone(), on_yield.clone()];
        }))
        .unwrap();
    local
        .install(extension("b", |b| b.hooks = vec![second.clone()]))
        .unwrap();
    assert!(same_handlers(
        &agent_hooks(&resolve_quiet(None, &local.snapshot()), "pi.tool"),
        &[&first, &second]
    ));
    assert!(same_handlers(
        &agent_hooks(
            &resolve_quiet(Some(&selection(&["b", "a"])), &local.snapshot()),
            "pi.tool"
        ),
        &[&second, &first]
    ));
    assert!(agent_hooks(
        &resolve_quiet(Some(&selection(&["b"])), &local.snapshot()),
        "pi.generation"
    )
    .is_empty());

    let defaults = resolve_quiet(None, &local.snapshot());
    assert_eq!(defaults.model, None);
    assert_eq!(defaults.thinking_level, ModelThinkingLevel::Off);
    assert_eq!(defaults.cwd, None);
    let configured = resolve_quiet(
        Some(&AgentState {
            model: Some(ModelRef {
                provider: "p".to_owned(),
                model_id: "m".to_owned(),
            }),
            thinking_level: Some(ModelThinkingLevel::High),
            cwd: Some("/w".to_owned()),
            ..AgentState::default()
        }),
        &local.snapshot(),
    );
    assert_eq!(
        (configured.model, configured.thinking_level, configured.cwd),
        (
            Some(ModelRef {
                provider: "p".to_owned(),
                model_id: "m".to_owned(),
            }),
            ModelThinkingLevel::High,
            Some("/w".to_owned()),
        )
    );
}
