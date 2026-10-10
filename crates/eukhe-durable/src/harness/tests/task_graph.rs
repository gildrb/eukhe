//! Port of `test/harness-task-graph.test.ts`.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::with_cancel;
use eukhe_chord::delta::{apply_immutable, Op, Seg};
use eukhe_chord::json::{to_json, JsonValue};
use eukhe_chord::{AttachedReplicatedState, DeliveryKind};
use futures::FutureExt;

use super::support::context;
use super::task_support::{
    aborted, aborted_with, completed, deferred, eventually, flush, open_tasks, Deferred,
    OpenTasksOptions,
};
use crate::harness::types::TaskInspectionState;
use crate::harness::{RootOptions, TaskAbortResult, TaskGraph, TaskGraphNode, TaskGraphState};
use crate::session::tests::support::ControlledStorage;
use crate::storage::sqlite::{open_native_sqlite_storage, NativeSqliteStorageOptions};
use crate::storage::MemoryStorage;
use crate::tasks::{define_task, NextTaskState, Task, TaskDefinition};
use crate::types::{
    ConversationId, ConversationOwnership, EntryDraft, JoinPolicy, Storage, TaskId, TaskOptions,
    TaskOutcomeStatus, TaskOwnership,
};

type JsonTask = Task<JsonValue, JsonValue, JsonValue, ()>;

fn json(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON literal")
}

fn graph_of(value: JsonValue) -> TaskGraph {
    crate::harness::task_graph::graph_from_json(value)
}

fn options(ownership: TaskOwnership) -> TaskOptions {
    TaskOptions {
        ownership,
        conversation_id: None,
        background: None,
        abandon_on_restart: None,
    }
}

/// Gates of the [`family`] children.
#[derive(Clone)]
struct Gates {
    child: Deferred,
    late: Deferred,
}

/// A parent that creates a child task and a conversation it owns, waits for
/// the child, creates a second child, and completes while that child is
/// still live, so its outcome is held as `completing`.
fn family(gates: Gates) -> (JsonTask, JsonTask) {
    let child = define_task(
        TaskDefinition::new(
            "test.graph-child",
            1,
            |_: &JsonValue| Ok(json(r#"{"phase":"work"}"#)),
            |_, _, _| async { Ok(()) },
        )
        .phase("work", move |task, runtime, cx| {
            let gates = gates.clone();
            async move {
                if task.input["late"].as_bool() == Some(true) {
                    gates.late.wait().await;
                } else {
                    gates.child.wait().await;
                }
                runtime
                    .commit(|_, _| async { Ok(Some(completed(JsonValue::Null))) }, &cx)
                    .await
            }
        }),
    );
    let spawned = child.clone();
    let joined = child.clone();
    let parent = define_task(
        TaskDefinition::new(
            "test.graph-parent",
            1,
            |_: &JsonValue| Ok(json(r#"{"phase":"spawn"}"#)),
            |_, _, _| async { Ok(()) },
        )
        .phase("spawn", move |task, runtime, cx| {
            let child = spawned.clone();
            async move {
                let ownership = ConversationOwnership::Task { task_id: task.id };
                // Two conversations in a commit that leaves the parent's record unchanged.
                runtime
                    .commit(
                        move |tx, _| async move {
                            tx.create_conversation(ownership).await?;
                            tx.create_conversation(ownership).await?;
                            Ok(None)
                        },
                        &cx,
                    )
                    .await?;
                let parent = task.id;
                runtime
                    .commit(
                        move |tx, _| async move {
                            let created = tx
                                .create_task(
                                    child.erase().as_definition_ref(),
                                    json(r#"{"late":false}"#),
                                    options(TaskOwnership::Task { task_id: parent }),
                                )
                                .await?;
                            Ok(Some(NextTaskState::Waiting {
                                checkpoint: json(&format!(
                                    r#"{{"phase":"join","child":{created}}}"#
                                )),
                                on: vec![created],
                                policy: JoinPolicy::AllSettled,
                            }))
                        },
                        &cx,
                    )
                    .await
            }
        })
        .phase("join", move |task, runtime, cx| {
            let child = joined.clone();
            async move {
                let parent = task.id;
                runtime
                    .commit(
                        move |tx, _| async move {
                            tx.create_task(
                                child.erase().as_definition_ref(),
                                json(r#"{"late":true}"#),
                                options(TaskOwnership::Task { task_id: parent }),
                            )
                            .await?;
                            Ok(Some(NextTaskState::Running {
                                checkpoint: json(r#"{"phase":"finish"}"#),
                            }))
                        },
                        &cx,
                    )
                    .await
            }
        })
        .phase("finish", |_, runtime, cx| async move {
            runtime
                .commit(|_, _| async { Ok(Some(completed(JsonValue::Null))) }, &cx)
                .await
        }),
    );
    (parent, child)
}

fn gates_never() -> Gates {
    Gates {
        child: deferred(),
        late: deferred(),
    }
}

/// Node states by task kind, for compact assertions.
fn statuses(graph: &TaskGraph) -> BTreeMap<String, String> {
    graph
        .nodes()
        .unwrap()
        .into_iter()
        .map(|node| {
            (
                format!("{}#{}", node.kind, node.id),
                node.state.status().to_owned(),
            )
        })
        .collect()
}

fn graph(state: &AttachedReplicatedState) -> TaskGraph {
    graph_of(state.value())
}

type Seen = Arc<Mutex<Vec<JsonValue>>>;

async fn observe(harness: &crate::harness::Harness, seen: &Seen) -> AttachedReplicatedState {
    let opened = harness.task_graph(context()).await.unwrap();
    let sink = Arc::clone(seen);
    let disposer = opened.subscribe(move |value, _, delivery| {
        if delivery.kind == DeliveryKind::Update {
            sink.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(value);
        }
    });
    drop(disposer);
    opened
}

#[tokio::test]
#[expect(clippy::too_many_lines, reason = "one-to-one port of the TS test")]
async fn follows_every_live_task_through_its_statuses_owner_edges_and_owned_conversations() {
    let gates = Gates {
        child: deferred(),
        late: deferred(),
    };
    let (parent_task, child_task) = family(gates.clone());
    let opened = open_tasks(
        Arc::new(MemoryStorage::new()),
        &[parent_task.erase(), child_task.erase()],
        OpenTasksOptions::default(),
    )
    .await;
    let harness = opened.harness;
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    let seen: Seen = Arc::default();
    let mut state = observe(&harness, &seen).await;
    assert_eq!(state.value(), json(r#"{"tasks":{}}"#));

    let definition = parent_task.erase().as_definition_ref();
    let parent: TaskId = root
        .commit(
            move |tx| async move {
                tx.create_task(
                    definition,
                    JsonValue::Null,
                    options(TaskOwnership::Conversation),
                )
                .await
            },
            context(),
        )
        .await
        .unwrap();
    flush().await;
    assert_eq!(
        graph(&state).node(parent).unwrap(),
        Some(TaskGraphNode {
            id: parent,
            kind: "test.graph-parent".to_owned(),
            conversation_id: root.id(),
            owner: None,
            background: false,
            abort_requested: false,
            state: TaskGraphState::Pending {
                phase: Some("spawn".to_owned())
            },
            conversations: vec![],
        })
    );

    harness.resume().unwrap();
    let child_id = |state: &AttachedReplicatedState| {
        graph(state)
            .nodes()
            .unwrap()
            .into_iter()
            .find(|node| node.kind == "test.graph-child")
            .map(|node| node.id)
    };
    eventually(|| {
        let ready = graph(&state).tasks().len() == 2
            && child_id(&state).is_some_and(|id| {
                matches!(
                    graph(&state).node(id).unwrap().map(|node| node.state),
                    Some(TaskGraphState::Running { .. })
                )
            });
        async move { ready }
    })
    .await;
    let first = child_id(&state).unwrap();
    let parent_node = graph(&state).node(parent).unwrap().unwrap();
    assert_eq!(
        parent_node.state,
        TaskGraphState::Waiting {
            phase: Some("join".to_owned()),
            on: vec![first],
            policy: JoinPolicy::AllSettled
        }
    );
    assert_eq!(parent_node.conversations.len(), 2);
    let mut sorted = parent_node.conversations.clone();
    sorted.sort_unstable();
    assert_eq!(sorted, parent_node.conversations);
    let owned = parent_node.conversations[0];
    let first_node = graph(&state).node(first).unwrap().unwrap();
    assert_eq!(
        (first_node.owner, first_node.conversation_id),
        (Some(parent), root.id())
    );
    assert!(harness
        .conversation(owned, context())
        .await
        .unwrap()
        .is_some());
    // The advanced value equals a fresh build from Storage once the last observer left.
    let rebuild = |state: AttachedReplicatedState| {
        let harness = harness.clone();
        let seen = Arc::clone(&seen);
        async move {
            let advanced = state.value();
            state.dispose().unwrap();
            let rebuilt = observe(&harness, &seen).await;
            assert!(!rebuilt.value().strict_equals(&advanced));
            assert_eq!(rebuilt.value(), advanced);
            rebuilt
        }
    };
    state = rebuild(state).await;

    gates.child.resolve(());
    // The parent completes while the late child lives: its outcome is held.
    eventually(|| {
        let held = matches!(
            graph(&state).node(parent).unwrap().map(|node| node.state),
            Some(TaskGraphState::Completing { .. })
        );
        async move { held }
    })
    .await;
    assert_eq!(
        graph(&state).node(parent).unwrap().unwrap().state,
        TaskGraphState::Completing {
            outcome: TaskOutcomeStatus::Completed
        }
    );
    assert_eq!(graph(&state).node(first).unwrap(), None);
    // Owned conversations stay listed while the owner lives.
    assert_eq!(
        graph(&state).node(parent).unwrap().unwrap().conversations,
        parent_node.conversations
    );
    state = rebuild(state).await;

    gates.late.resolve(());
    harness.wait_for_task(parent, context()).await.unwrap();
    flush().await;
    assert_eq!(state.value(), json(r#"{"tasks":{}}"#));
    let seen = seen.lock().unwrap_or_else(PoisonError::into_inner).clone();
    // Every revision is one commit that changed a node; none repeats its predecessor.
    for pair in seen.windows(2) {
        assert_ne!(pair[0], pair[1]);
    }
    // The commit that created the two conversations published one revision setting them.
    assert!(seen.iter().any(|value| {
        graph_of(value.clone())
            .node(parent)
            .unwrap()
            .is_some_and(|node| node.conversations.len() == 2)
    }));
    state.dispose().unwrap();
    harness.close(context()).await.unwrap();
}

fn work_task(gate: Deferred) -> JsonTask {
    define_task(
        TaskDefinition::new(
            "test.graph-work",
            1,
            |_: &JsonValue| Ok(json(r#"{"phase":"work"}"#)),
            |_, runtime: crate::tasks::TaskRuntime<JsonValue, JsonValue, JsonValue, ()>, cx| async move {
                runtime
                    .commit(|_, _| async { Ok(Some(aborted_with("test"))) }, &cx)
                    .await
            },
        )
        .phase("work", move |_, runtime, cx| {
            let gate = gate.clone();
            async move {
                let signal = runtime.signal();
                tokio::select! {
                    () = gate.wait() => {}
                    error = aborted(&signal) => return Err(error),
                }
                runtime
                    .commit(|_, _| async { Ok(Some(completed(JsonValue::Null))) }, &cx)
                    .await
            }
        }),
    )
}

#[tokio::test]
#[expect(clippy::too_many_lines, reason = "one-to-one port of the TS test")]
async fn builds_from_committed_tasks_shows_surviving_tasks_as_pending_after_reopen_and_marks_aborts(
) {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("session.sqlite");
    let gate: Deferred = deferred();
    let work = work_task(gate.clone());
    let sqlite = || async {
        Arc::new(
            open_native_sqlite_storage(&path, NativeSqliteStorageOptions::default())
                .await
                .unwrap(),
        ) as Arc<dyn Storage>
    };
    let first = open_tasks(sqlite().await, &[work.erase()], OpenTasksOptions::default()).await;
    let first_root = first
        .harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    let definition = work.erase().as_definition_ref();
    let (foreground, background, owned) = first_root
        .commit(
            move |tx| async move {
                let foreground = tx
                    .create_task(
                        Arc::clone(&definition),
                        JsonValue::Null,
                        options(TaskOwnership::Conversation),
                    )
                    .await?;
                let background = tx
                    .create_task(
                        definition,
                        JsonValue::Null,
                        TaskOptions {
                            background: Some(true),
                            ..options(TaskOwnership::Conversation)
                        },
                    )
                    .await?;
                let owned = tx
                    .create_conversation(ConversationOwnership::Task {
                        task_id: foreground,
                    })
                    .await?;
                Ok((foreground, background, owned.id))
            },
            context(),
        )
        .await
        .unwrap();
    first.harness.resume().unwrap();
    eventually(|| {
        let harness = first.harness.clone();
        async move {
            harness
                .inspect(context())
                .await
                .unwrap()
                .tasks
                .iter()
                .all(|task| matches!(task.state, TaskInspectionState::Running))
        }
    })
    .await;
    let running = first.harness.task_graph(context()).await.unwrap();
    let expected = |status: &str| {
        BTreeMap::from([
            (format!("test.graph-work#{foreground}"), status.to_owned()),
            (format!("test.graph-work#{background}"), status.to_owned()),
        ])
    };
    assert_eq!(statuses(&graph(&running)), expected("running"));
    first.harness.close(context()).await.unwrap();

    // Acquired after reopen: built from the committed records and owner edges; open reconciled running to pending.
    let opened = open_tasks(sqlite().await, &[work.erase()], OpenTasksOptions::default()).await;
    let harness = opened.harness;
    let watch = harness.watch_task_graph(context()).await.unwrap();
    assert_eq!(statuses(&watch.value()), expected("pending"));
    assert_eq!(
        watch
            .value()
            .node(foreground)
            .unwrap()
            .unwrap()
            .conversations,
        vec![owned]
    );
    assert!(watch.value().node(background).unwrap().unwrap().background);

    // Exact frames: replaying their operations from the acquisition revision gives each delivered value.
    let replica = Arc::new(Mutex::new(watch.value().json().clone()));
    let frames: Arc<Mutex<Vec<Vec<Op>>>> = Arc::default();
    {
        let (replica, frames) = (Arc::clone(&replica), Arc::clone(&frames));
        watch
            .start(Arc::new(
                move |value: TaskGraph, ops: crate::session::Ops, _| {
                    let mut replica = replica.lock().unwrap_or_else(PoisonError::into_inner);
                    *replica = apply_immutable(&replica, &ops).unwrap();
                    assert_eq!(*replica, *value.json());
                    frames
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .push(ops.to_vec());
                    async { Ok(()) }.boxed()
                },
            ))
            .unwrap();
    }
    harness.resume().unwrap();
    eventually(|| {
        let running = matches!(
            watch
                .value()
                .node(background)
                .unwrap()
                .map(|node| node.state),
            Some(TaskGraphState::Running { .. })
        );
        async move { running }
    })
    .await;
    assert_eq!(
        harness.abort_task(background, context()).await.unwrap(),
        TaskAbortResult::Marked
    );
    harness.wait_for_task(background, context()).await.unwrap();
    flush().await;
    let frames = frames
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    let key = background.to_string();
    assert!(frames.iter().any(|ops| matches!(
        ops.as_slice(),
        [Op::Set(path, node)] if *path == [Seg::from("tasks"), Seg::from(key.as_str())]
            && node["abortRequested"] == JsonValue::Bool(true)
    )));
    assert_eq!(
        frames.last().unwrap().as_slice(),
        [Op::Delete(vec![
            Seg::from("tasks"),
            Seg::from(key.as_str())
        ])]
    );
    let keys: Vec<String> = graph_of(
        replica
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone(),
    )
    .tasks()
    .keys()
    .map(str::to_owned)
    .collect();
    assert_eq!(keys, [foreground.to_string()]);
    watch.stop().await;
    gate.resolve(());
    harness.wait_for_task(foreground, context()).await.unwrap();
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn lists_owned_conversations_in_id_order_whatever_order_one_commit_creates_them_in() {
    let gate: Deferred = deferred();
    let created: Arc<Mutex<Vec<ConversationId>>> = Arc::default();
    let spawner = {
        let (gate, created) = (gate.clone(), Arc::clone(&created));
        define_task(
            TaskDefinition::<JsonValue, JsonValue, JsonValue, ()>::new(
                "test.graph-spawner",
                1,
                |_: &JsonValue| Ok(json(r#"{"phase":"spawn"}"#)),
                |_, _, _| async { Ok(()) },
            )
            .phase("spawn", move |task, runtime, cx| {
                let (gate, created) = (gate.clone(), Arc::clone(&created));
                async move {
                    let ownership = ConversationOwnership::Task { task_id: task.id };
                    let at = serde_json::from_value(serde_json::Value::from(&task.input["at"]))
                        .expect("entry ID input");
                    let conversation_id = runtime.conversation_id();
                    runtime
                        .commit(
                            move |tx, _| async move {
                                let (forked, fresh) = futures::join!(
                                    tx.fork_conversation(conversation_id, at, ownership),
                                    tx.create_conversation(ownership)
                                );
                                let mut created =
                                    created.lock().unwrap_or_else(PoisonError::into_inner);
                                created.push(forked?.id);
                                created.push(fresh?.id);
                                Ok(None)
                            },
                            &cx,
                        )
                        .await?;
                    gate.wait().await;
                    runtime
                        .commit(|_, _| async { Ok(Some(completed(JsonValue::Null))) }, &cx)
                        .await
                }
            }),
        )
    };
    let opened = open_tasks(
        Arc::new(MemoryStorage::new()),
        &[spawner.erase()],
        OpenTasksOptions::default(),
    )
    .await;
    let harness = opened.harness;
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    let state = harness.task_graph(context()).await.unwrap();
    let (root_id, definition) = (root.id(), spawner.erase().as_definition_ref());
    let id: TaskId = root
        .commit(
            move |tx| async move {
                let entry = tx.append_entry(root_id, EntryDraft::new("note")).await?;
                tx.create_task(
                    definition,
                    to_json(&serde_json::json!({ "at": entry.id }))?,
                    options(TaskOwnership::Conversation),
                )
                .await
            },
            context(),
        )
        .await
        .unwrap();
    harness.resume().unwrap();
    eventually(|| {
        let ready = graph(&state)
            .node(id)
            .unwrap()
            .is_some_and(|node| node.conversations.len() == 2);
        async move { ready }
    })
    .await;
    let advanced = state.value();
    let mut expected = created
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    expected.sort_unstable();
    assert_eq!(
        graph_of(advanced.clone())
            .node(id)
            .unwrap()
            .unwrap()
            .conversations,
        expected
    );
    state.dispose().unwrap();
    let rebuilt = harness.task_graph(context()).await.unwrap();
    assert_eq!(rebuilt.value(), advanced);
    rebuilt.dispose().unwrap();
    gate.resolve(());
    harness.wait_for_task(id, context()).await.unwrap();
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn registers_nothing_for_an_acquisition_cancelled_while_it_waits_for_the_line() {
    let storage = ControlledStorage::new();
    let opened = open_tasks(
        Arc::clone(&storage) as Arc<dyn Storage>,
        &[],
        OpenTasksOptions::default(),
    )
    .await;
    let harness = opened.harness;
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    let (_, child) = family(gates_never());
    let definition = child.erase().as_definition_ref();
    root.commit(
        move |tx| async move {
            tx.create_task(
                definition,
                json(r#"{"late":false}"#),
                options(TaskOwnership::Conversation),
            )
            .await
        },
        context(),
    )
    .await
    .unwrap();
    let held = storage.hold_commits();
    let root_id = root.id();
    let blocking = tokio::spawn(harness.commit(
        move |tx| async move {
            tx.append_entry(root_id, EntryDraft::new("blocker")).await?;
            Ok(())
        },
        context(),
    ));
    held.entered().await;
    let (cancelled_context, cancel) = with_cancel(context());
    let cancelled = tokio::spawn(harness.watch_task_graph(&cancelled_context));
    cancel.cancel(Some(Arc::new(std::io::Error::other("cancelled"))));
    held.release();
    blocking.await.unwrap().unwrap();
    let error = cancelled.await.unwrap().unwrap_err();
    assert!(error.to_string().contains("cancelled"), "{error}");
    // No observer kept the mount: each new observer builds a new revision.
    let first = harness.task_graph(context()).await.unwrap();
    let value = first.value();
    first.dispose().unwrap();
    let second = harness.task_graph(context()).await.unwrap();
    assert!(!second.value().strict_equals(&value));
    assert_eq!(second.value(), value);
    second.dispose().unwrap();
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn publishes_no_revision_for_a_commit_that_changes_no_node_and_shares_one_mount_between_observers(
) {
    let gate: Deferred = deferred();
    let reached: Deferred = deferred();
    let memo = {
        let (gate, reached) = (gate.clone(), reached.clone());
        define_task(
            TaskDefinition::<JsonValue, JsonValue, JsonValue, ()>::new(
                "test.graph-memo",
                1,
                |_: &JsonValue| Ok(json(r#"{"phase":"work"}"#)),
                |_, _, _| async { Ok(()) },
            )
            .phase("work", move |_, runtime, cx| {
                let (gate, reached) = (gate.clone(), reached.clone());
                async move {
                    runtime.memo_or("seen", &true, &cx).await?;
                    reached.resolve(());
                    gate.wait().await;
                    runtime
                        .commit(|_, _| async { Ok(Some(completed(JsonValue::Null))) }, &cx)
                        .await
                }
            }),
        )
    };
    let opened = open_tasks(
        Arc::new(MemoryStorage::new()),
        &[memo.erase()],
        OpenTasksOptions::default(),
    )
    .await;
    let harness = opened.harness;
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    let definition = memo.erase().as_definition_ref();
    let id: TaskId = root
        .commit(
            move |tx| async move {
                tx.create_task(
                    definition,
                    JsonValue::Null,
                    options(TaskOwnership::Conversation),
                )
                .await
            },
            context(),
        )
        .await
        .unwrap();
    let first = harness.task_graph(context()).await.unwrap();
    let second = harness.task_graph(context()).await.unwrap();
    assert!(second.value().strict_equals(&first.value()));
    let updates: Arc<Mutex<Vec<String>>> = Arc::default();
    let sink = Arc::clone(&updates);
    let disposer = first.subscribe(move |value, _, delivery| {
        if delivery.kind == DeliveryKind::Update {
            let status = graph_of(value)
                .node(id)
                .unwrap()
                .map_or("gone", |node| node.state.status());
            sink.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(status.to_owned());
        }
    });
    drop(disposer);
    harness.resume().unwrap();
    reached.wait().await;
    flush().await;
    // Reservation changed the node; the memo commit did not.
    assert_eq!(
        *updates.lock().unwrap_or_else(PoisonError::into_inner),
        ["running"]
    );
    gate.resolve(());
    harness.wait_for_task(id, context()).await.unwrap();
    flush().await;
    assert_eq!(
        *updates.lock().unwrap_or_else(PoisonError::into_inner),
        ["running", "gone"]
    );
    let last = first.value();
    first.dispose().unwrap();
    second.dispose().unwrap();
    // No observer is left, so the mount was dropped: a new observer builds a new revision.
    let rebuilt = harness.task_graph(context()).await.unwrap();
    assert_eq!(rebuilt.value(), last);
    assert!(!rebuilt.value().strict_equals(&last));
    rebuilt.dispose().unwrap();
    harness.close(context()).await.unwrap();
}
