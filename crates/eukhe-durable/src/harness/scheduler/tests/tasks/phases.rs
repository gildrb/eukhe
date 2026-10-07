//! `describe("task phases")`.

use std::sync::Arc;

use eukhe_chord::context::{with_cancel, Context};
use eukhe_chord::json::JsonValue;
use eukhe_types::pi_ai::{Message, ModelThinkingLevel};
use serde::{Deserialize, Serialize};

use super::{
    advance, complete, completed_outcome, create, faulted, json, lock, one_step, open_root, reason,
    shared, start, OpenedRoot, Shared, StepRuntime,
};
use crate::documents::{DocDefinition, TaskDoc};
use crate::entries::Entry;
use crate::harness::agent::AGENT_DOC;
use crate::harness::tests::support::{add_hooks, add_tool, context, tool_described, user};
use crate::harness::tests::task_support::{completed, deferred, eventually, flush};
use crate::harness::types::{
    AgentChange, ConversationCreateOptions, FieldChange, RegistrySnapshot,
};
use crate::session::{SessionError, SessionResult};
use crate::tasks::{define_task, NextTaskState, TaskDefinition, TaskRuntime, TaskRuntimeBackend};
use crate::types::{
    ConversationOwnership, EntryDraft, EntryId, JoinPolicy, TaskId, TaskOutcome, TaskOutcomeStatus,
    TaskState,
};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
enum Count {
    Count { n: u64 },
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
struct CounterInput {
    to: u64,
}

#[tokio::test]
async fn continues_one_invocation_through_checkpoint_progress_and_completes_with_a_typed_result() {
    let seen = shared(Vec::<u64>::new());
    let runtimes = shared(Vec::<Arc<dyn TaskRuntimeBackend>>::new());
    let counter = define_task(
        TaskDefinition::<CounterInput, Count, u64, ()>::new(
            "test.counter",
            1,
            |_: &CounterInput| Ok(Count::Count { n: 0 }),
            |_task, _runtime, _cx| async { Ok(()) },
        )
        .phase("count", {
            let (seen, runtimes) = (seen.clone(), runtimes.clone());
            move |task, runtime: TaskRuntime<CounterInput, Count, u64, ()>, cx: Context| {
                let Count::Count { n } = task.checkpoint;
                lock(&seen).push(n);
                {
                    let mut runtimes = lock(&runtimes);
                    if !runtimes
                        .iter()
                        .any(|known| Arc::ptr_eq(known, runtime.backend()))
                    {
                        runtimes.push(Arc::clone(runtime.backend()));
                    }
                }
                let to = task.input.to;
                async move {
                    runtime
                        .commit(
                            move |_tx, current| async move {
                                let Count::Count { n } = current.checkpoint;
                                let n = n + 1;
                                Ok(Some(if n == to {
                                    completed(n)
                                } else {
                                    NextTaskState::Running {
                                        checkpoint: Count::Count { n },
                                    }
                                }))
                            },
                            &cx,
                        )
                        .await
                }
            }
        }),
    );
    let OpenedRoot { harness, root, .. } = open_root(&[counter.erase()]).await;
    let id = create(&root, &counter, &CounterInput { to: 3 }).await;
    harness.resume().unwrap();
    let receipt = harness
        .wait_for_task(id, context())
        .await
        .unwrap()
        .decode::<u64>()
        .unwrap();
    let result = match receipt.outcome {
        TaskOutcome::Completed { result } => Some(result),
        _ => None,
    };
    assert_eq!(result, Some(3));
    assert_eq!(*lock(&seen), [0, 1, 2]);
    assert_eq!(lock(&runtimes).len(), 1);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn faults_a_phase_without_durable_progress_and_a_throwing_phase() {
    let idle = one_step::<(), _, _>("test.idle", |_task, _runtime, _cx| async { Ok(()) });
    let document_only = one_step::<(), _, _>(
        "test.document-only",
        |_task, runtime: StepRuntime, cx: Context| async move {
            // A commit that returns no state is not progress.
            runtime
                .commit(|_tx, _current| async { Ok(None) }, &cx)
                .await
        },
    );
    let throws = one_step::<(), _, _>("test.throws", |_task, _runtime, _cx| async {
        Err(SessionError::error("boom"))
    });
    let OpenedRoot { harness, root, .. } =
        open_root(&[idle.erase(), document_only.erase(), throws.erase()]).await;
    let ids = [
        start(&root, &idle).await,
        start(&root, &document_only).await,
        start(&root, &throws).await,
    ];
    harness.resume().unwrap();
    let mut outcomes = Vec::new();
    for id in ids {
        outcomes.push(super::outcome(&harness, id).await);
    }
    assert_eq!(
        outcomes,
        [
            faulted("Task test.idle phase run returned without durable progress"),
            faulted("Task test.document-only phase run returned without durable progress"),
            faulted("boom"),
        ]
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_a_committed_terminal_outcome_when_the_handler_throws_afterwards() {
    let late_commit: Shared<Option<SessionResult<()>>> = shared(None);
    let done = one_step::<String, _, _>("test.done", {
        let late_commit = late_commit.clone();
        move |_task, runtime: StepRuntime<String>, cx: Context| {
            let late_commit = late_commit.clone();
            async move {
                complete(&runtime, "ok".to_owned(), &cx).await?;
                let late = runtime
                    .commit(|_tx, _current| async { Ok(None) }, &cx)
                    .await;
                *lock(&late_commit) = Some(late);
                Err(SessionError::error("after terminal"))
            }
        }
    });
    let OpenedRoot { harness, root, .. } = open_root(&[done.erase()]).await;
    let id = start(&root, &done).await;
    harness.resume().unwrap();
    assert_eq!(super::outcome(&harness, id).await, completed_outcome(&"ok"));
    eventually(|| std::future::ready(lock(&late_commit).is_some())).await;
    let late = lock(&late_commit).take().unwrap();
    super::assert_rejects(late, &format!("Task {id} is terminal"));
    harness.close(context()).await.unwrap();
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
enum Collect {
    Collect { items: Vec<String> },
}

#[tokio::test]
async fn compares_checkpoints_by_value_including_arrays() {
    let collect = define_task(
        TaskDefinition::<(), Collect, (), ()>::new(
            "test.collect",
            1,
            |(): &()| Ok(Collect::Collect { items: Vec::new() }),
            |_task, _runtime, _cx| async { Ok(()) },
        )
        .phase("collect", |task, runtime, cx: Context| {
            let Collect::Collect { items } = task.checkpoint;
            // Two rounds of progress, then an equal copy of the checkpoint, which is no progress.
            let next = if items.len() < 2 {
                let mut next = items.clone();
                next.push(format!("item{}", items.len()));
                next
            } else {
                items
            };
            async move { advance(&runtime, Collect::Collect { items: next }, &cx).await }
        }),
    );
    let OpenedRoot { harness, root, .. } = open_root(&[collect.erase()]).await;
    let id = create(&root, &collect, &()).await;
    harness.resume().unwrap();
    assert_eq!(
        super::outcome(&harness, id).await,
        faulted("Task test.collect phase collect returned without durable progress")
    );
    harness.close(context()).await.unwrap();
}

#[derive(Debug, Default, Clone, PartialEq, Serialize, Deserialize)]
struct Lines {
    lines: Vec<String>,
}

static PROGRESS: TaskDoc<Lines> = match TaskDoc::define(DocDefinition {
    kind: "test.task-progress",
    version: 1,
    initial: Lines::default,
    migrate: None,
    checkpoint_when: None,
}) {
    Ok(token) => token,
    Err(_) => panic!("test.task-progress has a valid version"),
};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
enum Writer {
    Write,
    Answer,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct WriterResult {
    entry_id: EntryId,
}

/// What the `write` phase read from its memos.
#[derive(Debug, PartialEq)]
struct MemoReads {
    before: Option<String>,
    winners: [String; 2],
    after: Option<String>,
    inherited: Option<String>,
    own: String,
}

#[tokio::test]
#[expect(
    clippy::too_many_lines,
    reason = "one TS test with its inline task definition"
)]
async fn commits_results_with_entries_atomically_keeps_memos_until_terminal_and_retires_task_documents(
) {
    let answer: Entry = Entry::define("answer").unwrap();
    let child = one_step::<(), _, _>(
        "test.child",
        |_task, runtime: StepRuntime, cx: Context| async move { complete(&runtime, (), &cx).await },
    );
    let child_id: Shared<Option<TaskId>> = shared(None);
    let progress_seen: Shared<Option<JsonValue>> = shared(None);
    let memo_reads: Shared<Option<MemoReads>> = shared(None);
    let answer_memos: Shared<Option<JsonValue>> = shared(None);
    let writer = define_task(
        TaskDefinition::<(), Writer, WriterResult, ()>::new(
            "test.writer",
            1,
            |(): &()| Ok(Writer::Write),
            |_task, _runtime, _cx| async { Ok(()) },
        )
        .phase("write", {
            let (child, child_id, memo_reads) =
                (child.clone(), child_id.clone(), memo_reads.clone());
            move |task, runtime: TaskRuntime<(), Writer, WriterResult, ()>, cx: Context| {
                let (child, child_id, memo_reads) =
                    (child.clone(), child_id.clone(), memo_reads.clone());
                async move {
                    let before = runtime.memo::<String>("choice", &cx).await?;
                    let (first, second) = futures::join!(
                        runtime.memo_or("choice", &"a".to_owned(), &cx),
                        runtime.memo_or("choice", &"b".to_owned(), &cx)
                    );
                    let winners = [first?, second?];
                    let after = runtime.memo::<String>("choice", &cx).await?;
                    // Memo names never resolve to inherited object properties.
                    let inherited = runtime.memo::<String>("toString", &cx).await?;
                    let own = runtime.memo_or("toString", &"own".to_owned(), &cx).await?;
                    *lock(&memo_reads) = Some(MemoReads {
                        before,
                        winners,
                        after,
                        inherited,
                        own,
                    });
                    let task_id = task.id.erase();
                    let definition = child.erase().as_definition_ref();
                    runtime
                        .commit(
                            move |tx, _current| async move {
                                tx.doc(&PROGRESS, task_id)
                                    .await?
                                    .child("lines")?
                                    .push(["wrote"])?;
                                // Task creation defaults to the task's own conversation.
                                let id = tx
                                    .create_task(
                                        definition,
                                        JsonValue::Null,
                                        crate::types::TaskOptions {
                                            ownership: crate::types::TaskOwnership::Conversation,
                                            conversation_id: None,
                                            background: None,
                                        },
                                    )
                                    .await?;
                                *lock(&child_id) = Some(id);
                                Ok(Some(NextTaskState::Running {
                                    checkpoint: Writer::Answer,
                                }))
                            },
                            &cx,
                        )
                        .await
                }
            }
        })
        .phase("answer", {
            let (progress_seen, answer_memos) = (progress_seen.clone(), answer_memos.clone());
            move |task, runtime: TaskRuntime<(), Writer, WriterResult, ()>, cx: Context| {
                *lock(&answer_memos) = task.memos.clone().map(JsonValue::Object);
                let progress_seen = progress_seen.clone();
                let task_id = task.id.erase();
                async move {
                    runtime
                        .commit(
                            move |tx, _current| async move {
                                let lines =
                                    tx.doc(&PROGRESS, task_id).await?.child("lines")?.value()?;
                                *lock(&progress_seen) = Some(lines);
                                Ok(None)
                            },
                            &cx,
                        )
                        .await?;
                    runtime
                        .commit(
                            |tx, current| async move {
                                let entry = tx
                                    .append_entry(
                                        current.conversation_id,
                                        EntryDraft {
                                            model: Some(vec![Message::User(user("done"))]),
                                            ..EntryDraft::new("answer")
                                        },
                                    )
                                    .await?;
                                Ok(Some(completed(WriterResult { entry_id: entry.id })))
                            },
                            &cx,
                        )
                        .await
                }
            }
        }),
    );
    let OpenedRoot { harness, root, .. } = open_root(&[writer.erase(), child.erase()]).await;
    let conversation = harness
        .create_conversation(
            ConversationCreateOptions::new(ConversationOwnership::Ownerless),
            context(),
        )
        .await
        .unwrap();
    let id = create(&conversation, &writer, &()).await;
    harness.resume().unwrap();
    let receipt = harness.wait_for_task(id, context()).await.unwrap();
    assert_eq!(
        lock(&memo_reads).take(),
        Some(MemoReads {
            before: None,
            winners: ["a".to_owned(), "a".to_owned()],
            after: Some("a".to_owned()),
            inherited: None,
            own: "own".to_owned(),
        })
    );
    assert_eq!(
        lock(&answer_memos).take(),
        Some(json(r#"{"choice":"a","toString":"own"}"#))
    );
    // A receipt has no checkpoint (its state is the outcome) and no memos.
    assert_eq!(receipt.memos, None);
    let TaskOutcome::Completed { result } =
        receipt.clone().decode::<WriterResult>().unwrap().outcome
    else {
        panic!("expected completion");
    };
    let entry = harness
        .commit(
            move |tx| async move { tx.entry(result.entry_id).await },
            context(),
        )
        .await
        .unwrap();
    assert!(answer.is(entry.as_ref()));
    assert_eq!(
        entry.map(|entry| entry.conversation_id),
        Some(conversation.id())
    );
    assert_eq!(lock(&progress_seen).take(), Some(json(r#"["wrote"]"#)));
    assert_eq!(
        harness
            .snapshot(&PROGRESS, id.erase(), context())
            .await
            .unwrap(),
        None
    );
    assert_eq!(
        harness.get_task(id, context()).await.unwrap(),
        Some(receipt.into_record())
    );
    let child_id = lock(&child_id).expect("the child was created");
    assert_eq!(
        harness
            .wait_for_task(child_id, context())
            .await
            .unwrap()
            .conversation_id,
        conversation.id()
    );
    assert_ne!(root.id(), conversation.id());
    harness.close(context()).await.unwrap();
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
enum Wait {
    Wait,
    Resume,
}

#[tokio::test]
async fn resumes_a_waiting_task_once_every_task_in_on_is_terminal_whatever_the_outcome() {
    let gate = deferred::<()>();
    let order = shared(Vec::<String>::new());
    let on: Shared<Vec<TaskId>> = shared(Vec::new());
    let outcomes = shared(Vec::<TaskOutcomeStatus>::new());
    let waiter =
        define_task(
            TaskDefinition::<(), Wait, (), ()>::new(
                "test.waiter",
                1,
                |(): &()| Ok(Wait::Wait),
                |_task, runtime, cx: Context| async move {
                    super::abort_with(&runtime, "test", &cx).await
                },
            )
            .phase("wait", {
                let (order, on) = (order.clone(), on.clone());
                move |_task, runtime: TaskRuntime<(), Wait, (), ()>, cx: Context| {
                    lock(&order).push("wait".to_owned());
                    let on = lock(&on).clone();
                    async move {
                        runtime
                            .commit(
                                move |_tx, _current| async move {
                                    Ok(Some(NextTaskState::Waiting {
                                        checkpoint: Wait::Resume,
                                        on,
                                        policy: JoinPolicy::AllSettled,
                                    }))
                                },
                                &cx,
                            )
                            .await
                    }
                }
            })
            .phase("resume", {
                let (order, on, outcomes) = (order.clone(), on.clone(), outcomes.clone());
                move |_task, runtime: TaskRuntime<(), Wait, (), ()>, cx: Context| {
                    lock(&order).push("resume".to_owned());
                    let (on, outcomes) = (lock(&on).clone(), outcomes.clone());
                    async move {
                        let settled = runtime.outcomes::<JsonValue>(&on, &cx).await?;
                        *lock(&outcomes) = settled.iter().map(TaskOutcome::status).collect();
                        complete(&runtime, (), &cx).await
                    }
                }
            }),
        );
    let first = one_step::<(), _, _>("test.first", {
        let (order, gate) = (order.clone(), gate.clone());
        move |_task, runtime: StepRuntime, cx: Context| {
            lock(&order).push("first".to_owned());
            let opened = gate.wait();
            async move {
                opened.await;
                complete(&runtime, (), &cx).await
            }
        }
    });
    let faulting = one_step::<(), _, _>("test.faulting", {
        let order = order.clone();
        move |_task, _runtime, _cx| {
            lock(&order).push("faulting".to_owned());
            async { Err(SessionError::error("fails")) }
        }
    });
    let OpenedRoot { harness, root, .. } =
        open_root(&[first.erase(), faulting.erase(), waiter.erase()]).await;
    let first_id = start(&root, &first).await.erase();
    let faulting_id = start(&root, &faulting).await.erase();
    *lock(&on) = vec![first_id, faulting_id];
    let waiter_id = create(&root, &waiter, &()).await;
    harness.resume().unwrap();
    eventually(|| std::future::ready(lock(&order).len() == 3)).await;
    flush().await;
    let mut sorted = lock(&order).clone();
    sorted.sort();
    assert_eq!(sorted, ["faulting", "first", "wait"]);
    let record = harness
        .get_task(waiter_id, context())
        .await
        .unwrap()
        .unwrap();
    match record.state {
        TaskState::Waiting { on: waiting_on, .. } => assert_eq!(waiting_on, *lock(&on)),
        state => panic!("expected waiting, got {state:?}"),
    }
    gate.resolve(());
    harness.wait_for_task(waiter_id, context()).await.unwrap();
    assert_eq!(lock(&order).last().map(String::as_str), Some("resume"));
    assert_eq!(
        *lock(&outcomes),
        [TaskOutcomeStatus::Completed, TaskOutcomeStatus::Faulted]
    );
    harness.close(context()).await.unwrap();
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
enum Ab {
    A,
    B,
}

/// One phase observation: the phase, what it saw, and whether a value stayed
/// the same within the phase.
type PhaseSeen<T> = (String, T, Option<bool>);

fn tool_names(snapshot: &RegistrySnapshot) -> Vec<String> {
    snapshot
        .tools()
        .iter()
        .map(|installed| installed.tool.name.clone())
        .collect()
}

#[tokio::test]
async fn keeps_one_registry_snapshot_per_phase_and_refreshes_it_at_the_phase_boundary() {
    let seen: Shared<Vec<PhaseSeen<Vec<String>>>> = shared(Vec::new());
    let phase_gate = deferred::<()>();
    let entered = deferred::<()>();
    let snapshots = define_task(
        TaskDefinition::<(), Ab, (), ()>::new(
            "test.snapshots",
            1,
            |(): &()| Ok(Ab::A),
            |_task, _runtime, _cx| async { Ok(()) },
        )
        .phase("a", {
            let (seen, phase_gate, entered) = (seen.clone(), phase_gate.clone(), entered.clone());
            move |_task, runtime: TaskRuntime<(), Ab, (), ()>, cx: Context| {
                let before = runtime.registry();
                entered.resolve(());
                let opened = phase_gate.wait();
                let seen = seen.clone();
                async move {
                    opened.await;
                    let now = runtime.registry();
                    lock(&seen).push((
                        "a".to_owned(),
                        tool_names(&now),
                        Some(RegistrySnapshot::ptr_eq(&now, &before)),
                    ));
                    advance(&runtime, Ab::B, &cx).await
                }
            }
        })
        .phase("b", {
            let seen = seen.clone();
            move |_task, runtime: TaskRuntime<(), Ab, (), ()>, cx: Context| {
                lock(&seen).push(("b".to_owned(), tool_names(&runtime.registry()), Some(true)));
                async move { complete(&runtime, (), &cx).await }
            }
        }),
    );
    let OpenedRoot {
        harness,
        registry,
        root,
        ..
    } = open_root(&[snapshots.erase()]).await;
    let id = create(&root, &snapshots, &()).await;
    harness.resume().unwrap();
    entered.wait().await;
    add_tool(&registry, tool_described("late", "late"), None).unwrap();
    phase_gate.resolve(());
    harness.wait_for_task(id, context()).await.unwrap();
    assert_eq!(
        *lock(&seen),
        [
            ("a".to_owned(), Vec::<String>::new(), Some(true)),
            ("b".to_owned(), vec!["late".to_owned()], Some(true)),
        ]
    );
    harness.close(context()).await.unwrap();
}

/// TS `PingHooks`.
#[derive(Clone)]
struct PingHooks {
    ping: Option<Arc<dyn Fn() + Send + Sync>>,
}

async fn ping(
    runtime: &TaskRuntime<(), Ab, (), PingHooks>,
    pings: &Shared<Vec<String>>,
) -> SessionResult<Vec<String>> {
    lock(pings).clear();
    runtime
        .hooks()
        .each(
            |hooks: &PingHooks| hooks.ping.clone(),
            |handler| async move {
                handler();
                Ok(())
            },
        )
        .await?;
    Ok(lock(pings).clone())
}

/// One `seen` row of the agent phases test.
type AgentSeen = (String, Vec<String>, ModelThinkingLevel, Option<bool>);

#[tokio::test]
#[expect(
    clippy::too_many_lines,
    reason = "one TS test with its inline task definition"
)]
async fn resolves_the_agent_at_first_use_in_a_phase_from_its_snapshot_keeps_it_for_the_phase_and_anew_at_the_next(
) {
    let pings = shared(Vec::<String>::new());
    let seen: Shared<Vec<AgentSeen>> = shared(Vec::new());
    let before_use = deferred::<()>();
    let after_use = deferred::<()>();
    let waiting_before_use = deferred::<()>();
    let waiting_after_use = deferred::<()>();
    let phases = define_task(
        TaskDefinition::<(), Ab, (), PingHooks>::new(
            "test.agent-phases",
            1,
            |(): &()| Ok(Ab::A),
            |_task, _runtime, _cx| async { Ok(()) },
        )
        .phase("a", {
            let (pings, seen) = (pings.clone(), seen.clone());
            let (before_use, after_use) = (before_use.clone(), after_use.clone());
            let (waiting_before_use, waiting_after_use) =
                (waiting_before_use.clone(), waiting_after_use.clone());
            move |_task, runtime: TaskRuntime<(), Ab, (), PingHooks>, cx: Context| {
                let (pings, seen) = (pings.clone(), seen.clone());
                let (before_use, after_use) = (before_use.wait(), after_use.wait());
                let waiting_after_use = waiting_after_use.clone();
                waiting_before_use.resolve(());
                async move {
                    before_use.await;
                    let first = runtime.agent(&cx).await?;
                    let row = (
                        "a".to_owned(),
                        ping(&runtime, &pings).await?,
                        first.thinking_level,
                        None,
                    );
                    lock(&seen).push(row);
                    waiting_after_use.resolve(());
                    after_use.await;
                    let second = runtime.agent(&cx).await?;
                    let row = (
                        "a".to_owned(),
                        ping(&runtime, &pings).await?,
                        second.thinking_level,
                        Some(Arc::ptr_eq(&second, &first)),
                    );
                    lock(&seen).push(row);
                    advance(&runtime, Ab::B, &cx).await
                }
            }
        })
        .phase("b", {
            let (pings, seen) = (pings.clone(), seen.clone());
            move |_task, runtime: TaskRuntime<(), Ab, (), PingHooks>, cx: Context| {
                let (pings, seen) = (pings.clone(), seen.clone());
                async move {
                    let agent = runtime.agent(&cx).await?;
                    let row = (
                        "b".to_owned(),
                        ping(&runtime, &pings).await?,
                        agent.thinking_level,
                        None,
                    );
                    lock(&seen).push(row);
                    complete(&runtime, (), &cx).await
                }
            }
        }),
    );
    let OpenedRoot {
        harness,
        registry,
        root,
        ..
    } = open_root(&[phases.erase()]).await;
    let pinger = |label: &'static str| {
        let pings = pings.clone();
        PingHooks {
            ping: Some(Arc::new(move || lock(&pings).push(label.to_owned()))),
        }
    };
    add_hooks(&registry, &phases, pinger("before"), None).unwrap();
    let id = create(&root, &phases, &()).await;
    harness.resume().unwrap();

    // Configured during the phase but before its first use: the lazy resolution reads it.
    waiting_before_use.wait().await;
    root.configure(thinking(ModelThinkingLevel::Low), context())
        .await
        .unwrap();
    before_use.resolve(());
    // Configured and installed after the first use: not seen until the next phase.
    waiting_after_use.wait().await;
    add_hooks(&registry, &phases, pinger("late"), None).unwrap();
    root.configure(thinking(ModelThinkingLevel::High), context())
        .await
        .unwrap();
    after_use.resolve(());

    harness.wait_for_task(id, context()).await.unwrap();
    let strings = |values: &[&str]| {
        values
            .iter()
            .map(|value| (*value).to_owned())
            .collect::<Vec<_>>()
    };
    assert_eq!(
        *lock(&seen),
        [
            (
                "a".to_owned(),
                strings(&["before"]),
                ModelThinkingLevel::Low,
                None
            ),
            (
                "a".to_owned(),
                strings(&["before"]),
                ModelThinkingLevel::Low,
                Some(true)
            ),
            (
                "b".to_owned(),
                strings(&["before", "late"]),
                ModelThinkingLevel::High,
                None
            ),
        ]
    );
    harness.close(context()).await.unwrap();
}

fn thinking(level: ModelThinkingLevel) -> AgentChange {
    AgentChange {
        thinking_level: FieldChange::Set(level),
        ..AgentChange::default()
    }
}

#[tokio::test]
async fn rejects_an_agent_wait_whose_caller_context_is_cancelled_without_affecting_the_phases_resolution(
) {
    let cancelled: Shared<Option<String>> = shared(None);
    let resolved: Shared<Option<ModelThinkingLevel>> = shared(None);
    let agent = one_step::<(), _, _>("test.agent-cancel", {
        let (cancelled, resolved) = (cancelled.clone(), resolved.clone());
        move |_task, runtime: StepRuntime, cx: Context| {
            let (cancelled, resolved) = (cancelled.clone(), resolved.clone());
            async move {
                let (caller, cancel) = with_cancel(&cx);
                cancel.cancel(Some(reason("caller gone")));
                let error = runtime
                    .agent(&caller)
                    .await
                    .expect_err("the caller is cancelled");
                *lock(&cancelled) = Some(error.to_string());
                *lock(&resolved) = Some(runtime.agent(&cx).await?.thinking_level);
                complete(&runtime, (), &cx).await
            }
        }
    });
    let OpenedRoot { harness, root, .. } = open_root(&[agent.erase()]).await;
    let id = start(&root, &agent).await;
    harness.wait_for_task(id, context()).await.unwrap();
    assert_eq!(lock(&cancelled).as_deref(), Some("caller gone"));
    assert_eq!(*lock(&resolved), Some(ModelThinkingLevel::Off));
    harness.close(context()).await.unwrap();
}

/// Replaces the TS settings getter that throws (JS-only): the conversation's
/// committed `pi.agent` value does not decode, so the phase's agent
/// resolution fails; its first caller already stopped waiting and the second
/// caller observes the shared failure.
#[tokio::test]
async fn observes_a_failed_agent_resolution_whose_only_caller_stopped_waiting() {
    let resolved: Shared<Option<SessionResult<ModelThinkingLevel>>> = shared(None);
    let agent = one_step::<(), _, _>("test.agent-failure", {
        let resolved = resolved.clone();
        move |_task, runtime: StepRuntime, cx: Context| {
            let resolved = resolved.clone();
            async move {
                let (caller, cancel) = with_cancel(&cx);
                cancel.cancel(Some(reason("caller gone")));
                let _ = runtime.agent(&caller).await;
                // Let the abandoned resolution settle before the task ends.
                flush().await;
                let result = runtime.agent(&cx).await.map(|agent| agent.thinking_level);
                *lock(&resolved) = Some(result);
                complete(&runtime, (), &cx).await
            }
        }
    });
    let OpenedRoot { harness, root, .. } = open_root(&[agent.erase()]).await;
    let root_id = root.id();
    root.commit(
        move |tx| async move {
            tx.doc(&AGENT_DOC, root_id).await?.set("thinkingLevel", 5)?;
            Ok(())
        },
        context(),
    )
    .await
    .unwrap();
    let id = start(&root, &agent).await;
    harness.wait_for_task(id, context()).await.unwrap();
    let result = lock(&resolved)
        .take()
        .expect("the phase resolved the agent");
    assert!(
        matches!(result, Err(SessionError::Json(_))),
        "expected a decode failure, got {result:?}"
    );
    harness.close(context()).await.unwrap();
}
