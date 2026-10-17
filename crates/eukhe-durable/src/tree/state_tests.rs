use std::sync::Arc;

use serde_json::{json, Value};

use super::{CursorAhead, StateError, StateKey, StateKind, StateNode, StateTree};
use crate::storage::jsonl::HistoryCommit;
use crate::tree::{Applied, NodeId, RewindEffect, TreeOp, TreeRecord};
use crate::types::{
    AnyTaskRecord, CommitChange, CommitPublication, ConversationId, ConversationOwner,
    ConversationRecord, ConversationSemantics, DocumentBase, DocumentCommitChange, DocumentContent,
    DocumentCreate, DocumentDelta, DocumentId, DocumentRecord, DocumentRecordScope, EntryId,
    EntryRecord, JsonObject, LatestFork, Seq, StorageWrite, SubmissionRecord, TaskId,
};

const CONVERSATION: ConversationId = ConversationId::from_number(1);

fn seq(n: u64) -> Seq {
    Seq::from_number(n)
}

fn conversation() -> ConversationRecord {
    ConversationRecord {
        id: CONVERSATION,
        parent: None,
        owner: None,
    }
}

fn entry(id: u64, conversation_id: ConversationId) -> EntryRecord {
    EntryRecord {
        model: None,
        data: None,
        edits: None,
        kind: "user".to_owned(),
        id: EntryId::from_number(id),
        conversation_id,
        head: None,
        by_task_id: None,
    }
}

fn task(status: &Value) -> AnyTaskRecord {
    serde_json::from_value(json!({
        "id": 4, "conversationId": 1, "kind": "pi.generation", "version": 1, "input": {},
        "background": false, "abortRequested": false, "state": status,
    }))
    .unwrap()
}

fn pending() -> AnyTaskRecord {
    task(&json!({"status": "pending", "checkpoint": null}))
}

fn terminal() -> AnyTaskRecord {
    task(&json!({"status": "terminal", "outcome": {"status": "completed", "result": null}}))
}

fn submission() -> SubmissionRecord {
    serde_json::from_value(json!({
        "conversationId": 1, "type": "input", "status": "placed", "entry": 3, "id": 5,
    }))
    .unwrap()
}

fn session_document() -> DocumentCreate {
    DocumentCreate {
        id: DocumentId::from_number(2),
        kind: "eukhe.daemon.session".to_owned(),
        key: None,
        scope: DocumentRecordScope::Session,
    }
}

fn conversation_document() -> DocumentCreate {
    DocumentCreate {
        id: DocumentId::from_number(6),
        kind: "pi.live".to_owned(),
        key: None,
        scope: DocumentRecordScope::Conversation {
            conversation_id: CONVERSATION,
            semantics: ConversationSemantics::Latest(LatestFork::Initial),
        },
    }
}

fn document_change(
    create: DocumentCreate,
    created_at: u64,
    retired_at: Option<u64>,
) -> CommitChange {
    let retired = retired_at.is_some();
    CommitChange::Document(DocumentCommitChange::Document {
        conversation_id: match create.scope {
            DocumentRecordScope::Conversation {
                conversation_id, ..
            } => Some(conversation_id),
            DocumentRecordScope::Session | DocumentRecordScope::Task { .. } => None,
        },
        record: DocumentRecord {
            retired_at: retired_at.map(seq),
            ..DocumentRecord::from_create(create, seq(created_at))
        },
        version: (!retired).then_some(1),
        value: (!retired).then(|| Arc::new(JsonObject::new())),
        ops: Arc::from(Vec::new()),
    })
}

/// Three commits: a conversation with an entry and a session document;
/// a task, a submission and a conversation document; the task ends, the
/// conversation document changes, the session document retires.
fn publications() -> Vec<CommitPublication> {
    vec![
        CommitPublication {
            seq: seq(1),
            changes: vec![
                CommitChange::Entry(entry(3, CONVERSATION)),
                CommitChange::Conversation(conversation()),
                document_change(session_document(), 1, None),
            ],
        },
        CommitPublication {
            seq: seq(2),
            changes: vec![
                CommitChange::Task(pending()),
                CommitChange::Submission(submission()),
                document_change(conversation_document(), 2, None),
            ],
        },
        CommitPublication {
            seq: seq(3),
            changes: vec![
                CommitChange::Task(terminal()),
                document_change(conversation_document(), 2, None),
                document_change(session_document(), 1, Some(3)),
            ],
        },
    ]
}

/// The same commits as storage writes.
fn writes() -> Vec<(Seq, Vec<StorageWrite>)> {
    let base = || DocumentBase {
        version: 1,
        value: Arc::new(JsonObject::new()),
    };
    vec![
        (
            seq(1),
            vec![
                StorageWrite::Entry {
                    value: entry(3, CONVERSATION),
                },
                StorageWrite::Conversation {
                    value: conversation(),
                },
                StorageWrite::DocumentCreate {
                    record: session_document(),
                    content: base(),
                },
            ],
        ),
        (
            seq(2),
            vec![
                StorageWrite::Task { value: pending() },
                StorageWrite::Submission {
                    value: submission(),
                },
                StorageWrite::DocumentCreate {
                    record: conversation_document(),
                    content: base(),
                },
            ],
        ),
        (
            seq(3),
            vec![
                StorageWrite::Task { value: terminal() },
                StorageWrite::DocumentChange {
                    id: DocumentId::from_number(6),
                    content: DocumentContent::Delta(DocumentDelta {
                        version: 1,
                        ops: Arc::from(Vec::new()),
                    }),
                },
                StorageWrite::DocumentRetire {
                    id: DocumentId::from_number(2),
                },
            ],
        ),
    ]
}

fn node(kind: StateKind, value: Value) -> StateNode {
    StateNode {
        kind,
        value: Arc::new(value),
    }
}

fn conversation_node() -> StateNode {
    node(StateKind::Conversation, json!({"id": 1}))
}

fn entry_node() -> StateNode {
    node(
        StateKind::Entry,
        json!({"kind": "user", "conversationId": 1, "head": null, "byTaskId": null}),
    )
}

fn task_node(record: &AnyTaskRecord) -> StateNode {
    node(StateKind::Task, serde_json::to_value(record).unwrap())
}

fn submission_node() -> StateNode {
    node(
        StateKind::Submission,
        serde_json::to_value(submission()).unwrap(),
    )
}

fn document_node(kind: &str, scope: &str, created_at: u64, changed_at: u64) -> StateNode {
    node(
        StateKind::Document,
        json!({
            "kind": kind, "key": null, "scope": scope,
            "createdAt": created_at, "changedAt": changed_at,
        }),
    )
}

fn put(id: u64, parent: u64, value: StateNode) -> TreeRecord<StateNode> {
    TreeRecord::Do(TreeOp::Put {
        id: NodeId(id),
        parent: NodeId(parent),
        value,
    })
}

fn expected_records() -> Vec<TreeRecord<StateNode>> {
    vec![
        put(1, 0, conversation_node()),
        put(2, 0, document_node("eukhe.daemon.session", "session", 1, 1)),
        put(3, 1, entry_node()),
        put(4, 1, task_node(&pending())),
        put(5, 1, submission_node()),
        put(6, 1, document_node("pi.live", "conversation", 2, 2)),
        put(4, 1, task_node(&terminal())),
        put(6, 1, document_node("pi.live", "conversation", 2, 3)),
        TreeRecord::Do(TreeOp::Del { id: NodeId(2) }),
    ]
}

/// `(id, parent, key, node)` of each node, in id order.
fn rows(
    state: &StateTree,
    tree: &crate::tree::SessionTree<StateNode>,
) -> Vec<(u64, u64, StateKey, StateNode)> {
    tree.iter()
        .map(|(id, node)| {
            (
                id.0,
                node.parent.0,
                state.key(id).unwrap().clone(),
                node.value.clone(),
            )
        })
        .collect()
}

fn built() -> StateTree {
    let mut state = StateTree::new();
    for publication in publications() {
        state.record(&publication);
    }
    state
}

#[test]
fn commits_build_the_tree_with_parents_first() {
    let mut state = StateTree::new();
    let results: Vec<_> = publications()
        .iter()
        .map(|publication| state.record(publication))
        .collect();
    assert_eq!(
        (
            results,
            state.cursor(),
            state.seq(),
            state.records_since(0).unwrap().to_vec(),
            rows(&state, state.tree()),
        ),
        (
            vec![vec![Ok(Applied::Accepted); 3]; 3],
            9,
            Some(seq(3)),
            expected_records(),
            vec![
                (
                    1,
                    0,
                    StateKey::Conversation("1".to_owned()),
                    conversation_node()
                ),
                (3, 1, StateKey::Entry("3".to_owned()), entry_node()),
                (4, 1, StateKey::Task("4".to_owned()), task_node(&terminal())),
                (
                    5,
                    1,
                    StateKey::Submission("5".to_owned()),
                    submission_node()
                ),
                (
                    6,
                    1,
                    StateKey::Document("6".to_owned()),
                    document_node("pi.live", "conversation", 2, 3),
                ),
            ],
        )
    );
}

#[test]
fn storage_writes_build_the_same_journal_as_publications() {
    let history: Vec<HistoryCommit> = writes()
        .into_iter()
        .map(|(seq, writes)| HistoryCommit { seq, writes })
        .collect();
    let (replayed, results) = StateTree::from_history(&history);
    let live = built();
    assert_eq!(
        (
            results,
            replayed.records_since(0).unwrap(),
            rows(&replayed, replayed.tree()),
        ),
        (
            vec![Ok(Applied::Accepted); 9],
            live.records_since(0).unwrap(),
            rows(&live, live.tree())
        ),
    );
}

/// A stored history keeps no early state of a terminal task: its document
/// and the conversation it owns come first, and still find their parent.
#[test]
fn a_history_gives_every_node_its_conversation() {
    let task_document = DocumentCreate {
        id: DocumentId::from_number(7),
        kind: "pi.task".to_owned(),
        key: Some("k".to_owned()),
        scope: DocumentRecordScope::Task {
            task_id: TaskId::from_number(4),
        },
    };
    let owned = ConversationRecord {
        id: ConversationId::from_number(8),
        parent: None,
        owner: Some(ConversationOwner {
            conversation_id: CONVERSATION,
            task_id: TaskId::from_number(4),
        }),
    };
    let history = vec![
        HistoryCommit {
            seq: seq(1),
            writes: vec![StorageWrite::Conversation {
                value: conversation(),
            }],
        },
        HistoryCommit {
            seq: seq(2),
            writes: vec![
                StorageWrite::DocumentCreate {
                    record: task_document,
                    content: DocumentBase {
                        version: 1,
                        value: Arc::new(JsonObject::new()),
                    },
                },
                StorageWrite::Conversation { value: owned },
            ],
        },
        HistoryCommit {
            seq: seq(3),
            writes: vec![StorageWrite::Task { value: terminal() }],
        },
    ];
    let (state, results) = StateTree::from_history(&history);
    assert_eq!(
        (results, rows(&state, state.tree())),
        (
            vec![Ok(Applied::Accepted); 4],
            vec![
                (
                    1,
                    0,
                    StateKey::Conversation("1".to_owned()),
                    conversation_node()
                ),
                (
                    2,
                    1,
                    StateKey::Document("7".to_owned()),
                    node(
                        StateKind::Document,
                        json!({
                            "kind": "pi.task", "key": "k", "scope": "task",
                            "createdAt": 2, "changedAt": 2,
                        }),
                    ),
                ),
                (
                    3,
                    1,
                    StateKey::Conversation("8".to_owned()),
                    node(
                        StateKind::Conversation,
                        json!({"id": 8, "owner": {"conversationId": 1, "taskId": 4}}),
                    ),
                ),
                (4, 1, StateKey::Task("4".to_owned()), task_node(&terminal())),
            ],
        )
    );
}

#[test]
fn an_old_commit_records_nothing() {
    let mut state = built();
    assert_eq!(
        (state.record(&publications()[1]), state.cursor()),
        (Vec::new(), 9)
    );
}

#[test]
fn records_since_a_cursor_are_the_tail() {
    let state = built();
    assert_eq!(
        (state.records_since(6), state.records_since(10)),
        (
            Ok(&expected_records()[6..]),
            Err(CursorAhead {
                cursor: 10,
                current: 9
            })
        )
    );
}

#[test]
fn a_snapshot_is_the_tree_at_its_cursor() {
    let state = built();
    let snapshot = state.snapshot_at(3).unwrap();
    assert_eq!(
        rows(&state, &snapshot),
        vec![
            (
                1,
                0,
                StateKey::Conversation("1".to_owned()),
                conversation_node()
            ),
            (
                2,
                0,
                StateKey::Document("2".to_owned()),
                document_node("eukhe.daemon.session", "session", 1, 1)
            ),
            (3, 1, StateKey::Entry("3".to_owned()), entry_node()),
        ]
    );
}

#[test]
fn a_rewind_plan_stops_starts_and_restores() {
    let state = built();
    assert_eq!(
        (
            state.rewind_plan(3),
            state.rewind_plan(6),
            state.rewind_plan(9),
            state.rewind_plan(10),
        ),
        (
            Ok(vec![
                RewindEffect::Stop(NodeId(4)),
                RewindEffect::Stop(NodeId(5)),
                RewindEffect::Stop(NodeId(6)),
                RewindEffect::Start(NodeId(2)),
            ]),
            Ok(vec![
                RewindEffect::Start(NodeId(2)),
                RewindEffect::Restore(NodeId(4)),
                RewindEffect::Restore(NodeId(6)),
            ]),
            Ok(Vec::new()),
            Err(CursorAhead {
                cursor: 10,
                current: 9
            }),
        )
    );
}

#[test]
fn an_unknown_parent_or_node_is_an_error() {
    let mut state = built();
    let results = state.record(&CommitPublication {
        seq: seq(4),
        changes: vec![
            CommitChange::Entry(entry(7, ConversationId::from_number(99))),
            document_change(session_document(), 1, Some(4)),
        ],
    });
    assert_eq!(
        (results, state.cursor()),
        (
            vec![
                Err(StateError::UnknownParent {
                    seq: seq(4),
                    key: StateKey::Entry("7".to_owned()),
                    parent: StateKey::Conversation("99".to_owned()),
                }),
                Err(StateError::UnknownNode {
                    seq: seq(4),
                    key: StateKey::Document("2".to_owned()),
                }),
            ],
            9
        )
    );
}
