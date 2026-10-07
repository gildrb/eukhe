//! Port of `test/types.test.ts` (record shapes) plus serde round trips of
//! every record kind against JSON written by the TS package (`ts_records.json`,
//! produced by `ts_records.mjs`). The TS compile-time failure checks are
//! `compile_fail` doctests in `types::compile_checks`.

use std::sync::Arc;

use eukhe_chord::delta::{Op, Seg};
use eukhe_chord::json::{from_json, to_json, JsonObject, JsonValue};
use serde::de::DeserializeOwned;
use serde::Serialize;

use super::*;
use crate::harness::define::{define_extension, hook};
use crate::harness::types::{
    CompactionResult, Extension, InputSubmissionDraft, SubmissionDraft, WhenBusy,
    WriteSubmissionDraft,
};
use crate::harness::{Conversation, Harness};
use crate::ids::{id_from_number, seq_from_number};
use crate::session::SessionResult;
use crate::tasks::{define_task, AnyTask, NextTaskState, SettledTask, TaskDefinition, TaskRuntime};
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};

const TS_RECORDS: &str = include_str!("ts_records.json");

fn json(text: &str) -> JsonValue {
    JsonValue::parse(text).unwrap()
}

/// The Rust record decoded from `value` and its re-encoding.
fn round_trip<T: Serialize + DeserializeOwned>(value: &JsonValue) -> (T, JsonValue) {
    let record: T = from_json(value).unwrap_or_else(|error| panic!("{error}: {value}"));
    let encoded = to_json(&record).unwrap();
    (record, encoded)
}

#[test]
fn brands_numeric_ids_by_record_kind_and_carries_task_result_types() {
    // `TaskResult<typeof taskId>` is `number`: the result type is carried by the ID.
    fn result_of<R>(_: TaskId<R>) -> std::marker::PhantomData<R> {
        std::marker::PhantomData
    }

    let conversation_id: ConversationId = id_from_number(1);
    let task_id = TaskId::<u32>::from_number(4);
    assert_eq!(conversation_id.get(), 1);
    assert_eq!(to_json(&task_id).unwrap().to_string(), "4");
    assert_eq!(serde_json::to_string(&conversation_id).unwrap(), "1");
    let _: std::marker::PhantomData<u32> = result_of(task_id);
    // Widening erases the result type; narrowing an erased ID does not compile (see `compile_checks`).
    let widened: TaskId = TaskId::<bool>::from_number(7).erase();
    assert_eq!(widened.get(), 7);
    assert_eq!(seq_from_number(1).get(), 1);
}

#[test]
fn encodes_discriminator_dependent_fields() {
    let entry_id = EntryId::from_number(2);
    let answer_id = EntryId::from_number(3);
    let conversation_id = ConversationId::from_number(1);
    let submission_id = SubmissionId::from_number(5);
    let encode = |value: &dyn erased_serialize::Encode| value.encode();

    let omit = ContextEdit {
        target: entry_id,
        action: ContextEditAction::Omit,
    };
    assert_eq!(encode(&omit), r#"{"target":2,"action":"omit"}"#);
    let replace = ContextEdit {
        target: entry_id,
        action: ContextEditAction::Replace {
            messages: Vec::new(),
        },
    };
    assert_eq!(
        encode(&replace),
        r#"{"target":2,"action":"replace","messages":[]}"#
    );

    let pending: TaskState<JsonValue, JsonValue> = TaskState::Pending {
        checkpoint: json(r#"{"phase":"ready"}"#),
    };
    assert_eq!(
        encode(&pending),
        r#"{"status":"pending","checkpoint":{"phase":"ready"}}"#
    );
    assert_eq!(pending.status(), TaskStatus::Pending);
    let terminal: TaskState<JsonValue, JsonValue> = TaskState::Terminal {
        outcome: TaskOutcome::Completed {
            result: json(r#"{"value":1}"#),
        },
    };
    assert_eq!(
        encode(&terminal),
        r#"{"status":"terminal","outcome":{"status":"completed","result":{"value":1}}}"#
    );
    assert_eq!(terminal.status(), TaskStatus::Terminal);

    let completed_input = SubmissionRecord {
        id: submission_id,
        conversation_id,
        request_id: None,
        state: SubmissionState::Input(InputSubmission::Done {
            entry: entry_id,
            answer: answer_id,
        }),
    };
    assert_eq!(completed_input.state.answer(), Some(answer_id));
    assert_eq!(
        from_json::<SubmissionRecord>(&json(
            r#"{"id":5,"conversationId":1,"type":"input","status":"done","entry":2,"answer":3}"#
        ))
        .unwrap(),
        completed_input
    );
    let completed_write = SubmissionRecord {
        id: submission_id,
        conversation_id,
        request_id: None,
        state: SubmissionState::Write(WriteSubmission::Done { entry: entry_id }),
    };
    assert_eq!(
        completed_write.state.submission_type(),
        SubmissionType::Write
    );
    assert_eq!(
        from_json::<SubmissionRecord>(&json(
            r#"{"id":5,"conversationId":1,"type":"write","status":"done","entry":2}"#
        ))
        .unwrap(),
        completed_write
    );
    let queued_write_create = SubmissionCreate {
        conversation_id,
        request_id: None,
        state: SubmissionState::Write(WriteSubmission::Queued),
    };
    assert_eq!(queued_write_create.state.status(), SubmissionStatus::Queued);
    assert_eq!(
        encode(&queued_write_create),
        r#"{"conversationId":1,"type":"write","status":"queued"}"#
    );
    encodes_document_discriminators(conversation_id, DocumentId::from_number(6));
}

/// The document cases of `encodes discriminator-dependent fields`.
fn encodes_document_discriminators(conversation_id: ConversationId, document_id: DocumentId) {
    let encode = |value: &dyn erased_serialize::Encode| value.encode();
    let base = DocumentContent::Base(DocumentBase {
        version: 1,
        value: Arc::new(
            [("count", JsonValue::from(1))]
                .into_iter()
                .collect::<JsonObject>(),
        ),
    });
    assert_eq!(
        from_json::<DocumentContent>(&json(r#"{"kind":"base","version":1,"value":{"count":1}}"#))
            .unwrap(),
        base
    );
    let delta = DocumentContent::Delta(DocumentDelta {
        version: 1,
        ops: Arc::from(vec![Op::Set(vec![Seg::from("count")], JsonValue::from(2))]),
    });
    assert_eq!(
        from_json::<DocumentContent>(&json(
            r#"{"kind":"delta","version":1,"ops":[["s",["count"],2]]}"#
        ))
        .unwrap(),
        delta
    );
    let conversation_document = DocumentCreate {
        id: document_id,
        kind: "test".to_owned(),
        key: None,
        scope: DocumentRecordScope::Conversation {
            conversation_id,
            semantics: ConversationSemantics::Rewindable(RewindableFork::AsOf),
        },
    };
    assert_eq!(conversation_document.scope.fork(), Some(DocumentFork::AsOf));
    assert_eq!(
        encode(&conversation_document),
        r#"{"id":6,"kind":"test","scope":{"kind":"conversation","conversationId":1},"history":"rewindable","fork":"asOf"}"#
    );
}

/// TS `beforeStep(step: number, api: HookApi, context: Context): { readonly skip: boolean } | undefined`.
type BeforeStep = Arc<
    dyn Fn(f64, &crate::harness::types::HookApi, &eukhe_chord::context::Context) -> Option<Skip>
        + Send
        + Sync,
>;

/// Stepper hook set of `types submissions, task waits, compaction, and tasks
/// erased into extensions` (TS `Hooks`).
#[derive(Clone, Default)]
struct StepperHooks {
    before_step: Option<BeforeStep>,
}

/// TS `{ readonly skip: boolean }`.
#[derive(Debug, Clone, Copy, PartialEq)]
struct Skip {
    skip: bool,
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
struct StepperInput {
    steps: f64,
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
enum StepperCheckpoint {
    Plan { steps: f64 },
    Run { step: f64 },
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
struct Ran {
    ran: f64,
}

type Stepper = crate::tasks::Task<StepperInput, StepperCheckpoint, Ran, StepperHooks>;

// `HooksOf<typeof Stepper>` is `Hooks`.
fn hooks_of<I, S, R, H>(_: &crate::tasks::Task<I, S, R, H>) -> std::marker::PhantomData<H> {
    std::marker::PhantomData
}
fn before_step(step: f64) -> Option<Skip> {
    (step > 1.0).then_some(Skip { skip: true })
}
// Typed waits; compiled, never run (TS `expectTypeOf(typedWaits).toBeFunction()`).
async fn typed_waits(
    harness: Harness,
    conversation: Conversation,
    runtime: TaskRuntime<(), StepperCheckpoint, (), StepperHooks>,
    stepper: Stepper,
) -> SessionResult<()> {
    let call_context = &*BACKGROUND_CONTEXT;
    let definition = stepper.as_definition_ref();
    let id = conversation
        .commit(
            move |tx| async move {
                tx.create_task(
                    definition,
                    to_json(&StepperInput { steps: 2.0 })?,
                    TaskOptions {
                        ownership: TaskOwnership::Conversation,
                        conversation_id: None,
                        background: None,
                    },
                )
                .await
            },
            call_context,
        )
        .await?;
    // `Tx::create_task` takes the erased definition and JSON input, so
    // the ID is erased; the definition's result type re-brands it.
    let id: TaskId<Ran> = TaskId::from_number(id.get());
    // `Harness::wait_for_task` returns the erased receipt; the runtime's is typed.
    let settled: SettledTask = harness.wait_for_task(id, call_context).await?;
    let typed: SettledTask<Ran> = runtime.wait_for_task(id, call_context).await?;
    if let TaskOutcome::Completed { result } = typed.outcome {
        let _: Ran = result;
    }
    let compaction: TaskId<CompactionResult> = conversation.compact(None, call_context).await?;
    let _: SettledTask = harness.wait_for_task(compaction, call_context).await?;
    let _ = settled;
    Ok(())
}

#[test]
#[expect(clippy::too_many_lines, reason = "one TS case, ported whole")]
fn types_submissions_task_waits_compaction_and_tasks_erased_into_extensions() {
    // `satisfies SubmissionDraft`: the discriminant selects the variant and its fields.
    let input: SubmissionDraft = InputSubmissionDraft {
        when_busy: Some(WhenBusy::Steer),
        ..InputSubmissionDraft::new("hi")
    }
    .into();
    let write: SubmissionDraft = WriteSubmissionDraft {
        request_id: None,
        entry: EntryDraft::new("note"),
    }
    .into();
    assert_eq!(
        input,
        SubmissionDraft::Input(InputSubmissionDraft {
            request_id: None,
            content: "hi".into(),
            when_busy: Some(WhenBusy::Steer),
        })
    );
    assert_eq!(
        write,
        SubmissionDraft::Write(WriteSubmissionDraft {
            request_id: None,
            entry: EntryDraft::new("note"),
        })
    );

    // A task with narrowed input, several phases, and custom hooks. Rust has
    // no per-phase narrowing: a handler matches its checkpoint variant.
    let stepper: Stepper = define_task(
        TaskDefinition::new(
            "test.stepper",
            1,
            |input: &StepperInput| Ok(StepperCheckpoint::Plan { steps: input.steps }),
            |_task, _runtime, _cx| async { Ok(()) },
        )
        .phase(
            "plan",
            |task,
             runtime: TaskRuntime<StepperInput, StepperCheckpoint, Ran, StepperHooks>,
             cx: Context| async move {
                if let StepperCheckpoint::Plan { steps } = task.checkpoint {
                    let _: f64 = steps;
                }
                let _: f64 = task.input.steps;
                runtime
                    .commit(
                        |_tx, _current| async {
                            Ok(Some(NextTaskState::Running {
                                checkpoint: StepperCheckpoint::Run { step: 0.0 },
                            }))
                        },
                        &cx,
                    )
                    .await
            },
        )
        .phase(
            "run",
            |task,
             runtime: TaskRuntime<StepperInput, StepperCheckpoint, Ran, StepperHooks>,
             cx: Context| async move {
                if let StepperCheckpoint::Run { step } = task.checkpoint {
                    let _: f64 = step;
                }
                runtime
                    .hooks()
                    .each(
                        |hooks: &StepperHooks| hooks.before_step.clone(),
                        |handler| {
                            // `handler` is `Hooks["beforeStep"]`.
                            let _: BeforeStep = handler;
                            async { Ok(()) }
                        },
                    )
                    .await?;
                runtime
                    .commit(
                        |_tx, _current| async {
                            Ok(Some(NextTaskState::Terminal {
                                outcome: TaskOutcome::Completed {
                                    result: Ran { ran: 1.0 },
                                },
                            }))
                        },
                        &cx,
                    )
                    .await
            },
        ),
    );
    let _: std::marker::PhantomData<StepperHooks> = hooks_of(&stepper);
    let registration = hook(
        &stepper,
        StepperHooks {
            before_step: Some(Arc::new(|step, _api, _context| before_step(step))),
        },
    );
    assert_eq!(before_step(2.0).map(|decision| decision.skip), Some(true));
    assert_eq!(before_step(1.0), None);
    // Erased into an extension, whatever its input, phases, and hooks.
    let erased: AnyTask = stepper.erase();
    let extension: Arc<Extension> = define_extension(Extension {
        name: "stepper".to_owned(),
        tasks: vec![stepper.erase()],
        hooks: vec![registration],
        ..Extension::default()
    });
    assert!(AnyTask::ptr_eq(&erased, &extension.tasks[0]));
    assert_eq!(extension.hooks[0].task, "test.stepper");
    // The registration holds the stepper's typed hook set.
    assert!(extension.hooks[0]
        .handlers
        .downcast_ref::<StepperHooks>()
        .is_some_and(|hooks| hooks.before_step.is_some()));

    // TS `expectTypeOf(typedWaits).toBeFunction()`.
    let _ = typed_waits;
}

/// Shapes the TS types reject, which Rust types cannot express either, rejected
/// when they arrive as JSON.
#[test]
fn rejects_discriminator_violations_in_json() {
    let reject = |result: Result<(), String>, message: &str| {
        assert!(result.unwrap_err().contains(message), "{message}");
    };
    let decode = |text: &str| -> Result<(), String> {
        from_json::<SubmissionRecord>(&json(text))
            .map(drop)
            .map_err(|e| e.to_string())
    };
    reject(
        decode(r#"{"id":5,"conversationId":1,"type":"input","status":"queued","entry":2}"#),
        "a queued input submission cannot carry `entry`",
    );
    reject(
        decode(r#"{"id":5,"conversationId":1,"type":"input","status":"done","entry":2}"#),
        "a done input submission requires `answer`",
    );
    reject(
        decode(
            r#"{"id":5,"conversationId":1,"type":"write","status":"done","entry":2,"answer":3}"#,
        ),
        "a done write submission cannot carry `answer`",
    );
    reject(
        from_json::<SubmissionCreate>(&json(
            r#"{"id":5,"conversationId":1,"type":"write","status":"queued"}"#,
        ))
        .map(drop)
        .map_err(|e| e.to_string()),
        "a submission create value cannot carry `id`",
    );
    let document = |text: &str| -> Result<(), String> {
        from_json::<DocumentRecord>(&json(text))
            .map(drop)
            .map_err(|e| e.to_string())
    };
    reject(
        document(
            r#"{"id":6,"kind":"test","createdAt":1,"scope":{"kind":"session"},"history":"latest","fork":"current"}"#,
        ),
        "a session document cannot carry `history`",
    );
    reject(
        from_json::<DocumentCreate>(&json(
            r#"{"id":6,"kind":"test","scope":{"kind":"conversation","conversationId":1}}"#,
        ))
        .map(drop)
        .map_err(|e| e.to_string()),
        "a conversation document requires `history`",
    );
    reject(
        from_json::<DocumentCreate>(&json(
            r#"{"id":6,"kind":"test","scope":{"kind":"task","taskId":4},"history":"latest","fork":"initial"}"#,
        ))
        .map(drop)
        .map_err(|e| e.to_string()),
        "a task document cannot carry `history`",
    );
    reject(
        from_json::<DocumentCreate>(&json(
            r#"{"id":6,"kind":"test","scope":{"kind":"session"},"createdAt":1}"#,
        ))
        .map(drop)
        .map_err(|e| e.to_string()),
        "a document create value cannot carry `createdAt`",
    );
    let content = |text: &str| -> Result<(), String> {
        from_json::<DocumentContent>(&json(text))
            .map(drop)
            .map_err(|e| e.to_string())
    };
    reject(
        content(r#"{"kind":"base","version":1,"value":{},"ops":[]}"#),
        "a document base cannot carry `ops`",
    );
    reject(
        content(r#"{"kind":"delta","version":1,"ops":[],"value":{}}"#),
        "a document delta cannot carry `value`",
    );
    reject(
        from_json::<StorageWrite>(&json(
            r#"{"type":"document.create","record":{"id":6,"kind":"test","scope":{"kind":"session"}},"content":{"kind":"delta","version":1,"ops":[]}}"#,
        ))
        .map(drop)
        .map_err(|e| e.to_string()),
        "document creation always starts from a complete base",
    );
    reject(
        from_json::<ContextEdit>(&json(r#"{"target":2,"action":"replace"}"#))
            .map(drop)
            .map_err(|e| e.to_string()),
        "messages",
    );
}

/// Every record the TS Session and storage wrote decodes, and re-encodes to the
/// same JSON. Byte order matches too, except where TS key order depends on a
/// record's history rather than its shape.
#[test]
fn round_trips_ts_written_records() {
    let fixture = json(TS_RECORDS);
    let mut reordered = Vec::new();
    let mut check = |label: String, original: &JsonValue, encoded: &JsonValue| {
        assert_eq!(encoded, original, "{label}");
        if encoded.to_string() != original.to_string() {
            reordered.push(label);
        }
    };

    for (batch_index, batch) in fixture["batches"].as_array().unwrap().iter().enumerate() {
        for (index, write) in batch.as_array().unwrap().iter().enumerate() {
            let (_, encoded) = round_trip::<StorageWrite>(write);
            check(
                format!("batch {batch_index} write {index} {}", write["type"]),
                write,
                &encoded,
            );
        }
    }
    let records = &fixture["records"];
    for value in records["conversations"].as_array().unwrap() {
        let (_, encoded) = round_trip::<ConversationRecord>(value);
        check(format!("conversation {}", value["id"]), value, &encoded);
    }
    for value in records["entries"].as_array().unwrap() {
        let (_, encoded) = round_trip::<EntryRecord>(value);
        check(format!("entry {}", value["kind"]), value, &encoded);
    }
    let (lookup, encoded) = round_trip::<StoredEntry>(&records["entryLookup"]);
    check("entry lookup".to_owned(), &records["entryLookup"], &encoded);
    assert_eq!(lookup.commit_seq, Seq::from_number(1));
    for value in records["tasks"].as_array().unwrap() {
        let (_, encoded) = round_trip::<AnyTaskRecord>(value);
        check(
            format!("task {}", value["state"]["status"]),
            value,
            &encoded,
        );
    }
    for value in records["submissions"].as_array().unwrap() {
        let (_, encoded) = round_trip::<SubmissionRecord>(value);
        check(format!("submission {}", value["id"]), value, &encoded);
    }
    for value in records["documents"].as_array().unwrap() {
        let (_, encoded) = round_trip::<DocumentRecord>(value);
        check(format!("document {}", value["id"]), value, &encoded);
    }
    let (stored, encoded) = round_trip::<StoredDocument>(&records["stored"]);
    check("stored document".to_owned(), &records["stored"], &encoded);
    assert_eq!(stored.deltas_since_base, 1);

    // Untyped `appendEntry` keeps the caller's draft key order; placement and
    // settlement append `entry`/`reason`/`detail` after `id`.
    assert_eq!(
        reordered,
        [
            r#"batch 0 write 5 "entry""#,
            r#"batch 0 write 8 "entry""#,
            r#"batch 1 write 0 "submission""#,
            r#"batch 1 write 1 "submission""#,
            r#"batch 1 write 2 "submission""#,
            r#"batch 2 write 0 "submission""#,
            r#"entry "pi.compaction""#,
            r#"entry "t.edits""#,
            "submission 19",
            "submission 20",
            "submission 21",
        ]
    );
}

#[test]
fn decodes_typed_records_from_ts_json() {
    let fixture = json(TS_RECORDS);
    let records = &fixture["records"];
    let entries: Vec<EntryRecord> = from_json(&records["entries"]).unwrap();
    let reset = entries
        .iter()
        .find(|entry| entry.kind == "pi.reset")
        .unwrap();
    assert_eq!(reset.head, Some(reset.id));
    let edits = entries
        .iter()
        .find(|entry| entry.kind == "t.edits")
        .unwrap();
    assert_eq!(edits.data, Some(JsonValue::Null));
    assert_eq!(
        edits.edits.as_ref().unwrap()[0].action,
        ContextEditAction::Omit
    );

    let child: AnyTaskRecord = from_json(&records["tasks"][0]).unwrap();
    assert_eq!(child.owner, Some(TaskId::from_number(16)));
    assert_eq!(child.input, JsonValue::Null);
    let running: AnyTaskRecord = from_json(&records["tasks"][1]).unwrap();
    assert_eq!(running.memos.as_deref().map(JsonObject::len), Some(2));
    let aborted: AnyTaskRecord = from_json(&records["tasks"][7]).unwrap();
    assert_eq!(
        aborted.state,
        TaskState::Terminal {
            outcome: TaskOutcome::Aborted {
                reason: Some("user".to_owned()),
                result: Some(JsonValue::Null)
            }
        }
    );

    let submissions: Vec<SubmissionRecord> = from_json(&records["submissions"]).unwrap();
    assert_eq!(
        submissions[1].state,
        SubmissionState::Input(InputSubmission::Unanswered {
            entry: Some(EntryId::from_number(3)),
            reason: "failed".to_owned(),
            detail: Some(json(r#"{"codes":["x"]}"#)),
        })
    );
    let documents: Vec<DocumentRecord> = from_json(&records["documents"]).unwrap();
    let session = documents.last().unwrap();
    assert_eq!(session.scope, DocumentRecordScope::Session);
    assert_eq!(
        (session.created_at, session.retired_at),
        (Seq::from_number(1), Some(Seq::from_number(3)))
    );
    let copy: StorageWrite = from_json(&fixture["batches"][3][2]).unwrap();
    assert_eq!(
        copy,
        StorageWrite::DocumentCopy {
            record: DocumentCreate {
                id: DocumentId::from_number(26),
                kind: "t.rewindable".to_owned(),
                key: None,
                scope: DocumentRecordScope::Conversation {
                    conversation_id: ConversationId::from_number(25),
                    semantics: ConversationSemantics::Rewindable(RewindableFork::AsOf),
                },
            },
            source: DocumentCopySource {
                id: DocumentId::from_number(13),
                at: DocumentPoint::At(Seq::from_number(1))
            },
        }
    );
}

#[test]
fn serializes_queries_and_points_like_ts() {
    let query = TaskQuery {
        kind: Some("pi.generation".to_owned()),
        status: Some(TaskStatus::Completing),
        ..TaskQuery::default()
    };
    assert_eq!(
        to_json(&query).unwrap().to_string(),
        r#"{"kind":"pi.generation","status":"completing"}"#
    );
    let documents = DocumentQuery {
        scope: DocumentScope::Task {
            task_id: TaskId::from_number(4),
        },
        at: DocumentPoint::Current,
        kind: None,
    };
    assert_eq!(
        to_json(&documents).unwrap().to_string(),
        r#"{"scope":{"kind":"task","taskId":4},"at":"current"}"#
    );
    assert_eq!(
        from_json::<DocumentPoint>(&JsonValue::from(7)).unwrap(),
        DocumentPoint::At(Seq::from_number(7))
    );
    let page: Page<ConversationRecord> =
        from_json(&json(r#"{"items":[{"id":1}],"next":{"after":1}}"#)).unwrap();
    assert_eq!(
        page.next.as_ref().unwrap().get("after"),
        Some(&JsonValue::from(1))
    );
    assert_eq!(
        to_json(&page).unwrap().to_string(),
        r#"{"items":[{"id":1}],"next":{"after":1}}"#
    );
    assert_eq!(
        to_json(&SubmissionSettlement::Unanswered {
            reason: "stale".to_owned(),
            detail: None
        })
        .unwrap()
        .to_string(),
        r#"{"status":"unanswered","reason":"stale"}"#
    );
    assert_eq!(
        to_json(&ConversationOwnership::Task {
            task_id: TaskId::from_number(3)
        })
        .unwrap()
        .to_string(),
        r#"{"kind":"task","taskId":3}"#
    );
    assert_eq!(
        to_json(&TaskOptions {
            ownership: TaskOwnership::Conversation,
            conversation_id: None,
            background: Some(true)
        })
        .unwrap()
        .to_string(),
        r#"{"ownership":{"kind":"conversation"},"background":true}"#
    );
    assert_eq!(
        to_json(&EntryDraft {
            head: Some(EntryHead::SelfEntry),
            ..EntryDraft::new("pi.reset")
        })
        .unwrap()
        .to_string(),
        r#"{"kind":"pi.reset","head":"self"}"#
    );
}

/// Object-safe encoding for the heterogeneous literals above.
mod erased_serialize {
    use serde::Serialize;

    pub(super) trait Encode {
        fn encode(&self) -> String;
    }

    impl<T: Serialize> Encode for T {
        fn encode(&self) -> String {
            eukhe_chord::json::to_json(self).unwrap().to_string()
        }
    }
}
