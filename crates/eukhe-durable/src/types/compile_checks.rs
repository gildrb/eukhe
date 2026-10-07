//! Compile-time failures of `test/types.test.ts` and
//! `test/session-definitions.test.ts` (`@ts-expect-error` cases), as
//! `compile_fail` doctests. Each block must fail to compile.
//!
//! An erased task result cannot be narrowed without a typed source:
//! ```compile_fail
//! use eukhe_durable::types::TaskId;
//! let widened: TaskId = TaskId::<bool>::from_number(7).erase();
//! let narrowed: TaskId<String> = widened;
//! ```
//! Conversation IDs are not task IDs:
//! ```compile_fail
//! use eukhe_durable::types::{ConversationId, TaskId};
//! let wrong: TaskId = ConversationId::from_number(1);
//! ```
//! Task IDs are not conversation IDs:
//! ```compile_fail
//! use eukhe_durable::types::{ConversationId, TaskId};
//! let wrong: ConversationId = TaskId::<u32>::from_number(4);
//! ```
//! Entry IDs are not document IDs:
//! ```compile_fail
//! use eukhe_durable::types::{DocumentId, EntryId};
//! let wrong: DocumentId = EntryId::from_number(2);
//! ```
//! Entity IDs are not commit sequences:
//! ```compile_fail
//! use eukhe_durable::types::{EntryId, Seq};
//! let wrong: Seq = EntryId::from_number(2);
//! ```
//! Replacement edits require replacement messages:
//! ```compile_fail
//! use eukhe_durable::types::ContextEditAction;
//! let wrong = ContextEditAction::Replace {};
//! ```
//! Omission edits cannot carry replacement messages:
//! ```compile_fail
//! use eukhe_durable::types::ContextEditAction;
//! let wrong = ContextEditAction::Omit { messages: Vec::new() };
//! ```
//! Live task state cannot carry a terminal outcome:
//! ```compile_fail
//! use eukhe_durable::types::{TaskOutcome, TaskState};
//! let wrong: TaskState<u32, u32> = TaskState::Pending { checkpoint: 1, outcome: TaskOutcome::Completed { result: 1 } };
//! ```
//! Terminal task state cannot retain a live checkpoint:
//! ```compile_fail
//! use eukhe_durable::types::{TaskOutcome, TaskState};
//! let wrong: TaskState<u32, u32> = TaskState::Terminal { checkpoint: 1, outcome: TaskOutcome::Completed { result: 1 } };
//! ```
//! Session documents do not declare conversation history behavior:
//! ```compile_fail
//! use eukhe_durable::types::{ConversationSemantics, DocumentRecordScope, LatestFork};
//! let wrong = DocumentRecordScope::Session { semantics: ConversationSemantics::Latest(LatestFork::Current) };
//! ```
//! Conversation document creation requires history and fork policies:
//! ```compile_fail
//! use eukhe_durable::types::{ConversationId, DocumentRecordScope};
//! let wrong = DocumentRecordScope::Conversation { conversation_id: ConversationId::from_number(1) };
//! ```
//! Task document creation cannot declare conversation policies:
//! ```compile_fail
//! use eukhe_durable::types::{ConversationSemantics, DocumentRecordScope, LatestFork, TaskId};
//! let wrong = DocumentRecordScope::Task {
//!     task_id: TaskId::from_number(4),
//!     semantics: ConversationSemantics::Latest(LatestFork::Initial),
//! };
//! ```
//! Storage, not the create command, supplies `createdAt`:
//! ```compile_fail
//! use eukhe_durable::types::{DocumentCreate, DocumentId, DocumentRecordScope, Seq};
//! let wrong = DocumentCreate {
//!     id: DocumentId::from_number(6),
//!     kind: "test".to_owned(),
//!     key: None,
//!     scope: DocumentRecordScope::Session,
//!     created_at: Seq::from_number(1),
//! };
//! ```
//! Document bases cannot carry operation batches:
//! ```compile_fail
//! use std::sync::Arc;
//! use eukhe_durable::types::{DocumentBase, JsonObject};
//! let wrong = DocumentBase { version: 1, value: Arc::new(JsonObject::new()), ops: Vec::new() };
//! ```
//! Document deltas cannot carry materialized values:
//! ```compile_fail
//! use std::sync::Arc;
//! use eukhe_durable::types::{DocumentDelta, JsonObject};
//! let wrong = DocumentDelta { version: 1, ops: Arc::from(Vec::new()), value: Arc::new(JsonObject::new()) };
//! ```
//! Document creation always starts from a complete base:
//! ```compile_fail
//! use std::sync::Arc;
//! use eukhe_durable::types::{DocumentContent, DocumentCreate, DocumentDelta, DocumentId, DocumentRecordScope, StorageWrite};
//! let wrong = StorageWrite::DocumentCreate {
//!     record: DocumentCreate { id: DocumentId::from_number(6), kind: "test".to_owned(), key: None, scope: DocumentRecordScope::Session },
//!     content: DocumentContent::Delta(DocumentDelta { version: 1, ops: Arc::from(Vec::new()) }),
//! };
//! ```
//! Completed outcomes cannot carry errors:
//! ```compile_fail
//! use eukhe_durable::types::{TaskOutcome, TaskOutcomeError};
//! let wrong: TaskOutcome<u32> = TaskOutcome::Completed {
//!     result: 1,
//!     error: TaskOutcomeError { message: "impossible".to_owned(), detail: None },
//! };
//! ```
//! Queued submissions cannot reference transcript entries:
//! ```compile_fail
//! use eukhe_durable::types::{EntryId, InputSubmission};
//! let wrong = InputSubmission::Queued { entry: EntryId::from_number(2) };
//! ```
//! Successful input submissions require an answer entry:
//! ```compile_fail
//! use eukhe_durable::types::{EntryId, InputSubmission};
//! let wrong = InputSubmission::Done { entry: EntryId::from_number(2) };
//! ```
//! Passive write submissions never carry an answer:
//! ```compile_fail
//! use eukhe_durable::types::{EntryId, WriteSubmission};
//! let wrong = WriteSubmission::Done { entry: EntryId::from_number(2), answer: EntryId::from_number(3) };
//! ```
//! The Session, not the submission create value, assigns its ID:
//! ```compile_fail
//! use eukhe_durable::types::{ConversationId, SubmissionCreate, SubmissionId, SubmissionState, WriteSubmission};
//! let wrong = SubmissionCreate {
//!     id: SubmissionId::from_number(5),
//!     conversation_id: ConversationId::from_number(1),
//!     request_id: None,
//!     state: SubmissionState::Write(WriteSubmission::Queued),
//! };
//! ```
//! Session documents take no owner:
//! ```compile_fail
//! use eukhe_durable::documents::{resolve_token_address, DocDefinition, SessionDoc};
//! use eukhe_durable::types::ConversationId;
//! # #[derive(Default, serde::Serialize, serde::Deserialize)] struct State { value: u32 }
//! let token = SessionDoc::<State>::define(DocDefinition { kind: "t.session", version: 1, initial: State::default, migrate: None, checkpoint_when: None }).unwrap();
//! resolve_token_address(&token, ConversationId::from_number(1));
//! ```
//! Conversation documents require a conversation ID:
//! ```compile_fail
//! use eukhe_durable::documents::{resolve_token_address, ConversationDoc, DocDefinition};
//! use eukhe_durable::types::LatestFork;
//! # #[derive(Default, serde::Serialize, serde::Deserialize)] struct State { value: u32 }
//! let token = ConversationDoc::<State>::define(DocDefinition { kind: "t.latest", version: 1, initial: State::default, migrate: None, checkpoint_when: None }, LatestFork::Current).unwrap();
//! resolve_token_address(&token, ());
//! ```
//! Family access requires a creation seed (singleton tokens have none):
//! ```compile_fail
//! use eukhe_durable::documents::{DocFamilyDefinition, SessionDocFamily, SingletonDocToken};
//! # #[derive(Default, serde::Serialize, serde::Deserialize)] struct State { value: u32 }
//! fn singleton<D: SingletonDocToken>(_: &D) {}
//! let token = SessionDocFamily::<State, u32>::define(DocFamilyDefinition { kind: "t.family", version: 1, initial: |value| State { value }, migrate: None, checkpoint_when: None }).unwrap();
//! singleton(&token);
//! ```
//! Family seeds are typed:
//! ```compile_fail
//! use eukhe_durable::documents::{DocFamilyDefinition, DocToken, SessionDocFamily};
//! # #[derive(Default, serde::Serialize, serde::Deserialize)] struct State { value: u32 }
//! let token = SessionDocFamily::<State, u32>::define(DocFamilyDefinition { kind: "t.family", version: 1, initial: |value| State { value }, migrate: None, checkpoint_when: None }).unwrap();
//! token.encode_seed(&"seed");
//! ```
//! Latest conversation documents keep no history:
//! ```compile_fail
//! use eukhe_durable::documents::{ConversationDoc, DocDefinition, RewindableDocToken};
//! use eukhe_durable::types::LatestFork;
//! # #[derive(Default, serde::Serialize, serde::Deserialize)] struct State { value: u32 }
//! fn as_of<D: RewindableDocToken>(_: &D) {}
//! let token = ConversationDoc::<State>::define(DocDefinition { kind: "t.latest", version: 1, initial: State::default, migrate: None, checkpoint_when: None }, LatestFork::Current).unwrap();
//! as_of(&token);
//! ```
//! Session documents keep no history:
//! ```compile_fail
//! use eukhe_durable::documents::{DocDefinition, RewindableDocToken, SessionDoc};
//! # #[derive(Default, serde::Serialize, serde::Deserialize)] struct State { value: u32 }
//! fn as_of<D: RewindableDocToken>(_: &D) {}
//! let token = SessionDoc::<State>::define(DocDefinition { kind: "t.session", version: 1, initial: State::default, migrate: None, checkpoint_when: None }).unwrap();
//! as_of(&token);
//! ```
//! Task documents keep no history:
//! ```compile_fail
//! use eukhe_durable::documents::{DocDefinition, RewindableDocToken, TaskDoc};
//! # #[derive(Default, serde::Serialize, serde::Deserialize)] struct State { value: u32 }
//! fn as_of<D: RewindableDocToken>(_: &D) {}
//! let token = TaskDoc::<State>::define(DocDefinition { kind: "t.task", version: 1, initial: State::default, migrate: None, checkpoint_when: None }).unwrap();
//! as_of(&token);
//! ```
//! A data entry requires its data:
//! ```compile_fail
//! use eukhe_durable::types::TypedEntryDraft;
//! # #[derive(serde::Serialize, serde::Deserialize)] struct Note { text: String }
//! let wrong: TypedEntryDraft<Note> = TypedEntryDraft { model: None, head: None, edits: None };
//! ```
//! Data is typed by the token:
//! ```compile_fail
//! use eukhe_durable::types::TypedEntryDraft;
//! # #[derive(serde::Serialize, serde::Deserialize)] struct Note { text: String }
//! let wrong: TypedEntryDraft<Note> = TypedEntryDraft { model: None, data: Note { text: 1 }, head: None, edits: None };
//! ```
//! The token supplies the kind:
//! ```compile_fail
//! use eukhe_durable::types::TypedEntryDraft;
//! # #[derive(serde::Serialize, serde::Deserialize)] struct Note { text: String }
//! let wrong: TypedEntryDraft<Note> = TypedEntryDraft {
//!     kind: "t.note".to_owned(),
//!     model: None,
//!     data: Note { text: "x".to_owned() },
//!     head: None,
//!     edits: None,
//! };
//! ```
//! An entry kind without data takes none:
//! ```compile_fail
//! use eukhe_durable::types::{NoData, TypedEntryDraft};
//! let wrong: TypedEntryDraft<NoData> = TypedEntryDraft { model: None, data: 1, head: None, edits: None };
//! ```
//! An input submission carries no entry:
//! ```compile_fail
//! use eukhe_durable::harness::types::InputSubmissionDraft;
//! use eukhe_durable::types::EntryDraft;
//! let wrong = InputSubmissionDraft { request_id: None, content: "hi".into(), when_busy: None, entry: EntryDraft::new("note") };
//! ```
//! A write submission carries no content:
//! ```compile_fail
//! use eukhe_durable::harness::types::WriteSubmissionDraft;
//! use eukhe_durable::types::EntryDraft;
//! let wrong = WriteSubmissionDraft { request_id: None, entry: EntryDraft::new("note"), content: "hi".into() };
//! ```
//! A write submission never generates, so it has no busy policy:
//! ```compile_fail
//! use eukhe_durable::harness::types::{WhenBusy, WriteSubmissionDraft};
//! use eukhe_durable::types::EntryDraft;
//! let wrong = WriteSubmissionDraft { request_id: None, entry: EntryDraft::new("note"), when_busy: Some(WhenBusy::Steer) };
//! ```
//! Hook handlers are typed by the task's hooks:
//! ```compile_fail
//! use std::sync::Arc;
//! use eukhe_chord::context::Context;
//! use eukhe_durable::harness::define::hook;
//! use eukhe_durable::harness::types::{BeforeToolDecision, HookApi, HookFuture, ToolHooks};
//! use eukhe_durable::harness::TOOL_TASK;
//! let wrong = hook(&*TOOL_TASK, ToolHooks {
//!     before_tool: Some(Arc::new(|_call: &String, _api: &HookApi, _context: &Context| -> HookFuture<BeforeToolDecision> {
//!         Box::pin(async { Ok(None) })
//!     })),
//!     ..ToolHooks::default()
//! });
//! ```
//! Hook names come from the task's hooks:
//! ```compile_fail
//! use eukhe_durable::harness::define::hook;
//! use eukhe_durable::harness::types::ToolHooks;
//! use eukhe_durable::harness::TOOL_TASK;
//! let wrong = hook(&*TOOL_TASK, ToolHooks { after_step: None, ..ToolHooks::default() });
//! ```
//! Task input is typed by the definition (Rust's `Tx::create_task` takes the
//! erased definition and JSON input; the typed creation is
//! `ToolExecutionApiExt::create_task`):
//! ```compile_fail
//! use eukhe_chord::context::Context;
//! use eukhe_durable::harness::types::{InvocationTaskOptions, ToolExecutionApi, ToolExecutionApiExt};
//! use eukhe_durable::tasks::{define_task, TaskDefinition};
//! use eukhe_durable::types::TaskOwnership;
//! # #[derive(serde::Serialize, serde::Deserialize)] struct Input { steps: f64 }
//! # #[derive(serde::Serialize, serde::Deserialize)] #[serde(tag = "phase")] enum Checkpoint { Plan }
//! fn wrong(api: &dyn ToolExecutionApi, cx: &Context) {
//!     let stepper = define_task(TaskDefinition::<Input, Checkpoint, (), ()>::new(
//!         "test.stepper",
//!         1,
//!         |_: &Input| Ok(Checkpoint::Plan),
//!         |_task, _runtime, _cx| async { Ok(()) },
//!     ));
//!     let options = InvocationTaskOptions { ownership: TaskOwnership::Conversation, background: None };
//!     let _ = api.create_task(&stepper, &"two", options, cx);
//! }
//! ```
//!
//! The phase map is exhaustive: no Rust equivalent. Phases are registered at
//! run time with `TaskDefinition::phase`, keyed by the checkpoint's `phase`
//! string, so a missing handler cannot be a compile error; a checkpoint
//! without a handler faults the task when it runs.
