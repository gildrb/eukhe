//! Port of `test/state.test.ts`.
//!
//! Not ported: "rejects `PromiseLike` callbacks and aborts their draft" (a Rust
//! change callback returns `Result<(), E>`, so an asynchronous callback does
//! not compile) and the `Object.isFrozen` checks (`JsonValue` is immutable by
//! type). The NaN update in "clears a replica when an adopted update is
//! invalid" cannot be built: `JsonValue` numbers are finite.

use std::sync::{Arc, Mutex, PoisonError};

use serde_json::json as j;

use super::{json, ops_json, Recorder};
use crate::context::{Context, BACKGROUND_CONTEXT};
use crate::delta::{Draft, Op};
use crate::error::{BoxError, ChordError};
use crate::json::JsonValue;
use crate::services::state::{
    replicated_state, replicated_state_from_source, ReplicatedStateReplica,
};
use crate::types::{
    DeliveryKind, ReplicatedStateDelivery, ReplicatedStateSource, ReplicatedStateSourceAttachment,
    ReplicatedStateSourceFrame, ReplicatedStateSourceOptions, ReplicatedStateSourceSnapshot,
    SourceFrameListener,
};
use crate::{AttachedReplicatedState, ReplicatedStateSnapshot};

type Step = Result<(), BoxError>;

fn bg() -> Context {
    BACKGROUND_CONTEXT.clone()
}

fn hydrate(sequence: u64) -> ReplicatedStateDelivery {
    ReplicatedStateDelivery {
        kind: DeliveryKind::Hydrate,
        sequence,
    }
}

#[test]
fn publishes_one_immutable_structurally_shared_revision() {
    let state = replicated_state(json(
        j!({ "changed": { "value": 1 }, "retained": { "value": 2 } }),
    ))
    .unwrap();
    let previous = state.value();
    let deliveries = Recorder::default();
    let record = deliveries.clone();
    state.subscribe(move |_value, _context, delivery| record.push(delivery.sequence));
    state
        .change(&bg(), |draft| -> Step {
            draft.child("changed")?.set("value", 3)?;
            draft.child("changed")?.set("value", 4)?;
            Ok(())
        })
        .unwrap();
    assert_eq!(
        state.value(),
        json(j!({ "changed": { "value": 4 }, "retained": { "value": 2 } }))
    );
    assert!(!state.value().strict_equals(&previous));
    assert!(!state.value()["changed"].strict_equals(&previous["changed"]));
    assert!(state.value()["retained"].strict_equals(&previous["retained"]));
    assert_eq!(deliveries.get(), vec![0, 1]);
}

#[test]
fn rolls_back_callback_failures_and_revokes_escaped_drafts() {
    let state = replicated_state(json(j!({ "nested": { "value": 1 } }))).unwrap();
    let previous = state.value();
    let escaped: Mutex<Option<Draft>> = Mutex::new(None);
    let error = state
        .change(&bg(), |draft| -> Step {
            let nested = draft.child("nested")?;
            *escaped.lock().unwrap_or_else(PoisonError::into_inner) = Some(nested.clone());
            nested.set("value", 2)?;
            Err("stop".into())
        })
        .unwrap_err();
    assert_eq!(error.to_string(), "stop");
    assert!(state.value().strict_equals(&previous));
    let escaped = escaped
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take()
        .unwrap();
    assert!(escaped.get("value").is_err());
}

#[test]
fn rejects_nested_changes_and_replacements_without_losing_the_outer_rollback() {
    let state = replicated_state(json(j!({ "left": 0, "right": 0 }))).unwrap();
    let nested = state.clone();
    let error = state
        .change(&bg(), |draft| -> Step {
            draft.set("left", 1)?;
            nested.change(&bg(), |inner| -> Step {
                inner.set("right", 2)?;
                Ok(())
            })?;
            Ok(())
        })
        .unwrap_err();
    assert!(error.to_string().contains("reentrantly"));
    assert_eq!(state.value(), json(j!({ "left": 0, "right": 0 })));
    let error = state
        .change(&bg(), |_draft| -> Step {
            nested.replace(&bg(), json(j!({ "left": 1, "right": 2 })))?;
            Ok(())
        })
        .unwrap_err();
    assert!(error.to_string().contains("change callback"));
    assert_eq!(state.value(), json(j!({ "left": 0, "right": 0 })));
}

#[test]
fn queues_listener_triggered_changes_in_sequence_order() {
    let state = replicated_state(json(j!({ "value": 0 }))).unwrap();
    let source_sequences = Recorder::default();
    let deliveries = Recorder::default();
    let late_deliveries = Recorder::default();
    let nested = Arc::new(Mutex::new(false));
    {
        let state = state.clone();
        let late_deliveries = late_deliveries.clone();
        state
            .clone()
            .state_ref()
            .subscribe(move |_ops, _sequence, _context| -> Step {
                let mut done = nested.lock().unwrap_or_else(PoisonError::into_inner);
                if !*done {
                    *done = true;
                    drop(done);
                    state.change(&bg(), |draft| -> Step {
                        draft.set("value", 2)?;
                        Ok(())
                    })?;
                    let late = late_deliveries.clone();
                    state.subscribe(move |_value, _context, delivery| late.push(delivery));
                }
                Ok(())
            });
    }
    let record = source_sequences.clone();
    state
        .state_ref()
        .subscribe(move |_ops, sequence, _context| -> Step {
            record.push(sequence);
            Ok(())
        });
    let record = deliveries.clone();
    state.subscribe(move |value, _context, delivery| {
        if delivery.kind == DeliveryKind::Update {
            record.push((value["value"].clone(), delivery.sequence));
        }
    });
    state
        .change(&bg(), |draft| -> Step {
            draft.set("value", 1)?;
            Ok(())
        })
        .unwrap();
    assert_eq!(source_sequences.get(), vec![1, 2]);
    assert_eq!(
        deliveries.get(),
        vec![(JsonValue::from(1), 1), (JsonValue::from(2), 2)]
    );
    assert_eq!(late_deliveries.get(), vec![hydrate(2)]);
}

#[test]
fn isolates_listener_failures_after_committing_the_revision() {
    let state = replicated_state(json(j!({ "value": 0 }))).unwrap();
    let received = Recorder::default();
    state
        .state_ref()
        .subscribe(|_ops, _sequence, _context| -> Step { Err("listener failed".into()) });
    let record = received.clone();
    state
        .state_ref()
        .subscribe(move |_ops, sequence, _context| -> Step {
            record.push(sequence);
            Ok(())
        });
    let error = state
        .change(&bg(), |draft| -> Step {
            draft.set("value", 1)?;
            Ok(())
        })
        .unwrap_err();
    assert_eq!(error.to_string(), "listener failed");
    assert_eq!(state.value(), json(j!({ "value": 1 })));
    assert_eq!(received.get(), vec![1]);
}

#[test]
fn copies_assigned_values_by_value() {
    let external = json(j!({ "value": 1 }));
    let state = replicated_state(json(j!({ "left": null, "right": null }))).unwrap();
    state
        .change(&bg(), |draft| -> Step {
            draft.set("left", external.clone())?;
            draft.set("right", external.clone())?;
            draft.child("left")?.set("value", 2)?;
            Ok(())
        })
        .unwrap();
    assert_eq!(external, json(j!({ "value": 1 })));
    assert_eq!(
        state.value(),
        json(j!({ "left": { "value": 2 }, "right": { "value": 1 } }))
    );
    assert!(!state.value()["left"].strict_equals(&state.value()["right"]));
}

#[test]
fn takes_immutable_ownership_of_alias_free_replacements() {
    let state = replicated_state(json(
        j!({ "left": { "value": 1 }, "right": { "value": 2 } }),
    ))
    .unwrap();
    let replacement = json(j!({ "left": { "value": 1 }, "right": { "value": 1 } }));
    state.replace(&bg(), replacement.clone()).unwrap();
    assert!(state.value().strict_equals(&replacement));
    assert!(!state.value()["left"].strict_equals(&state.value()["right"]));
    state
        .change(&bg(), |draft| -> Step {
            draft.child("left")?.set("value", 9)?;
            Ok(())
        })
        .unwrap();
    assert_eq!(
        state.value(),
        json(j!({ "left": { "value": 9 }, "right": { "value": 1 } }))
    );
}

#[test]
fn preserves_compact_string_splice_and_permutation_operations() {
    let state = replicated_state(json(
        j!({ "text": "abcdefgh", "values": [{ "id": "a" }, { "id": "b" }, { "id": "c" }] }),
    ))
    .unwrap();
    let batches = Recorder::default();
    let record = batches.clone();
    state
        .state_ref()
        .subscribe(move |ops, _sequence, _context| -> Step {
            record.push(ops_json(ops));
            Ok(())
        });
    state
        .change(&bg(), |draft| -> Step {
            draft.set("text", "defghxyz")?;
            draft.child("values")?.shift()?;
            Ok(())
        })
        .unwrap();
    state
        .change(&bg(), |draft| -> Step {
            draft.child("values")?.reverse()?;
            Ok(())
        })
        .unwrap();
    assert_eq!(
        batches.get(),
        vec![
            json(j!([
                ["t", ["text"], 3],
                ["a", ["text"], "xyz"],
                ["p", ["values"], 0, 1, []]
            ])),
            json(j!([["m", ["values"], [1, 0]]])),
        ]
    );
}

#[test]
fn validates_replica_revisions_without_freezing_shared_immutable_payloads() {
    let replica = ReplicatedStateReplica::new(Arc::new(|_| {}));
    let initial = json(j!({ "rows": [{ "value": 1 }] }));
    replica
        .hydrate(0, &[Op::Replace(initial.clone())], &bg())
        .unwrap();
    assert!(replica.current().unwrap().strict_equals(&initial));

    let inserted = json(j!({ "value": 2 }));
    replica
        .update(
            1,
            &[Op::Splice(
                vec!["rows".into()],
                1,
                0,
                vec![inserted.clone()],
            )],
            &bg(),
        )
        .unwrap();
    let value = replica.current().unwrap();
    assert!(!value.strict_equals(&initial));
    assert_eq!(value["rows"], json(j!([{ "value": 1 }, { "value": 2 }])));
    assert!(value["rows"][0].strict_equals(&initial["rows"][0]));
    assert!(value["rows"][1].strict_equals(&inserted));
    assert_eq!(initial["rows"].as_array().unwrap().len(), 1);
}

#[test]
fn clears_a_replica_when_an_adopted_update_is_invalid() {
    let errors = Recorder::<ChordError>::default();
    let record = errors.clone();
    let malformed = ReplicatedStateReplica::new(Arc::new(move |error| record.push(error)));
    malformed
        .hydrate(0, &[Op::Replace(json(j!({ "values": [1, 2] })))], &bg())
        .unwrap();
    assert!(malformed
        .update(1, &[Op::Move(vec!["values".into()], vec![0])], &bg())
        .is_err());
    assert_eq!(malformed.current(), None);
    let error = malformed
        .update(
            2,
            &[Op::Set(vec!["value".into()], JsonValue::from(2))],
            &bg(),
        )
        .unwrap_err();
    assert!(error.to_string().contains("before hydration"));
    assert_eq!(errors.len(), 0);
}

#[test]
fn replaces_atomically_and_ignores_deeply_equal_replacements() {
    let state = replicated_state(json(
        j!({ "value": { "nested": 1 }, "retained": { "nested": 2 } }),
    ))
    .unwrap();
    let previous = state.value();
    state
        .replace(
            &bg(),
            json(j!({ "value": { "nested": 1 }, "retained": { "nested": 2 } })),
        )
        .unwrap();
    assert!(state.value().strict_equals(&previous));
    let replacement: JsonValue = [
        ("value", json(j!({ "nested": 2 }))),
        ("retained", previous["retained"].clone()),
    ]
    .into_iter()
    .collect::<crate::json::JsonObject>()
    .into();
    state.replace(&bg(), replacement).unwrap();
    assert_eq!(
        state.value(),
        json(j!({ "value": { "nested": 2 }, "retained": { "nested": 2 } }))
    );
    assert!(state.value()["retained"].strict_equals(&previous["retained"]));
}

/// The TS `TestSource`.
#[derive(Clone)]
struct TestSource {
    inner: Arc<Mutex<TestSourceState>>,
}

struct TestSourceState {
    attachments: Vec<TestAttachment>,
    on_attach: Option<Arc<dyn Fn() + Send + Sync>>,
    value: JsonValue,
    cursor: i64,
}

impl TestSource {
    fn new(value: JsonValue, cursor: i64) -> Self {
        Self {
            inner: Arc::new(Mutex::new(TestSourceState {
                attachments: Vec::new(),
                on_attach: None,
                value,
                cursor,
            })),
        }
    }

    fn state(&self) -> std::sync::MutexGuard<'_, TestSourceState> {
        self.inner.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn attachment_count(&self) -> usize {
        self.state().attachments.len()
    }

    fn commit(&self, value: JsonValue, ops: Arc<[Op]>) {
        let cursor = self.state().cursor + 1;
        self.commit_at(value, ops, bg(), cursor);
    }

    fn commit_at(&self, value: JsonValue, ops: Arc<[Op]>, context: Context, cursor: i64) {
        let attachments = {
            let mut state = self.state();
            state.value = value.clone();
            state.cursor = cursor;
            state.attachments.clone()
        };
        let frame = ReplicatedStateSourceFrame {
            cursor,
            value,
            ops,
            context,
        };
        for attachment in attachments {
            attachment.publish(frame.clone());
        }
    }
}

impl ReplicatedStateSource for TestSource {
    fn attach(&self) -> Result<Box<dyn ReplicatedStateSourceAttachment>, BoxError> {
        let (attachment, on_attach) = {
            let mut state = self.state();
            let source = self.clone();
            let attachment = TestAttachment::new(
                ReplicatedStateSourceSnapshot {
                    value: state.value.clone(),
                    cursor: state.cursor,
                },
                source,
            );
            state.attachments.push(attachment.clone());
            (attachment, state.on_attach.clone())
        };
        if let Some(on_attach) = on_attach {
            on_attach();
        }
        Ok(Box::new(attachment))
    }
}

#[derive(Clone)]
struct TestAttachment {
    inner: Arc<Mutex<TestAttachmentState>>,
    snapshot: ReplicatedStateSourceSnapshot,
    source: TestSource,
}

struct TestAttachmentState {
    buffer: Vec<ReplicatedStateSourceFrame>,
    listener: Option<SourceFrameListener>,
    activated: bool,
    disposed: bool,
}

impl TestAttachment {
    fn new(snapshot: ReplicatedStateSourceSnapshot, source: TestSource) -> Self {
        Self {
            inner: Arc::new(Mutex::new(TestAttachmentState {
                buffer: Vec::new(),
                listener: None,
                activated: false,
                disposed: false,
            })),
            snapshot,
            source,
        }
    }

    fn publish(&self, frame: ReplicatedStateSourceFrame) {
        let listener = {
            let mut state = self.inner.lock().unwrap_or_else(PoisonError::into_inner);
            if state.disposed {
                return;
            }
            let Some(listener) = state.listener.clone() else {
                state.buffer.push(frame);
                return;
            };
            listener
        };
        listener(frame);
    }
}

impl ReplicatedStateSourceAttachment for TestAttachment {
    fn snapshot(&self) -> ReplicatedStateSourceSnapshot {
        self.snapshot.clone()
    }

    fn activate(&self, listener: SourceFrameListener) -> Result<(), BoxError> {
        let buffered = {
            let mut state = self.inner.lock().unwrap_or_else(PoisonError::into_inner);
            if state.activated {
                return Err("attachment is already active".into());
            }
            state.activated = true;
            state.listener = Some(Arc::clone(&listener));
            std::mem::take(&mut state.buffer)
        };
        for frame in buffered {
            listener(frame);
        }
        Ok(())
    }

    fn dispose(&self) -> Result<(), BoxError> {
        {
            let mut state = self.inner.lock().unwrap_or_else(PoisonError::into_inner);
            if state.disposed {
                return Ok(());
            }
            state.disposed = true;
            state.buffer.clear();
        }
        self.source
            .state()
            .attachments
            .retain(|candidate| !Arc::ptr_eq(&candidate.inner, &self.inner));
        Ok(())
    }
}

fn set_value(value: i64) -> Arc<[Op]> {
    Arc::from(vec![Op::Set(
        vec!["value".into()],
        JsonValue::try_from(value).unwrap(),
    )])
}

fn value_of(value: i64) -> JsonValue {
    json(j!({ "value": value }))
}

fn attach(source: &TestSource) -> AttachedReplicatedState {
    replicated_state_from_source(source, ReplicatedStateSourceOptions::default()).unwrap()
}

#[test]
fn captures_before_activation_and_drains_queued_commits_in_order() {
    let first = value_of(1);
    let second = value_of(2);
    let source = TestSource::new(value_of(0), 10);
    {
        let source_for_hook = source.clone();
        let second = second.clone();
        source.state().on_attach = Some(Arc::new(move || {
            source_for_hook.commit(first.clone(), set_value(1));
            source_for_hook.commit(second.clone(), set_value(2));
        }));
    }
    let state = attach(&source);
    let deliveries = Recorder::default();
    let record = deliveries.clone();
    state.subscribe(move |value, _context, delivery| record.push((value, delivery.sequence)));
    assert!(state.value().strict_equals(&second));
    let delivered = deliveries.get();
    assert_eq!(delivered.len(), 1);
    assert!(delivered[0].0.strict_equals(&second));
    assert_eq!(delivered[0].1, 2);
    assert_eq!(
        state.state_ref().snapshot(),
        ReplicatedStateSnapshot {
            value: second,
            sequence: 2
        }
    );
}

#[test]
fn hydrates_at_sequence_zero_when_attaching_after_existing_commits() {
    let current = value_of(1);
    let source = TestSource::new(value_of(0), 40);
    source.commit(current.clone(), set_value(1));
    let state = attach(&source);
    let deliveries = Recorder::default();
    let record = deliveries.clone();
    state.subscribe(move |_value, _context, delivery| record.push(delivery.sequence));
    assert!(state.value().strict_equals(&current));
    assert_eq!(deliveries.get(), vec![0]);
}

#[test]
fn publishes_exact_source_value_and_operation_references_without_applying_or_re_diffing() {
    let source = TestSource::new(value_of(0), 0);
    let state = attach(&source);
    let next = value_of(1);
    let ops = set_value(1);
    let published_ops: Arc<Mutex<Option<Arc<[Op]>>>> = Arc::default();
    let record = Arc::clone(&published_ops);
    state
        .state_ref()
        .subscribe(move |received, _sequence, _context| -> Step {
            *record.lock().unwrap_or_else(PoisonError::into_inner) = Some(Arc::clone(received));
            Ok(())
        });
    let published_value = Recorder::default();
    let record = published_value.clone();
    state.subscribe(move |value, _context, delivery| {
        if delivery.kind == DeliveryKind::Update {
            record.push(value);
        }
    });

    source.commit(next.clone(), Arc::clone(&ops));
    assert!(state.value().strict_equals(&next));
    assert!(published_value.get()[0].strict_equals(&next));
    let published = published_ops
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .unwrap();
    assert!(Arc::ptr_eq(&published, &ops));
}

#[test]
fn buffers_reentrant_frames_and_skips_updates_covered_by_a_late_hydration() {
    let source = TestSource::new(value_of(0), 0);
    let state = attach(&source);
    let received = Recorder::default();
    let late = Recorder::default();
    let nested = Arc::new(Mutex::new(false));
    {
        let (source, state, late) = (source.clone(), state.clone(), late.clone());
        state
            .clone()
            .state_ref()
            .subscribe(move |_ops, sequence, _context| -> Step {
                let mut done = nested.lock().unwrap_or_else(PoisonError::into_inner);
                if sequence != 1 || *done {
                    return Ok(());
                }
                *done = true;
                drop(done);
                source.commit(value_of(2), set_value(2));
                let late = late.clone();
                state.subscribe(move |value, _context, delivery| {
                    late.push((delivery, value["value"].clone()));
                });
                Ok(())
            });
    }
    let record = received.clone();
    state.subscribe(move |value, _context, delivery| {
        if delivery.kind == DeliveryKind::Update {
            record.push(value["value"].clone());
        }
    });

    source.commit(value_of(1), set_value(1));
    assert_eq!(received.get(), vec![JsonValue::from(1), JsonValue::from(2)]);
    assert_eq!(late.get(), vec![(hydrate(2), JsonValue::from(2))]);
}

#[test]
fn reports_listener_failures_without_throwing_them_into_the_source() {
    let source = TestSource::new(value_of(0), 0);
    let errors = Recorder::<ChordError>::default();
    let record = errors.clone();
    let state = replicated_state_from_source(
        &source,
        ReplicatedStateSourceOptions {
            on_error: Some(Arc::new(move |error| record.push(error))),
        },
    )
    .unwrap();
    let received = Recorder::default();
    state.subscribe(|_value, _context, delivery| -> Step {
        if delivery.kind == DeliveryKind::Update {
            return Err("listener failed".into());
        }
        Ok(())
    });
    let record = received.clone();
    state.subscribe(move |value, _context, delivery| {
        if delivery.kind == DeliveryKind::Update {
            record.push(value["value"].clone());
        }
    });

    source.commit(value_of(1), set_value(1));
    source.commit(value_of(2), set_value(2));
    assert_eq!(received.get(), vec![JsonValue::from(1), JsonValue::from(2)]);
    let messages: Vec<String> = errors.get().iter().map(ToString::to_string).collect();
    assert_eq!(messages, vec!["listener failed", "listener failed"]);
}

#[test]
fn reports_cursor_gaps_disposes_the_broken_attachment_and_ignores_later_frames() {
    let source = TestSource::new(value_of(0), 5);
    let errors = Recorder::<ChordError>::default();
    let record = errors.clone();
    let state = replicated_state_from_source(
        &source,
        ReplicatedStateSourceOptions {
            on_error: Some(Arc::new(move |error| record.push(error))),
        },
    )
    .unwrap();
    source.commit_at(value_of(2), set_value(2), bg(), 7);
    assert!(errors.get()[0]
        .to_string()
        .contains("expected 6, received 7"));
    assert_eq!(source.attachment_count(), 0);
    assert_eq!(state.value(), value_of(0));
    source.commit_at(value_of(3), set_value(3), bg(), 8);
    assert_eq!(state.value(), value_of(0));
}

#[test]
fn keeps_attachments_independent_and_disposes_each_idempotently() {
    let source = TestSource::new(value_of(0), 0);
    let first = attach(&source);
    let second = attach(&source);
    assert_eq!(source.attachment_count(), 2);
    source.commit(value_of(1), set_value(1));
    assert_eq!(first.value()["value"], JsonValue::from(1));
    assert_eq!(second.value()["value"], JsonValue::from(1));

    first.dispose().unwrap();
    first.dispose().unwrap();
    assert_eq!(source.attachment_count(), 1);
    source.commit(value_of(2), set_value(2));
    assert_eq!(first.value()["value"], JsonValue::from(1));
    assert_eq!(second.value()["value"], JsonValue::from(2));
    second.dispose().unwrap();
    assert_eq!(source.attachment_count(), 0);
}
