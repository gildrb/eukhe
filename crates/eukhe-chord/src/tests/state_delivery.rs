//! Port of `test/state-delivery.test.ts`.

use std::sync::{Arc, Mutex, PoisonError};

use serde_json::json as j;

use super::{json, start_capturing_uncaught, take_uncaught, wait_for, Gate, Recorder};
use crate::callback::{Disposer, Outcome};
use crate::context::{with_cancel, Context, BACKGROUND_CONTEXT};
use crate::delta::Op;
use crate::error::{BoxError, ChordError, ErrorReporter};
use crate::json::JsonValue;
use crate::services::state::{
    replicated_state, replicated_state_from_source, ReplicatedStateReplica,
};
use crate::services::state_internals::ReplicatedStateRef;
use crate::types::{
    DeliveryKind, ReplicatedState, ReplicatedStateDelivery, ReplicatedStateSource,
    ReplicatedStateSourceAttachment, ReplicatedStateSourceFrame, ReplicatedStateSourceOptions,
    ReplicatedStateSourceSnapshot, SourceFrameListener, StateListener,
};

#[derive(Clone, Copy, Debug)]
enum Kind {
    Mutable,
    Attached,
    Replica,
}

type Publish = Arc<dyn Fn(i64, &Context) + Send + Sync>;

struct Fixture {
    state: Arc<dyn ReplicatedState>,
    publish: Publish,
    exact: Option<ReplicatedStateRef>,
}

fn bg() -> Context {
    BACKGROUND_CONTEXT.clone()
}

fn value_of(value: i64) -> JsonValue {
    json(j!({ "value": value }))
}

fn number(value: &JsonValue) -> i64 {
    value["value"].as_i64().unwrap()
}

fn update(sequence: u64) -> ReplicatedStateDelivery {
    ReplicatedStateDelivery {
        kind: DeliveryKind::Update,
        sequence,
    }
}

fn hydrate(sequence: u64) -> ReplicatedStateDelivery {
    ReplicatedStateDelivery {
        kind: DeliveryKind::Hydrate,
        sequence,
    }
}

struct CapturingSource {
    listener: Arc<Mutex<Option<SourceFrameListener>>>,
}

struct CapturingAttachment {
    listener: Arc<Mutex<Option<SourceFrameListener>>>,
}

impl ReplicatedStateSource for CapturingSource {
    fn attach(&self) -> Result<Box<dyn ReplicatedStateSourceAttachment>, BoxError> {
        Ok(Box::new(CapturingAttachment {
            listener: Arc::clone(&self.listener),
        }))
    }
}

impl ReplicatedStateSourceAttachment for CapturingAttachment {
    fn snapshot(&self) -> ReplicatedStateSourceSnapshot {
        ReplicatedStateSourceSnapshot {
            value: value_of(0),
            cursor: 0,
        }
    }

    fn activate(&self, listener: SourceFrameListener) -> Result<(), BoxError> {
        *self.listener.lock().unwrap_or_else(PoisonError::into_inner) = Some(listener);
        Ok(())
    }

    fn dispose(&self) -> Result<(), BoxError> {
        Ok(())
    }
}

fn set_value(value: i64) -> Vec<Op> {
    vec![Op::Set(
        vec!["value".into()],
        JsonValue::try_from(value).unwrap(),
    )]
}

fn fixture(kind: Kind, on_error: ErrorReporter) -> Fixture {
    match kind {
        Kind::Mutable => {
            let mutable = replicated_state(value_of(0)).unwrap();
            let target = mutable.clone();
            Fixture {
                exact: Some(mutable.state_ref()),
                state: Arc::new(mutable),
                publish: Arc::new(move |value, context| {
                    target.replace(context, value_of(value)).unwrap();
                }),
            }
        }
        Kind::Attached => {
            let listener: Arc<Mutex<Option<SourceFrameListener>>> = Arc::default();
            let source = CapturingSource {
                listener: Arc::clone(&listener),
            };
            let attached = replicated_state_from_source(
                &source,
                ReplicatedStateSourceOptions {
                    on_error: Some(on_error),
                },
            )
            .unwrap();
            Fixture {
                exact: Some(attached.state_ref()),
                state: Arc::new(attached),
                publish: Arc::new(move |value, context| {
                    let receive = listener
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .clone()
                        .unwrap();
                    receive(ReplicatedStateSourceFrame {
                        cursor: value,
                        value: value_of(value),
                        ops: Arc::from(set_value(value)),
                        context: context.clone(),
                    });
                }),
            }
        }
        Kind::Replica => {
            let replica = ReplicatedStateReplica::new(on_error);
            replica
                .hydrate(0, &[Op::Replace(value_of(0))], &bg())
                .unwrap();
            let target = replica.clone();
            Fixture {
                exact: None,
                state: Arc::new(replica),
                publish: Arc::new(move |value, context| {
                    target
                        .update(u64::try_from(value).unwrap(), &set_value(value), context)
                        .unwrap();
                }),
            }
        }
    }
}

fn quiet() -> ErrorReporter {
    Arc::new(|_| {})
}

fn record_exact(exact: Option<&ReplicatedStateRef>) -> Recorder<u64> {
    let recorder = Recorder::default();
    if let Some(exact) = exact {
        let record = recorder.clone();
        exact.subscribe(move |_ops, sequence, _context| -> Result<(), BoxError> {
            record.push(sequence);
            Ok(())
        });
    }
    recorder
}

async fn awaits_hydration_and_each_update_independently(kind: Kind) {
    let Fixture {
        state,
        publish,
        exact,
    } = fixture(kind, quiet());
    let hydration = Gate::new();
    let update_gate = Gate::new();
    let events = Recorder::<String>::default();
    let fast = Recorder::default();
    let exact_sequences = record_exact(exact.as_ref());
    {
        let (events, hydration, update_gate) =
            (events.clone(), hydration.clone(), update_gate.clone());
        state.subscribe(StateListener::new(move |value, _context, _delivery| {
            let value = number(&value);
            events.push(format!("start:{value}"));
            let gate = match value {
                0 => Some(hydration.clone()),
                1 => Some(update_gate.clone()),
                _ => None,
            };
            let events = events.clone();
            Outcome::pending(async move {
                if let Some(gate) = gate {
                    gate.wait().await?;
                }
                events.push(format!("end:{value}"));
                Ok::<(), ChordError>(())
            })
        }));
    }
    let record = fast.clone();
    state.subscribe(StateListener::new(move |value, _context, _delivery| {
        record.push(number(&value));
    }));
    publish(1, &bg());
    publish(2, &bg());
    assert_eq!(events.get(), vec!["start:0"]);
    assert_eq!(fast.get(), vec![0, 1, 2]);
    assert_eq!(state.value(), Some(value_of(2)));
    if exact.is_some() {
        assert_eq!(exact_sequences.get(), vec![1, 2]);
    }
    hydration.resolve();
    wait_for(|| events.get() == ["start:0", "end:0", "start:1"]).await;
    update_gate.resolve();
    wait_for(|| events.get() == ["start:0", "end:0", "start:1", "end:1", "start:2", "end:2"]).await;
}

async fn bounds_pending_deliveries_without_changing_exact_publication(kind: Kind) {
    for count in [100_i64, 101, 102, 201, 202] {
        let Fixture {
            state,
            publish,
            exact,
        } = fixture(kind, quiet());
        let hydration = Gate::new();
        let received = Recorder::default();
        let exact_sequences = record_exact(exact.as_ref());
        {
            let (received, hydration) = (received.clone(), hydration.clone());
            state.subscribe(StateListener::new(move |value, _context, _delivery| {
                let value = number(&value);
                received.push(value);
                if value == 0 {
                    Outcome::pending(hydration.wait())
                } else {
                    Outcome::Done
                }
            }));
        }
        for value in 1..=count {
            publish(value, &bg());
        }
        assert_eq!(received.get(), vec![0]);
        if exact.is_some() {
            let expected: Vec<u64> = (1..=u64::try_from(count).unwrap()).collect();
            assert_eq!(exact_sequences.get(), expected);
        }
        hydration.resolve();
        hydration.wait().await.unwrap();
        let first = (count - 1) / 100 * 100 + 1;
        let expected: Vec<i64> = std::iter::once(0).chain(first..=count).collect();
        wait_for(|| received.len() == expected.len()).await;
        assert_eq!(received.get(), expected, "count {count}");
    }
}

async fn excludes_a_running_update_from_overflow(kind: Kind) {
    let Fixture { state, publish, .. } = fixture(kind, quiet());
    let gate = Gate::new();
    let (context, _cancel) = with_cancel(&bg());
    let received = Recorder::<(JsonValue, Context, ReplicatedStateDelivery)>::default();
    {
        let (received, gate) = (received.clone(), gate.clone());
        state.subscribe(StateListener::new(move |value, context, delivery| {
            let one = number(&value) == 1;
            received.push((value, context, delivery));
            if one {
                Outcome::pending(gate.wait())
            } else {
                Outcome::Done
            }
        }));
    }
    for value in 1..102 {
        publish(value, &bg());
    }
    publish(102, &context);
    let adopted = state.value().unwrap();
    publish(103, &bg());
    let values = |received: &Recorder<(JsonValue, Context, ReplicatedStateDelivery)>| -> Vec<i64> {
        received
            .get()
            .iter()
            .map(|(value, _, _)| number(value))
            .collect()
    };
    assert_eq!(values(&received), vec![0, 1]);
    gate.resolve();
    gate.wait().await.unwrap();
    wait_for(|| received.len() == 4).await;
    assert_eq!(values(&received), vec![0, 1, 102, 103]);
    let (value, delivered_context, delivery) = received.get()[2].clone();
    assert!(value.strict_equals(&adopted));
    assert!(delivered_context
        .abort_signal()
        .unwrap()
        .same(&context.abort_signal().unwrap()));
    assert_eq!(delivery, update(102));
}

fn serializes_reentrant_hydration_and_update_callbacks(kind: Kind) {
    let Fixture { state, publish, .. } = fixture(kind, quiet());
    let events = Recorder::<String>::default();
    let record = events.clone();
    state.subscribe(StateListener::new(move |value, _context, _delivery| {
        let value = number(&value);
        record.push(format!("start:{value}"));
        if value < 2 {
            publish(value + 1, &bg());
        }
        record.push(format!("end:{value}"));
    }));
    assert_eq!(
        events.get(),
        vec!["start:0", "end:0", "start:1", "end:1", "start:2", "end:2"]
    );
}

async fn treats_two_subscriptions_of_the_same_callback_independently(kind: Kind) {
    let Fixture { state, publish, .. } = fixture(kind, quiet());
    let gate = Gate::new();
    let received = Recorder::default();
    let listener = {
        let (received, gate) = (received.clone(), gate.clone());
        StateListener::new(move |value, _context, _delivery| {
            let value = number(&value);
            received.push(value);
            if value == 0 {
                Outcome::pending(gate.wait())
            } else {
                Outcome::Done
            }
        })
    };
    let stop_first = state.subscribe(listener.clone());
    let stop_second = state.subscribe(listener);
    publish(1, &bg());
    stop_first.dispose();
    stop_first.dispose();
    gate.resolve();
    gate.wait().await.unwrap();
    wait_for(|| received.len() == 3).await;
    assert_eq!(received.get(), vec![0, 0, 1]);
    stop_second.dispose();
}

async fn unsubscribe_drops_queued_callbacks_without_joining_or_aborting(kind: Kind) {
    let Fixture { state, publish, .. } = fixture(kind, quiet());
    let gate = Gate::new();
    let (context, _cancel) = with_cancel(&bg());
    let received = Recorder::default();
    let completed = Arc::new(Mutex::new(false));
    let stop: Disposer = {
        let (received, gate, completed) = (received.clone(), gate.clone(), Arc::clone(&completed));
        state.subscribe(StateListener::new(move |value, _context, _delivery| {
            let value = number(&value);
            received.push(value);
            let (gate, completed) = (gate.clone(), Arc::clone(&completed));
            Outcome::pending(async move {
                if value == 1 {
                    gate.wait().await?;
                    *completed.lock().unwrap_or_else(PoisonError::into_inner) = true;
                }
                Ok::<(), ChordError>(())
            })
        }))
    };
    publish(1, &context);
    publish(2, &context);
    stop.dispose();
    publish(3, &context);
    assert!(!context.aborted());
    assert!(!*completed.lock().unwrap_or_else(PoisonError::into_inner));
    gate.resolve();
    wait_for(|| *completed.lock().unwrap_or_else(PoisonError::into_inner)).await;
    assert_eq!(received.get(), vec![0, 1]);
}

fn errors_recorder() -> (Recorder<ChordError>, ErrorReporter) {
    let errors = Recorder::default();
    let record = errors.clone();
    (errors, Arc::new(move |error| record.push(error)))
}

fn isolates_a_synchronous_hydration_failure(kind: Kind) {
    let (errors, reporter) = errors_recorder();
    let Fixture { state, publish, .. } = fixture(kind, reporter);
    let received = Recorder::default();
    let record = received.clone();
    state.subscribe(StateListener::new(move |value, _context, _delivery| {
        let value = number(&value);
        record.push(value);
        if value == 0 {
            return Outcome::failed("sync hydration");
        }
        Outcome::Done
    }));
    publish(1, &bg());
    let messages: Vec<String> = errors.get().iter().map(ToString::to_string).collect();
    assert_eq!(messages, vec!["sync hydration"]);
    assert_eq!(received.get(), vec![0, 1]);
}

async fn observes_hydration_rejection_sync_throw_and_update_rejection(kind: Kind) {
    let (errors, reporter) = errors_recorder();
    let Fixture { state, publish, .. } = fixture(kind, reporter);
    let gate = Gate::new();
    let received = Recorder::default();
    let fast = Recorder::default();
    {
        let (received, gate) = (received.clone(), gate.clone());
        state.subscribe(StateListener::new(move |value, _context, _delivery| {
            let value = number(&value);
            received.push(value);
            match value {
                0 => Outcome::pending(gate.wait()),
                1 => Outcome::failed("sync update"),
                2 => Outcome::pending(async { Err::<(), BoxError>("async update".into()) }),
                _ => Outcome::Done,
            }
        }));
    }
    let record = fast.clone();
    state.subscribe(StateListener::new(move |value, _context, _delivery| {
        record.push(number(&value));
    }));
    for value in 1..=3 {
        publish(value, &bg());
    }
    gate.reject(ChordError::error("async hydration"));
    wait_for(|| received.get() == [0, 1, 2, 3]).await;
    let messages: Vec<String> = errors.get().iter().map(ToString::to_string).collect();
    assert_eq!(
        messages,
        vec!["async hydration", "sync update", "async update"]
    );
    assert_eq!(fast.get(), vec![0, 1, 2, 3]);
}

async fn still_observes_a_callback_rejection_after_unsubscribe(kind: Kind) {
    let (errors, reporter) = errors_recorder();
    let Fixture { state, publish, .. } = fixture(kind, reporter);
    let gate = Gate::new();
    let received = Recorder::default();
    let stop = {
        let (received, gate) = (received.clone(), gate.clone());
        state.subscribe(StateListener::new(move |value, _context, _delivery| {
            received.push(number(&value));
            Outcome::pending(gate.wait())
        }))
    };
    publish(1, &bg());
    stop.dispose();
    gate.reject(ChordError::error("stopped callback"));
    wait_for(|| errors.len() == 1).await;
    assert_eq!(errors.get()[0].to_string(), "stopped callback");
    assert_eq!(received.get(), vec![0]);
}

macro_rules! for_kinds {
    (async $name:ident, [$($kind:ident),+]) => {
        mod $name {
            $(
                #[allow(non_snake_case, reason = "one generated test per fixture kind")]
                #[tokio::test]
                async fn $kind() {
                    super::$name(super::Kind::$kind).await;
                }
            )+
        }
    };
    (sync $name:ident, [$($kind:ident),+]) => {
        mod $name {
            $(
                #[allow(non_snake_case, reason = "one generated test per fixture kind")]
                #[test]
                fn $kind() {
                    super::$name(super::Kind::$kind);
                }
            )+
        }
    };
}

for_kinds!(async awaits_hydration_and_each_update_independently, [Mutable, Attached, Replica]);
for_kinds!(async bounds_pending_deliveries_without_changing_exact_publication, [Mutable, Attached, Replica]);
for_kinds!(async excludes_a_running_update_from_overflow, [Mutable, Attached, Replica]);
for_kinds!(sync serializes_reentrant_hydration_and_update_callbacks, [Mutable, Attached, Replica]);
for_kinds!(async treats_two_subscriptions_of_the_same_callback_independently, [Mutable, Attached, Replica]);
for_kinds!(async unsubscribe_drops_queued_callbacks_without_joining_or_aborting, [Mutable, Attached, Replica]);
for_kinds!(sync isolates_a_synchronous_hydration_failure, [Attached, Replica]);
for_kinds!(async observes_hydration_rejection_sync_throw_and_update_rejection, [Attached, Replica]);
for_kinds!(async still_observes_a_callback_rejection_after_unsubscribe, [Attached, Replica]);

#[tokio::test]
async fn mutable_state_reports_rejected_callbacks_through_its_default_error_reporter() {
    start_capturing_uncaught();
    let state = replicated_state(value_of(0)).unwrap();
    let received = Recorder::default();
    let record = received.clone();
    state.subscribe(move |value, _context, _delivery| {
        let value = number(&value);
        record.push(value);
        if value == 0 {
            return Outcome::pending(async {
                Err::<(), BoxError>("async mutable hydration".into())
            });
        }
        Outcome::Done
    });
    state.replace(&bg(), value_of(1)).unwrap();
    wait_for(|| received.len() == 2).await;
    assert_eq!(received.get(), vec![0, 1]);
    let reports = take_uncaught();
    assert_eq!(reports.len(), 1);
    assert_eq!(reports[0].to_string(), "async mutable hydration");
}

#[tokio::test]
async fn replica_disconnect_drops_obsolete_pending_work_but_waits_for_the_running_callback() {
    let replica = ReplicatedStateReplica::new(quiet());
    let gate = Gate::new();
    let received = Recorder::default();
    {
        let (received, gate) = (received.clone(), gate.clone());
        replica.subscribe(StateListener::new(
            move |_value, _context, delivery: ReplicatedStateDelivery| {
                received.push(delivery);
                if delivery.sequence == 0 {
                    Outcome::pending(gate.wait())
                } else {
                    Outcome::Done
                }
            },
        ));
    }
    replica
        .hydrate(0, &[Op::Replace(value_of(0))], &bg())
        .unwrap();
    replica.update(1, &set_value(1), &bg()).unwrap();
    replica.clear();
    replica
        .hydrate(50, &[Op::Replace(value_of(50))], &bg())
        .unwrap();
    replica.update(51, &set_value(51), &bg()).unwrap();
    assert_eq!(received.get(), vec![hydrate(0)]);
    gate.resolve();
    gate.wait().await.unwrap();
    wait_for(|| received.len() == 3).await;
    assert_eq!(received.get(), vec![hydrate(0), hydrate(50), update(51)]);
}

#[test]
fn cold_replicas_hydrate_all_listeners_before_their_reentrant_updates() {
    let replica = ReplicatedStateReplica::new(quiet());
    let second = Recorder::default();
    let target = replica.clone();
    replica.subscribe(StateListener::new(
        move |_value, _context, delivery: ReplicatedStateDelivery| {
            if delivery.kind == DeliveryKind::Hydrate {
                target.update(1, &set_value(1), &bg()).unwrap();
            }
        },
    ));
    let record = second.clone();
    replica.subscribe(StateListener::new(move |_value, _context, delivery| {
        record.push(delivery);
    }));
    replica
        .hydrate(0, &[Op::Replace(value_of(0))], &bg())
        .unwrap();
    assert_eq!(second.get(), vec![hydrate(0), update(1)]);
}
