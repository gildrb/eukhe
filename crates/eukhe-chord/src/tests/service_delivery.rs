//! Port of `test/service-delivery.test.ts`.
//!
//! TS `context === context` identity checks compare abort signals with
//! `AbortSignal::same`.

use std::sync::{Arc, Mutex, PoisonError};

use futures::future::BoxFuture;
use futures::FutureExt;
use serde_json::json as j;

use super::{json, Recorder};
use crate::context::{with_cancel, Context, BACKGROUND_CONTEXT};
use crate::error::{BoxError, ChordError, ErrorReporter};
use crate::json::JsonValue;
use crate::{
    create_remote_service_binding, create_service_state_decoder, create_service_state_encoder,
    define_service, parse_wire_service_provider_update, parse_wire_service_subscription_snapshot,
    replicated_state, MethodFuture, MutableReplicatedState, ProviderSubscription,
    RemoteServiceBindingOptions, RemoteServiceProvider, RemoteServiceTransport, Service,
    ServiceCall, ServiceHandle, ServiceMode, ServiceObject, ServiceObserver,
    ServiceProviderDefinition, ServiceProviderUpdate, ServiceStateDecoder, ServiceStateEncoder,
    ServiceSubscription, ServiceSubscriptionSnapshot, ServiceUpdateListener,
};

type Updates = Recorder<ServiceProviderUpdate>;

fn bg() -> Context {
    BACKGROUND_CONTEXT.clone()
}

fn counter() -> Service<()> {
    define_service::<()>("test.delivery-counter").unwrap()
}

fn value_of(value: i64) -> JsonValue {
    json(j!({ "value": value }))
}

fn put(state: &MutableReplicatedState, value: i64, context: &Context) {
    state.replace(context, value_of(value)).unwrap();
}

fn set(state: &MutableReplicatedState, value: i64) {
    state
        .change(&bg(), |draft| {
            draft
                .set("value", value_of(value)["value"].clone())
                .map(drop)
        })
        .unwrap();
}

fn counter_object(state: &MutableReplicatedState) -> ServiceObject {
    ServiceObject::new().state("state", state)
}

fn counter_provider(state: &MutableReplicatedState) -> (Service<()>, RemoteServiceProvider) {
    let counter = counter();
    let provider =
        RemoteServiceProvider::new([ServiceProviderDefinition::singleton(&counter)]).unwrap();
    provider.provide(&counter, counter_object(state)).unwrap();
    (counter, provider)
}

fn record_into(updates: &Updates) -> ServiceUpdateListener {
    let updates = updates.clone();
    Arc::new(
        move |update: ServiceProviderUpdate, _cx: &Context| -> Result<(), ChordError> {
            updates.push(update);
            Ok(())
        },
    )
}

fn to_json(updates: &Updates) -> Vec<JsonValue> {
    updates
        .get()
        .iter()
        .map(ServiceProviderUpdate::to_json)
        .collect()
}

fn kinds(updates: &Updates) -> Vec<&'static str> {
    updates
        .get()
        .iter()
        .map(ServiceProviderUpdate::kind)
        .collect()
}

fn sequence_of(update: &ServiceProviderUpdate) -> Option<u64> {
    match update {
        ServiceProviderUpdate::State { sequence, .. } => Some(*sequence),
        _ => None,
    }
}

/// `toMatchObject({ type: "reset", snapshot: { instances: [{ members: [{ sequence, ops }] }] } })`.
fn assert_single_reset(update: &ServiceProviderUpdate, sequence: i64) {
    let value = update.to_json();
    assert_eq!(value["type"], json(j!("reset")));
    let member = &value["snapshot"]["instances"][0]["members"][0];
    assert_eq!(member["sequence"], json(j!(sequence)));
    assert_eq!(member["ops"], json(j!([["r", { "value": sequence }]])));
}

struct Codecs {
    encoder: ServiceStateEncoder,
    decoder: ServiceStateDecoder,
}

struct WireTransport {
    provider: RemoteServiceProvider,
    before_activate: Arc<dyn Fn() + Send + Sync>,
    updates: Updates,
}

struct WireSubscription {
    subscription: ProviderSubscription,
    snapshot: ServiceSubscriptionSnapshot,
    before_activate: Arc<dyn Fn() + Send + Sync>,
}

impl ServiceSubscription for WireSubscription {
    fn snapshot(&self) -> &ServiceSubscriptionSnapshot {
        &self.snapshot
    }

    fn activate(&self) -> Result<(), ChordError> {
        (self.before_activate)();
        self.subscription.activate()
    }

    fn close(&self, _context: &Context) -> BoxFuture<'static, Result<(), ChordError>> {
        self.subscription.close();
        futures::future::ready(Ok(())).boxed()
    }
}

impl RemoteServiceTransport for WireTransport {
    fn invoke(&self, call: ServiceCall, context: &Context) -> MethodFuture {
        self.provider.invoke(call, context)
    }

    fn subscribe(
        &self,
        service_id: &str,
        mode: ServiceMode,
        listener: ServiceUpdateListener,
        _context: &Context,
    ) -> BoxFuture<'static, Result<Box<dyn ServiceSubscription>, ChordError>> {
        let codecs = Arc::new(Mutex::new(Codecs {
            encoder: create_service_state_encoder(),
            decoder: create_service_state_decoder(),
        }));
        let updates = self.updates.clone();
        let wire_codecs = Arc::clone(&codecs);
        let wire_listener: ServiceUpdateListener = Arc::new(move |update, context| {
            let decoded = {
                let mut codecs = wire_codecs.lock().unwrap_or_else(PoisonError::into_inner);
                let wire = codecs.encoder.encode_update(&update)?;
                let parsed = parse_wire_service_provider_update(&wire.to_json())?;
                codecs.decoder.decode_update(&parsed)?
            };
            updates.push(decoded.clone());
            listener(decoded, context)
        });
        let result = (|| {
            let subscription = self.provider.subscribe(service_id, mode, wire_listener)?;
            let snapshot = {
                let mut codecs = codecs.lock().unwrap_or_else(PoisonError::into_inner);
                let wire = codecs.encoder.encode_snapshot(subscription.snapshot())?;
                let parsed = parse_wire_service_subscription_snapshot(&wire.to_json())?;
                codecs.decoder.decode_snapshot(&parsed)?
            };
            Ok(Box::new(WireSubscription {
                subscription,
                snapshot,
                before_activate: Arc::clone(&self.before_activate),
            }) as Box<dyn ServiceSubscription>)
        })();
        futures::future::ready(result).boxed()
    }
}

fn wire_transport(
    provider: &RemoteServiceProvider,
    before_activate: impl Fn() + Send + Sync + 'static,
    updates: &Updates,
) -> Arc<dyn RemoteServiceTransport> {
    Arc::new(WireTransport {
        provider: provider.clone(),
        before_activate: Arc::new(before_activate),
        updates: updates.clone(),
    })
}

fn errors_recorder() -> (Recorder<ChordError>, ErrorReporter) {
    let errors = Recorder::default();
    let record = errors.clone();
    (errors, Arc::new(move |error| record.push(error)))
}

fn state_value(handle: &ServiceHandle, member: &str) -> Option<JsonValue> {
    handle.member(member).unwrap().value().unwrap()
}

#[test]
fn appends_reentrant_updates_to_the_activation_fifo() -> Result<(), BoxError> {
    let state = replicated_state(value_of(0))?;
    let (counter, provider) = counter_provider(&state);
    let received: Recorder<u64> = Recorder::default();
    let record = received.clone();
    let target = state.clone();
    let subscription = provider.subscribe(
        counter.id(),
        ServiceMode::Singleton,
        Arc::new(move |update, _cx| {
            let Some(sequence) = sequence_of(&update) else {
                return Ok(());
            };
            record.push(sequence);
            if sequence == 1 {
                put(&target, 3, &bg());
            }
            Ok(())
        }),
    )?;
    put(&state, 1, &bg());
    put(&state, 2, &bg());
    subscription.activate()?;
    subscription.activate()?;
    assert_eq!(received.get(), vec![1, 2, 3]);
    provider.dispose()?;
    Ok(())
}

fn bounds_pending_updates_with_explicit_root_resets(count: i64) -> Result<(), BoxError> {
    let state = replicated_state(value_of(0))?;
    let (counter, provider) = counter_provider(&state);
    let updates = Updates::default();
    let contexts: Recorder<Context> = Recorder::default();
    let (record_updates, record_contexts) = (updates.clone(), contexts.clone());
    let subscription = provider.subscribe(
        counter.id(),
        ServiceMode::Singleton,
        Arc::new(move |update, context| {
            record_updates.push(update);
            record_contexts.push(context.clone());
            Ok(())
        }),
    )?;
    let (context, _cancel) = with_cancel(&bg());
    for value in 1..=count {
        put(&state, value, &context);
    }
    assert_eq!(updates.len(), 0);
    assert_eq!(
        subscription.snapshot().instances[0].members[0].to_json()["sequence"],
        json(j!(0))
    );
    subscription.activate()?;
    let first = (count - 1) / 100 * 100 + 1;
    assert_eq!(updates.len(), usize::try_from(count - first + 1)?);
    if count > 100 {
        assert_eq!(
            updates.get()[0].to_json(),
            json(j!({
                "type": "reset",
                "snapshot": {
                    "serviceId": counter.id(),
                    "mode": "singleton",
                    "instances": [{ "members": [{ "name": "state", "kind": "state", "sequence": first, "ops": [["r", { "value": first }]] }] }],
                },
            }))
        );
    }
    let signal = context.abort_signal().unwrap();
    assert!(contexts.get().iter().all(|received| received
        .abort_signal()
        .is_some_and(|other| other.same(&signal))));
    put(&state, count + 1, &context);
    let last = updates.get().last().cloned().unwrap();
    assert_eq!(last.kind(), "state");
    assert_eq!(sequence_of(&last), Some(u64::try_from(count + 1)?));
    provider.dispose()?;
    Ok(())
}

#[test]
fn bounds_pending_updates_with_explicit_root_resets_each() -> Result<(), BoxError> {
    for count in [100, 101, 102, 201, 202] {
        bounds_pending_updates_with_explicit_root_resets(count)?;
    }
    Ok(())
}

#[test]
fn does_not_compact_the_running_delivery_when_activation_overflows_reentrantly(
) -> Result<(), BoxError> {
    let state = replicated_state(value_of(0))?;
    let (counter, provider) = counter_provider(&state);
    let updates = Updates::default();
    let record = updates.clone();
    let target = state.clone();
    let subscription = provider.subscribe(
        counter.id(),
        ServiceMode::Singleton,
        Arc::new(move |update, _cx| {
            let first = sequence_of(&update) == Some(1);
            record.push(update);
            if first {
                for value in 3..=103 {
                    put(&target, value, &bg());
                }
            }
            Ok(())
        }),
    )?;
    put(&state, 1, &bg());
    put(&state, 2, &bg());
    subscription.activate()?;
    let received = updates.get();
    assert_eq!(received.len(), 3);
    assert_eq!(sequence_of(&received[0]), Some(1));
    assert_single_reset(&received[1], 102);
    assert_eq!(sequence_of(&received[2]), Some(103));
    provider.dispose()?;
    Ok(())
}

#[test]
fn suppresses_notifications_already_covered_by_an_overflow_snapshot() -> Result<(), BoxError> {
    let state = replicated_state(value_of(0))?;
    let target = state.clone();
    state
        .state_ref()
        .subscribe(move |_ops, sequence, _cx| -> Result<(), BoxError> {
            if sequence == 101 {
                put(&target, 102, &bg());
                put(&target, 103, &bg());
            }
            Ok(())
        });
    let (counter, provider) = counter_provider(&state);
    let updates = Updates::default();
    let subscription =
        provider.subscribe(counter.id(), ServiceMode::Singleton, record_into(&updates))?;
    for value in 1..=101 {
        put(&state, value, &bg());
    }
    subscription.activate()?;
    assert_eq!(updates.len(), 1);
    assert_single_reset(&updates.get()[0], 103);
    put(&state, 104, &bg());
    let second = updates.get()[1].clone();
    assert_eq!(second.kind(), "state");
    assert_eq!(sequence_of(&second), Some(104));
    provider.dispose()?;
    Ok(())
}

#[test]
fn preserves_lifecycle_ordering_across_subscribers_during_reentrant_publication(
) -> Result<(), BoxError> {
    let state = replicated_state(value_of(0))?;
    let (counter, provider) = counter_provider(&state);
    let first = Updates::default();
    let second = Updates::default();
    let record = first.clone();
    let target = provider.clone();
    let service = counter.clone();
    provider
        .subscribe(
            counter.id(),
            ServiceMode::Singleton,
            Arc::new(move |update, _cx| {
                record.push(update);
                if record.len() == 1 {
                    target.replace(&service, counter_object(&replicated_state(value_of(2))?))?;
                }
                Ok(())
            }),
        )?
        .activate()?;
    provider
        .subscribe(counter.id(), ServiceMode::Singleton, record_into(&second))?
        .activate()?;
    provider.replace(&counter, counter_object(&replicated_state(value_of(1))?))?;
    assert_eq!(to_json(&first), to_json(&second));
    assert_eq!(second.len(), 2);
    let replaced = second.get()[0].to_json();
    assert_eq!(replaced["type"], json(j!("replaced")));
    assert_eq!(
        replaced["snapshot"]["members"][0]["ops"],
        json(j!([["r", { "value": 1 }]]))
    );
    provider.dispose()?;
    Ok(())
}

#[test]
fn close_during_a_callback_prevents_later_buffered_callbacks() -> Result<(), BoxError> {
    let state = replicated_state(value_of(0))?;
    let (counter, provider) = counter_provider(&state);
    let received = Updates::default();
    let record = received.clone();
    let slot: Arc<Mutex<Option<Arc<ProviderSubscription>>>> = Arc::default();
    let own = Arc::clone(&slot);
    let subscription = Arc::new(provider.subscribe(
        counter.id(),
        ServiceMode::Singleton,
        Arc::new(move |update, _cx| {
            record.push(update);
            if let Some(subscription) = own.lock().unwrap_or_else(PoisonError::into_inner).clone() {
                subscription.close();
            }
            Ok(())
        }),
    )?);
    *slot.lock().unwrap_or_else(PoisonError::into_inner) = Some(Arc::clone(&subscription));
    put(&state, 1, &bg());
    put(&state, 2, &bg());
    subscription.activate()?;
    assert_eq!(received.len(), 1);
    slot.lock().unwrap_or_else(PoisonError::into_inner).take();
    provider.dispose()?;
    Ok(())
}

#[test]
fn drains_terminal_updates_when_disposed_reentrantly() -> Result<(), BoxError> {
    let state = replicated_state(value_of(0))?;
    let (counter, provider) = counter_provider(&state);
    let received = Updates::default();
    let record = received.clone();
    let target = provider.clone();
    let subscription = provider.subscribe(
        counter.id(),
        ServiceMode::Singleton,
        Arc::new(move |update, _cx| {
            let is_state = update.kind() == "state";
            record.push(update);
            if is_state {
                target.dispose()?;
            }
            Ok(())
        }),
    )?;
    put(&state, 1, &bg());
    subscription.activate()?;
    assert_eq!(kinds(&received), vec!["state", "unavailable"]);
    Ok(())
}

#[tokio::test]
async fn rebaselines_every_member_through_wire_codecs_then_resumes_contiguous_deltas(
) -> Result<(), BoxError> {
    let pair = define_service::<()>("test.delivery-pair")?;
    let provider = RemoteServiceProvider::new([ServiceProviderDefinition::singleton(&pair)])?;
    let left = replicated_state(value_of(0))?;
    let right = replicated_state(value_of(0))?;
    provider.provide(
        &pair,
        ServiceObject::new()
            .state("left", &left)
            .state("right", &right),
    )?;
    let (errors, on_error) = errors_recorder();
    let updates = Updates::default();
    let (before_left, before_right) = (left.clone(), right.clone());
    let mut options = RemoteServiceBindingOptions::new(
        vec![pair.id().to_owned()],
        wire_transport(
            &provider,
            move || {
                for value in 1..=101 {
                    set(&before_left, value);
                    set(&before_right, value);
                }
            },
            &updates,
        ),
    );
    options.on_error = Some(on_error);
    let namespace = create_remote_service_binding(options)?;
    let handle = namespace.use_service(&pair)?;
    namespace.ready(&bg()).await?;
    assert_eq!(kinds(&updates), vec!["reset", "state"]);
    assert_eq!(state_value(&handle, "left"), Some(value_of(101)));
    assert_eq!(state_value(&handle, "right"), Some(value_of(101)));
    for value in 102..=104 {
        set(&left, value);
        set(&right, value);
    }
    assert_eq!(state_value(&handle, "left"), Some(value_of(104)));
    assert_eq!(state_value(&handle, "right"), Some(value_of(104)));
    assert_eq!(errors.len(), 0);
    namespace.dispose(&bg()).await?;
    provider.dispose()?;
    Ok(())
}

#[tokio::test]
async fn an_overflow_reset_can_make_a_singleton_unavailable_before_a_later_replacement(
) -> Result<(), BoxError> {
    let state = replicated_state(value_of(0))?;
    let (counter, provider) = counter_provider(&state);
    let updates = Updates::default();
    let (errors, on_error) = errors_recorder();
    let (target, service) = (provider.clone(), counter.clone());
    let mut options = RemoteServiceBindingOptions::new(
        vec![counter.id().to_owned()],
        wire_transport(
            &provider,
            move || {
                for value in 1..=100 {
                    target
                        .replace(
                            &service,
                            counter_object(&replicated_state(value_of(value)).unwrap()),
                        )
                        .unwrap();
                }
                target.withdraw(&service).unwrap();
            },
            &updates,
        ),
    );
    options.on_error = Some(on_error);
    let namespace = create_remote_service_binding(options)?;
    let handle = namespace.use_service(&counter)?;
    namespace.ready(&bg()).await?;
    assert_eq!(
        to_json(&updates),
        vec![json(j!({
            "type": "reset",
            "snapshot": { "serviceId": counter.id(), "mode": "singleton", "instances": [] },
        }))]
    );
    assert_eq!(state_value(&handle, "state"), None);
    let replacement = replicated_state(value_of(200))?;
    provider.replace(&counter, counter_object(&replacement))?;
    set(&replacement, 201);
    assert!(namespace.use_service(&counter)?.same(&handle));
    assert_eq!(state_value(&handle, "state"), Some(value_of(201)));
    assert_eq!(errors.len(), 0);
    namespace.dispose(&bg()).await?;
    provider.dispose()?;
    Ok(())
}

#[tokio::test]
async fn keyed_resets_retain_live_generations_and_reconcile_closed_and_reused_keys(
) -> Result<(), BoxError> {
    let counter = counter();
    let provider = RemoteServiceProvider::new([ServiceProviderDefinition::keyed(&counter)])?;
    let retained = replicated_state(value_of(0))?;
    provider.spawn(&counter, "retained", counter_object(&retained))?;
    let close_old = provider.spawn(
        &counter,
        "reused",
        counter_object(&replicated_state(value_of(0))?),
    )?;
    let removed = provider.spawn(
        &counter,
        "removed",
        counter_object(&replicated_state(value_of(0))?),
    )?;
    let updates = Updates::default();
    let (errors, on_error) = errors_recorder();
    let mut options = RemoteServiceBindingOptions::new(
        vec![counter.id().to_owned()],
        wire_transport(&provider, || {}, &updates),
    );
    options.on_error = Some(on_error);
    let namespace = create_remote_service_binding(options)?;
    let observed: Recorder<(ServiceHandle, Context)> = Recorder::default();
    let record = observed.clone();
    namespace.observe(
        &counter,
        ServiceObserver::new(move |service, context| record.push((service, context))),
    )?;
    namespace.ready(&bg()).await?;
    assert_eq!(observed.len(), 3);
    // Provider snapshots are sorted by key.
    let stable = observed.get()[1].clone();
    let old = observed.get()[2].clone();
    let replacement = replicated_state(value_of(500))?;
    let (target, service, retained_target, replacement_target) = (
        provider.clone(),
        counter.clone(),
        retained.clone(),
        replacement.clone(),
    );
    stable
        .0
        .member("state")?
        .subscribe(crate::StateListener::new(
            move |value: JsonValue, _cx, _delivery| {
                if value["value"] != json(j!(1)) {
                    return;
                }
                close_old.close().unwrap();
                removed.close().unwrap();
                target
                    .spawn(&service, "reused", counter_object(&replacement_target))
                    .unwrap();
                put(&retained_target, 102, &bg());
                for next in 501..=601 {
                    put(&replacement_target, next, &bg());
                }
            },
        ))?;
    put(&retained, 1, &bg());
    assert!(updates.get().iter().any(|update| update.kind() == "reset"));
    assert_eq!(observed.len(), 4);
    assert!(!stable.1.aborted());
    assert_eq!(state_value(&stable.0, "state"), Some(value_of(102)));
    assert!(old.1.aborted());
    assert!(observed.get()[0].1.aborted());
    let fourth = observed.get()[3].0.clone();
    assert_eq!(state_value(&fourth, "state"), Some(value_of(601)));
    set(&replacement, 602);
    assert_eq!(state_value(&fourth, "state"), Some(value_of(602)));
    assert_eq!(errors.len(), 0);
    namespace.dispose(&bg()).await?;
    provider.dispose()?;
    Ok(())
}
