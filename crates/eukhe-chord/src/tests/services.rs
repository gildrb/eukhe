//! Port of `test/services.test.ts`.
//!
//! Deviations:
//! - `checks remote JSON contracts only at compile time`: the `@ts-expect-error`
//!   contract checks have no Rust counterpart (remote contracts are untyped JSON);
//!   only the observable `local` flags are ported.
//! - TS `toBe` on values uses `JsonValue::strict_equals`; on contexts,
//!   `AbortSignal` presence; on facades, `ServiceHandle::same`.
//! - `rejects mode mixing and unsupported members`: a `Date` member becomes a
//!   non-exposable `ServiceObject::value` member.

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use futures::future::BoxFuture;
use futures::FutureExt;
use serde_json::json as j;

use super::{json, wait_for, Recorder};
use crate::context::{Context, BACKGROUND_CONTEXT};
use crate::delta::Op;
use crate::error::{BoxError, ChordError, ErrorReporter};
use crate::json::JsonValue;
use crate::services::loopback::create_loopback_service_transport;
use crate::{
    create_remote_service_binding, define_local_service, define_service,
    parse_service_subscription_snapshot, replicated_state, replicated_state_from_source,
    MethodFuture, MutableReplicatedState, ProviderSubscription, RemoteServiceBindingOptions,
    RemoteServiceProvider, RemoteServiceTransport, ReplicatedStateSource,
    ReplicatedStateSourceAttachment, ReplicatedStateSourceFrame, ReplicatedStateSourceOptions,
    ReplicatedStateSourceSnapshot, Service, ServiceCall, ServiceHandle, ServiceMemberSnapshot,
    ServiceMode, ServiceObject, ServiceObserver, ServiceProviderDefinition, ServiceProviderUpdate,
    ServiceSubscription, ServiceSubscriptionSnapshot, ServiceUpdateListener, SourceFrameListener,
    StateListener,
};

fn bg() -> Context {
    BACKGROUND_CONTEXT.clone()
}

fn models() -> Service<()> {
    define_service::<()>("test.models").unwrap()
}

fn question_dialogs() -> Service<()> {
    define_service::<()>("test.question-dialog").unwrap()
}

fn models_state(revision: i64) -> MutableReplicatedState {
    replicated_state(json(j!({ "selected": null, "revision": revision }))).unwrap()
}

fn noop(object: ServiceObject, name: &str) -> ServiceObject {
    object.method(name, |_args, _cx| async { Ok::<_, BoxError>(None) })
}

fn models_object(state: &MutableReplicatedState) -> ServiceObject {
    noop(ServiceObject::new().state("state", state), "select")
}

fn dialog_object(request: &MutableReplicatedState, accepted: bool) -> ServiceObject {
    ServiceObject::new()
        .state("request", request)
        .method("submit", move |_args, _cx| async move {
            Ok::<_, BoxError>(Some(json(j!({ "accepted": accepted }))))
        })
}

fn revision(handle: &ServiceHandle) -> Option<JsonValue> {
    handle
        .state_value("state")
        .unwrap()
        .map(|value| value["revision"].clone())
}

fn rev(value: i64) -> JsonValue {
    json(j!(value))
}

fn set_revision(state: &MutableReplicatedState, value: i64) {
    state
        .change(&bg(), |draft| {
            draft.set("revision", json(j!(value))).map(drop)
        })
        .unwrap();
}

fn errors_recorder() -> (Recorder<ChordError>, ErrorReporter) {
    let errors = Recorder::default();
    let record = errors.clone();
    (errors, Arc::new(move |error| record.push(error)))
}

fn binding(
    services: &[&Service<()>],
    transport: Arc<dyn RemoteServiceTransport>,
) -> RemoteServiceBindingOptions {
    RemoteServiceBindingOptions::new(
        services
            .iter()
            .map(|service| service.id().to_owned())
            .collect(),
        transport,
    )
}

fn assert_message<T>(result: Result<T, ChordError>, expected: &str) {
    match result {
        Ok(_) => panic!("expected an error containing {expected:?}"),
        Err(error) => assert!(
            error.to_string().contains(expected),
            "{error} does not contain {expected:?}"
        ),
    }
}

fn record_updates(updates: &Recorder<ServiceProviderUpdate>) -> ServiceUpdateListener {
    let updates = updates.clone();
    Arc::new(move |update, _cx| {
        updates.push(update);
        Ok(())
    })
}

#[test]
fn checks_remote_json_contracts_only_at_compile_time() {
    assert!(!define_service::<()>("test.json-passthrough")
        .unwrap()
        .local());
    assert!(define_local_service::<()>("test.local-non-json")
        .unwrap()
        .local());
}

#[test]
fn marks_services_remotable_by_default_and_reserves_chord_service_ids() {
    let local = define_local_service::<String>("test.local").unwrap();
    assert!(!models().local());
    assert!(local.local());
    assert_message(
        define_local_service::<()>("$chord.internal"),
        "Service IDs beginning with $chord. are reserved",
    );
    assert_message(
        RemoteServiceProvider::new([ServiceProviderDefinition::singleton(&local)]),
        "cannot be published remotely",
    );
}

#[test]
fn tracks_mutable_source_state_while_publishing_immutable_revisions() -> Result<(), BoxError> {
    let initial = json(j!({ "selected": null, "revision": 0 }));
    let state = replicated_state(initial.clone())?;
    let delivered: Recorder<JsonValue> = Recorder::default();
    let deliveries: Recorder<&'static str> = Recorder::default();
    let (record, kinds) = (delivered.clone(), deliveries.clone());
    let unsubscribe = state.subscribe(move |value, _cx, delivery| {
        record.push(value);
        kinds.push(delivery.kind.as_str());
    });
    assert!(state.value().strict_equals(&initial));
    assert!(delivered
        .get()
        .last()
        .unwrap()
        .strict_equals(&state.value()));
    let hydrated = delivered.get().last().cloned().unwrap();

    state.change(&bg(), |draft| -> Result<(), BoxError> {
        draft.set(
            "selected",
            json(j!({ "provider": "test", "modelId": "one" })),
        )?;
        draft.set("revision", 1)?;
        Ok(())
    })?;
    assert_eq!(
        state.value(),
        json(j!({ "selected": { "provider": "test", "modelId": "one" }, "revision": 1 }))
    );
    assert!(!state.value().strict_equals(&initial));
    assert!(delivered
        .get()
        .last()
        .unwrap()
        .strict_equals(&state.value()));
    assert_eq!(hydrated, json(j!({ "selected": null, "revision": 0 })));
    assert_eq!(deliveries.get(), vec!["hydrate", "update"]);
    unsubscribe.dispose();
    Ok(())
}

#[test]
fn does_not_publish_when_a_transaction_restores_the_prior_value() -> Result<(), BoxError> {
    let state = replicated_state(json(j!({ "value": 1 })))?;
    let deliveries: Recorder<(&'static str, u64)> = Recorder::default();
    let record = deliveries.clone();
    state.subscribe(move |_value, _cx, delivery| {
        record.push((delivery.kind.as_str(), delivery.sequence));
    });
    state.change(&bg(), |draft| -> Result<(), BoxError> {
        draft.set("value", 2)?;
        draft.set("value", 1)?;
        Ok(())
    })?;
    assert_eq!(state.value(), json(j!({ "value": 1 })));
    assert_eq!(deliveries.get(), vec![("hydrate", 0)]);
    Ok(())
}

#[test]
fn hydrates_a_new_subscriber_from_the_latest_atomic_revision() -> Result<(), BoxError> {
    let state = replicated_state(json(j!({ "entries": [{ "id": "one" }] })))?;
    let first: Recorder<JsonValue> = Recorder::default();
    let record = first.clone();
    state.subscribe(move |value, _cx, _delivery| record.push(value));
    state.change(&bg(), |draft| {
        draft
            .child("entries")?
            .push([json(j!({ "id": "two" }))])
            .map(drop)
    })?;

    let second: Recorder<JsonValue> = Recorder::default();
    let record = second.clone();
    state.subscribe(move |value, _cx, _delivery| record.push(value));

    assert_eq!(
        first.get(),
        vec![
            json(j!({ "entries": [{ "id": "one" }] })),
            json(j!({ "entries": [{ "id": "one" }, { "id": "two" }] })),
        ]
    );
    assert_eq!(
        second.get(),
        vec![json(j!({ "entries": [{ "id": "one" }, { "id": "two" }] }))]
    );
    Ok(())
}

#[tokio::test]
async fn does_not_defensively_clone_method_arguments_or_results() -> Result<(), BoxError> {
    let echo = define_service::<()>("test.echo")?;
    let provider = RemoteServiceProvider::new([ServiceProviderDefinition::singleton(&echo)])?;
    let received: Recorder<JsonValue> = Recorder::default();
    let response = json(j!({ "value": "response" }));
    let (record, reply) = (received.clone(), response.clone());
    provider.provide(
        &echo,
        ServiceObject::new().method("echo", move |args, _cx| {
            record.push(args[0].clone());
            let reply = reply.clone();
            async move { Ok::<_, BoxError>(Some(reply)) }
        }),
    )?;
    let namespace = create_remote_service_binding(binding(
        &[&echo],
        create_loopback_service_transport(provider.clone()),
    ))?;
    let handle = namespace.use_service(&echo)?;
    namespace.ready(&bg()).await?;
    let request = json(j!({ "value": "request" }));

    let result = handle
        .call("echo", vec![request.clone()], &bg())?
        .await?
        .unwrap();
    assert!(result.strict_equals(&response));
    assert!(received.get()[0].strict_equals(&request));

    namespace.dispose(&bg()).await?;
    provider.dispose()?;
    Ok(())
}

#[tokio::test]
async fn provides_and_consumes_one_singleton_with_replicated_state() -> Result<(), BoxError> {
    let models = models();
    let provider = RemoteServiceProvider::new([ServiceProviderDefinition::singleton(&models)])?;
    assert_eq!(
        crate::catalogue_json(provider.catalogue()),
        json(j!([{ "serviceId": "test.models", "mode": "singleton" }]))
    );
    let initial_state = json(j!({ "selected": null, "revision": 0 }));
    let state = replicated_state(initial_state.clone())?;
    let published: Recorder<JsonValue> = Recorder::default();
    let (target, record) = (state.clone(), published.clone());
    provider.provide(
        &models,
        ServiceObject::new()
            .state("state", &state)
            .method("select", move |args, cx| {
                let result = target.change(&cx, |draft| -> Result<(), BoxError> {
                    draft.set("selected", args[0].clone())?;
                    let next = target.value()["revision"].as_i64().unwrap() + 1;
                    draft.set("revision", json(j!(next)))?;
                    Ok(())
                });
                record.push(target.value());
                async move { result.map(|()| None) }
            }),
    )?;
    let (errors, on_error) = errors_recorder();
    let mut options = binding(
        &[&models],
        create_loopback_service_transport(provider.clone()),
    );
    options.on_error = Some(on_error);
    let namespace = create_remote_service_binding(options)?;

    let first = namespace.use_service(&models)?;
    let second = namespace.use_service(&models)?;
    assert!(first.same(&second));
    assert_eq!(first.state_value("state")?, None);
    namespace.ready(&bg()).await?;
    assert_eq!(first.state_value("state")?, Some(initial_state));

    let updates: Recorder<JsonValue> = Recorder::default();
    let record = updates.clone();
    let unsubscribe =
        second
            .member("state")?
            .subscribe(StateListener::new(move |value, _cx, _delivery| {
                record.push(value);
            }))?;
    first
        .call(
            "select",
            vec![json(j!({ "provider": "test", "modelId": "one" }))],
            &bg(),
        )?
        .await?;
    assert_eq!(first.state_value("state")?, published.get().last().cloned());
    assert_eq!(
        first.state_value("state")?,
        Some(json(
            j!({ "selected": { "provider": "test", "modelId": "one" }, "revision": 1 })
        ))
    );
    assert_eq!(
        updates.get(),
        vec![
            json(j!({ "selected": null, "revision": 0 })),
            json(j!({ "selected": { "provider": "test", "modelId": "one" }, "revision": 1 })),
        ]
    );
    assert_eq!(errors.len(), 0);

    let late_namespace = create_remote_service_binding(binding(
        &[&models],
        create_loopback_service_transport(provider.clone()),
    ))?;
    let late_models = late_namespace.use_service(&models)?;
    late_namespace.ready(&bg()).await?;
    assert_eq!(revision(&late_models), Some(rev(1)));

    unsubscribe.dispose();
    let (left, right) = futures::join!(namespace.dispose(&bg()), late_namespace.dispose(&bg()));
    left?;
    right?;
    provider.dispose()?;
    Ok(())
}

#[tokio::test]
async fn publishes_compact_tracked_operations_through_the_remote_provider() -> Result<(), BoxError>
{
    let timeline = define_service::<()>("test.timeline")?;
    let provider = RemoteServiceProvider::new([ServiceProviderDefinition::singleton(&timeline)])?;
    let initial = json(j!({ "entries": [{ "id": "one" }], "retained": { "value": 1 } }));
    let source = replicated_state(initial.clone())?;
    provider.provide(&timeline, ServiceObject::new().state("state", &source))?;
    let updates: Recorder<ServiceProviderUpdate> = Recorder::default();
    let raw = provider.subscribe(
        timeline.id(),
        ServiceMode::Singleton,
        record_updates(&updates),
    )?;
    let members = |subscription: &ProviderSubscription| -> Vec<JsonValue> {
        subscription.snapshot().instances[0]
            .members
            .iter()
            .map(ServiceMemberSnapshot::to_json)
            .collect()
    };
    assert_eq!(
        members(&raw),
        vec![json(
            j!({ "name": "state", "kind": "state", "sequence": 0, "ops": [["r", initial]] })
        )]
    );
    raw.activate()?;

    let namespace = create_remote_service_binding(binding(
        &[&timeline],
        create_loopback_service_transport(provider.clone()),
    ))?;
    let handle = namespace.use_service(&timeline)?;
    namespace.ready(&bg()).await?;
    let previous = handle.state_value("state")?;
    let next =
        json(j!({ "entries": [{ "id": "one" }, { "id": "two" }], "retained": { "value": 1 } }));
    source.change(&bg(), |draft| {
        draft
            .child("entries")?
            .push([json(j!({ "id": "two" }))])
            .map(drop)
    })?;

    let recorded = || -> Vec<JsonValue> {
        updates
            .get()
            .iter()
            .map(ServiceProviderUpdate::to_json)
            .collect()
    };
    assert!(recorded().contains(&json(j!({
        "type": "state", "member": "state", "sequence": 1, "ops": [["p", ["entries"], 1, 0, [{ "id": "two" }]]],
    }))));
    assert_eq!(
        previous,
        Some(json(
            j!({ "entries": [{ "id": "one" }], "retained": { "value": 1 } })
        ))
    );
    assert_eq!(handle.state_value("state")?, Some(next));

    source.change(&bg(), |draft| {
        draft
            .child("entries")?
            .push([json(j!({ "id": "three" }))])
            .map(drop)
    })?;
    let late = provider.subscribe(
        timeline.id(),
        ServiceMode::Singleton,
        Arc::new(|_update, _cx| Ok(())),
    )?;
    assert_eq!(
        recorded().last().cloned(),
        Some(json(j!({
            "type": "state", "member": "state", "sequence": 2, "ops": [["p", ["entries"], 2, 0, [{ "id": "three" }]]],
        })))
    );
    assert_eq!(
        members(&late),
        vec![json(j!({
            "name": "state",
            "kind": "state",
            "sequence": 2,
            "ops": [["r", { "entries": [{ "id": "one" }, { "id": "two" }, { "id": "three" }], "retained": { "value": 1 } }]],
        }))]
    );
    late.close();
    raw.close();
    namespace.dispose(&bg()).await?;
    provider.dispose()?;
    Ok(())
}

struct FrozenSource {
    initial: JsonValue,
    publish: Arc<Mutex<Option<SourceFrameListener>>>,
    disposed: Arc<AtomicBool>,
}

struct FrozenAttachment {
    initial: JsonValue,
    publish: Arc<Mutex<Option<SourceFrameListener>>>,
    disposed: Arc<AtomicBool>,
}

impl ReplicatedStateSource for FrozenSource {
    fn attach(&self) -> Result<Box<dyn ReplicatedStateSourceAttachment>, BoxError> {
        Ok(Box::new(FrozenAttachment {
            initial: self.initial.clone(),
            publish: Arc::clone(&self.publish),
            disposed: Arc::clone(&self.disposed),
        }))
    }
}

impl ReplicatedStateSourceAttachment for FrozenAttachment {
    fn snapshot(&self) -> ReplicatedStateSourceSnapshot {
        ReplicatedStateSourceSnapshot {
            value: self.initial.clone(),
            cursor: 20,
        }
    }

    fn activate(&self, listener: SourceFrameListener) -> Result<(), BoxError> {
        *self.publish.lock().unwrap_or_else(PoisonError::into_inner) = Some(listener);
        Ok(())
    }

    fn dispose(&self) -> Result<(), BoxError> {
        self.disposed.store(true, Ordering::SeqCst);
        Ok(())
    }
}

#[test]
fn publishes_authoritative_source_references_through_services_without_re_diffing(
) -> Result<(), BoxError> {
    let timeline = define_service::<()>("test.timeline")?;
    let initial = json(j!({ "entries": [{ "id": "one" }], "retained": { "value": 1 } }));
    let publish: Arc<Mutex<Option<SourceFrameListener>>> = Arc::default();
    let disposed = Arc::new(AtomicBool::new(false));
    let source = FrozenSource {
        initial: initial.clone(),
        publish: Arc::clone(&publish),
        disposed: Arc::clone(&disposed),
    };
    let state = replicated_state_from_source(&source, ReplicatedStateSourceOptions::default())?;
    let provider = RemoteServiceProvider::new([ServiceProviderDefinition::singleton(&timeline)])?;
    provider.provide(&timeline, ServiceObject::new().state("state", &state))?;
    let updates: Recorder<ServiceProviderUpdate> = Recorder::default();
    let subscription = provider.subscribe(
        timeline.id(),
        ServiceMode::Singleton,
        record_updates(&updates),
    )?;
    match &subscription.snapshot().instances[0].members[0] {
        ServiceMemberSnapshot::State { ops, .. } => match &ops[0] {
            Op::Replace(value) => assert!(value.strict_equals(&initial)),
            other => panic!("unexpected op {other:?}"),
        },
        ServiceMemberSnapshot::Method { .. } => panic!("expected a state member"),
    }
    subscription.activate()?;

    let next: JsonValue = [
        ("entries", json(j!([{ "id": "one" }, { "id": "two" }]))),
        ("retained", initial["retained"].clone()),
    ]
    .into_iter()
    .collect::<crate::json::JsonObject>()
    .into();
    let ops: Arc<[Op]> = Arc::from(vec![Op::from_json(&json(
        j!(["p", ["entries"], 1, 0, [{ "id": "two" }]]),
    ))?]);
    let listener = publish
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .unwrap();
    listener(ReplicatedStateSourceFrame {
        cursor: 21,
        value: next,
        ops: Arc::clone(&ops),
        context: bg(),
    });
    let received = updates.get();
    assert_eq!(received.len(), 1);
    match &received[0] {
        ServiceProviderUpdate::State { ops: published, .. } => {
            assert!(Arc::ptr_eq(published, &ops));
        }
        other => panic!("expected a state update, got {}", other.kind()),
    }

    subscription.close();
    provider.dispose()?;
    state.dispose()?;
    assert!(disposed.load(Ordering::SeqCst));
    Ok(())
}

#[tokio::test]
async fn keeps_singleton_facades_stable_when_their_provider_is_replaced() -> Result<(), BoxError> {
    let models = models();
    let provider = RemoteServiceProvider::new([ServiceProviderDefinition::singleton(&models)])?;
    provider.provide(&models, models_object(&models_state(1)))?;
    let namespace = create_remote_service_binding(binding(
        &[&models],
        create_loopback_service_transport(provider.clone()),
    ))?;
    let handle = namespace.use_service(&models)?;
    let state = handle.member("state")?;
    let select = handle.member("select")?;
    namespace.ready(&bg()).await?;
    let state_revision = || {
        state
            .value()
            .unwrap()
            .map(|value| value["revision"].clone())
    };
    assert_eq!(state_revision(), Some(rev(1)));

    provider.withdraw(&models)?;
    assert_eq!(state.value()?, None);
    let error = select
        .call(
            vec![json(j!({ "provider": "test", "modelId": "unavailable" }))],
            &bg(),
        )?
        .await
        .unwrap_err();
    assert_eq!(
        error.remote_service_error().unwrap().code().as_str(),
        "service_not_found"
    );

    let calls = Arc::new(AtomicUsize::new(0));
    let counted = Arc::clone(&calls);
    provider.replace(
        &models,
        ServiceObject::new()
            .state("state", &models_state(2))
            .method("select", move |_args, _cx| {
                counted.fetch_add(1, Ordering::SeqCst);
                async { Ok::<_, BoxError>(None) }
            }),
    )?;

    assert!(namespace.use_service(&models)?.same(&handle));
    assert!(handle.member("state")?.same(&state));
    assert_eq!(state_revision(), Some(rev(2)));
    select
        .call(
            vec![json(j!({ "provider": "test", "modelId": "replacement" }))],
            &bg(),
        )?
        .await?;
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_message(
        provider.replace(&models, noop(ServiceObject::new(), "select")),
        "replacement must preserve its member shape",
    );
    assert_message(
        provider.replace(&models, noop(noop(ServiceObject::new(), "state"), "select")),
        "replacement must preserve its member shape",
    );
    assert_eq!(state_revision(), Some(rev(2)));

    namespace.dispose(&bg()).await?;
    provider.dispose()?;
    Ok(())
}

#[test]
fn delivers_active_subscriber_updates_before_reporting_listener_failures() -> Result<(), BoxError> {
    let models = models();
    let provider = RemoteServiceProvider::new([ServiceProviderDefinition::singleton(&models)])?;
    provider.provide(&models, models_object(&models_state(1)))?;
    let delivered = Arc::new(AtomicUsize::new(0));
    let failing = provider.subscribe(
        models.id(),
        ServiceMode::Singleton,
        Arc::new(|_update, _cx| Err(ChordError::error("listener failed"))),
    )?;
    let counted = Arc::clone(&delivered);
    let succeeding = provider.subscribe(
        models.id(),
        ServiceMode::Singleton,
        Arc::new(move |_update, _cx| {
            counted.fetch_add(1, Ordering::SeqCst);
            Ok(())
        }),
    )?;
    failing.activate()?;
    succeeding.activate()?;

    let error = provider
        .replace(&models, models_object(&models_state(2)))
        .unwrap_err();
    assert_eq!(error.to_string(), "listener failed");
    assert_eq!(delivered.load(Ordering::SeqCst), 1);

    failing.close();
    succeeding.close();
    provider.dispose()?;
    Ok(())
}

#[test]
fn does_not_replay_a_queued_revision_already_covered_by_a_new_subscription_snapshot(
) -> Result<(), BoxError> {
    let models = models();
    let provider = RemoteServiceProvider::new([ServiceProviderDefinition::singleton(&models)])?;
    let state = models_state(0);
    provider.provide(&models, models_object(&state))?;
    let late_updates: Recorder<u64> = Recorder::default();
    let late: Arc<Mutex<Option<ProviderSubscription>>> = Arc::default();
    let (target, slot, record, service, id) = (
        provider.clone(),
        Arc::clone(&late),
        late_updates.clone(),
        state.clone(),
        models.id().to_owned(),
    );
    let first = provider.subscribe(
        models.id(),
        ServiceMode::Singleton,
        Arc::new(move |update, _cx| {
            if !matches!(update, ServiceProviderUpdate::State { sequence: 1, .. }) {
                return Ok(());
            }
            set_revision(&service, 2);
            let record = record.clone();
            let subscription = target.subscribe(
                &id,
                ServiceMode::Singleton,
                Arc::new(move |next, _cx| {
                    if let ServiceProviderUpdate::State { sequence, .. } = next {
                        record.push(sequence);
                    }
                    Ok(())
                }),
            )?;
            let members: Vec<JsonValue> = subscription.snapshot().instances[0]
                .members
                .iter()
                .map(ServiceMemberSnapshot::to_json)
                .collect();
            assert!(members.contains(&json(j!({
                "name": "state", "kind": "state", "sequence": 2, "ops": [["r", { "selected": null, "revision": 2 }]],
            }))));
            subscription.activate()?;
            *slot.lock().unwrap_or_else(PoisonError::into_inner) = Some(subscription);
            Ok(())
        }),
    )?;
    first.activate()?;
    set_revision(&state, 1);
    assert_eq!(late_updates.get(), Vec::<u64>::new());
    set_revision(&state, 3);
    assert_eq!(late_updates.get(), vec![3]);
    if let Some(late) = late.lock().unwrap_or_else(PoisonError::into_inner).take() {
        late.close();
    }
    first.close();
    provider.dispose()?;
    Ok(())
}

#[test]
fn replays_every_buffered_update_before_reporting_listener_failures() -> Result<(), BoxError> {
    let models = models();
    let provider = RemoteServiceProvider::new([ServiceProviderDefinition::singleton(&models)])?;
    let state = models_state(0);
    provider.provide(&models, models_object(&state))?;
    let delivered = Arc::new(AtomicUsize::new(0));
    let counted = Arc::clone(&delivered);
    let subscription = provider.subscribe(
        models.id(),
        ServiceMode::Singleton,
        Arc::new(move |_update, _cx| {
            counted.fetch_add(1, Ordering::SeqCst);
            Err(ChordError::error("listener failed"))
        }),
    )?;
    set_revision(&state, 1);
    set_revision(&state, 2);

    assert_message(
        subscription.activate(),
        "Failed to activate remote service subscription",
    );
    assert_eq!(delivered.load(Ordering::SeqCst), 2);
    subscription.close();
    provider.dispose()?;
    Ok(())
}

#[tokio::test]
async fn clears_retained_facades_when_providers_and_bindings_are_disposed() -> Result<(), BoxError>
{
    let models = models();
    let provider = RemoteServiceProvider::new([ServiceProviderDefinition::singleton(&models)])?;
    provider.provide(&models, models_object(&models_state(1)))?;
    let namespace = create_remote_service_binding(binding(
        &[&models],
        create_loopback_service_transport(provider.clone()),
    ))?;
    let handle = namespace.use_service(&models)?;
    let state = handle.member("state")?;
    namespace.ready(&bg()).await?;
    assert_eq!(revision(&handle), Some(rev(1)));

    provider.dispose()?;
    assert_eq!(state.value()?, None);
    let result = handle
        .call(
            "select",
            vec![json(j!({ "provider": "test", "modelId": "one" }))],
            &bg(),
        )?
        .await;
    assert_message(result, "Remote service provider is disposed");

    namespace.dispose(&bg()).await?;
    assert_message(state.value(), "Remote service binding is disposed");
    Ok(())
}

#[tokio::test]
async fn applies_provider_disposal_buffered_while_subscriptions_are_starting(
) -> Result<(), BoxError> {
    let models = models();
    let dialogs = question_dialogs();
    let provider = RemoteServiceProvider::new([
        ServiceProviderDefinition::singleton(&models),
        ServiceProviderDefinition::keyed(&dialogs),
    ])?;
    provider.provide(&models, models_object(&models_state(1)))?;
    let request = replicated_state(json(j!({ "question": "Pending?" })))?;
    provider.spawn(&dialogs, "pending", dialog_object(&request, true))?;
    let namespace = create_remote_service_binding(binding(
        &[&models, &dialogs],
        create_loopback_service_transport(provider.clone()),
    ))?;
    let handle = namespace.use_service(&models)?;
    let observed: Recorder<ServiceHandle> = Recorder::default();
    let record = observed.clone();
    namespace.observe(
        &dialogs,
        ServiceObserver::new(move |service, _cx| record.push(service)),
    )?;

    provider.dispose()?;
    namespace.ready(&bg()).await?;
    assert_eq!(handle.state_value("state")?, None);
    assert_eq!(observed.len(), 0);

    namespace.dispose(&bg()).await?;
    Ok(())
}

#[tokio::test]
async fn keeps_deferred_service_handles_inaccessible_until_host_activation() -> Result<(), BoxError>
{
    let models = models();
    let provider = RemoteServiceProvider::new([ServiceProviderDefinition::singleton(&models)])?;
    provider.provide(&models, models_object(&models_state(0)))?;
    let active = Arc::new(AtomicBool::new(false));
    let guard = Arc::clone(&active);
    let mut options = binding(
        &[&models],
        create_loopback_service_transport(provider.clone()),
    );
    options.bound = false;
    options.assert_access = Some(Arc::new(move || {
        if guard.load(Ordering::SeqCst) {
            Ok(())
        } else {
            Err(ChordError::error("Service handles are not active"))
        }
    }));
    let namespace = create_remote_service_binding(options)?;
    let handle = namespace.use_service(&models)?;

    assert_message(
        handle.member("state").and_then(|state| state.value()),
        "Service handles are not active",
    );
    assert_message(
        handle
            .member("state")
            .and_then(|state| state.subscribe(StateListener::new(|_value, _cx, _delivery| {}))),
        "Service handles are not active",
    );
    assert_message(
        handle.call(
            "select",
            vec![json(j!({ "provider": "test", "modelId": "one" }))],
            &bg(),
        ),
        "Service handles are not active",
    );

    namespace.rebind(true, &bg()).await?;
    active.store(true, Ordering::SeqCst);
    namespace.ready(&bg()).await?;
    assert_eq!(revision(&handle), Some(rev(0)));

    namespace.dispose(&bg()).await?;
    provider.dispose()?;
    Ok(())
}

/// A transport whose `subscribe` is supplied per test.
type SubscribeFn = dyn Fn(&str, ServiceMode, ServiceUpdateListener) -> Result<Box<dyn ServiceSubscription>, ChordError>
    + Send
    + Sync;

struct CustomTransport {
    invoke: Option<RemoteServiceProvider>,
    subscribe: Box<SubscribeFn>,
}

impl RemoteServiceTransport for CustomTransport {
    fn invoke(&self, call: ServiceCall, context: &Context) -> MethodFuture {
        match &self.invoke {
            Some(provider) => provider.invoke(call, context),
            None => futures::future::ready(Err(ChordError::error("unexpected invocation"))).boxed(),
        }
    }

    fn subscribe(
        &self,
        service_id: &str,
        mode: ServiceMode,
        listener: ServiceUpdateListener,
        _context: &Context,
    ) -> BoxFuture<'static, Result<Box<dyn ServiceSubscription>, ChordError>> {
        futures::future::ready((self.subscribe)(service_id, mode, listener)).boxed()
    }
}

#[tokio::test]
async fn rejects_namespace_readiness_when_initial_hydration_fails() -> Result<(), BoxError> {
    let models = models();
    let (errors, on_error) = errors_recorder();
    let transport = CustomTransport {
        invoke: None,
        subscribe: Box::new(|_id, _mode, _listener| {
            Err(ChordError::error("initial hydration failed"))
        }),
    };
    let mut options = binding(&[&models], Arc::new(transport));
    options.on_error = Some(on_error);
    let namespace = create_remote_service_binding(options)?;
    let handle = namespace.use_service(&models)?;

    let error = namespace.ready(&bg()).await.unwrap_err();
    assert_eq!(error.to_string(), "initial hydration failed");
    assert_eq!(handle.state_value("state")?, None);
    let reported: Vec<String> = errors.get().iter().map(ToString::to_string).collect();
    assert_eq!(reported, vec!["initial hydration failed".to_owned()]);
    namespace.dispose(&bg()).await?;
    Ok(())
}

#[tokio::test]
async fn buffers_state_updates_that_race_subscription_hydration() -> Result<(), BoxError> {
    let models = models();
    let provider = RemoteServiceProvider::new([ServiceProviderDefinition::singleton(&models)])?;
    let state = models_state(0);
    provider.provide(&models, models_object(&state))?;
    let (target, service) = (provider.clone(), state.clone());
    let transport = CustomTransport {
        invoke: Some(provider.clone()),
        subscribe: Box::new(move |id, mode, listener| {
            let subscription = target.subscribe(id, mode, listener)?;
            set_revision(&service, 1);
            Ok(Box::new(subscription) as Box<dyn ServiceSubscription>)
        }),
    };
    let namespace = create_remote_service_binding(binding(&[&models], Arc::new(transport)))?;
    let handle = namespace.use_service(&models)?;
    let revisions: Recorder<JsonValue> = Recorder::default();
    let record = revisions.clone();
    handle.member("state")?.subscribe(StateListener::new(
        move |value: JsonValue, _cx, _delivery| record.push(value["revision"].clone()),
    ))?;

    wait_for(|| revisions.get() == vec![json(j!(0)), json(j!(1))]).await;
    assert_eq!(revision(&handle), Some(rev(1)));
    namespace.dispose(&bg()).await?;
    provider.dispose()?;
    Ok(())
}

struct StaticSubscription {
    snapshot: ServiceSubscriptionSnapshot,
}

impl ServiceSubscription for StaticSubscription {
    fn snapshot(&self) -> &ServiceSubscriptionSnapshot {
        &self.snapshot
    }

    fn activate(&self) -> Result<(), ChordError> {
        Ok(())
    }

    fn close(&self, _context: &Context) -> BoxFuture<'static, Result<(), ChordError>> {
        futures::future::ready(Ok(())).boxed()
    }
}

async fn clears_replicated_state_after_an_operation_sequence(
    sequence: u64,
) -> Result<(), BoxError> {
    let models = models();
    let send_update: Arc<Mutex<Option<ServiceUpdateListener>>> = Arc::default();
    let (errors, on_error) = errors_recorder();
    let slot = Arc::clone(&send_update);
    let transport = CustomTransport {
        invoke: None,
        subscribe: Box::new(move |_id, _mode, listener| {
            *slot.lock().unwrap_or_else(PoisonError::into_inner) = Some(listener);
            let snapshot = parse_service_subscription_snapshot(&json(j!({
                "serviceId": "test.models",
                "mode": "singleton",
                "instances": [{ "members": [
                    { "name": "select", "kind": "method" },
                    { "name": "state", "kind": "state", "sequence": 0, "ops": [["r", { "selected": null, "revision": 0 }]] },
                ] }],
            })))?;
            Ok(Box::new(StaticSubscription { snapshot }) as Box<dyn ServiceSubscription>)
        }),
    };
    let mut options = binding(&[&models], Arc::new(transport));
    options.on_error = Some(on_error);
    let namespace = create_remote_service_binding(options)?;
    let handle = namespace.use_service(&models)?;
    namespace.ready(&bg()).await?;
    assert_eq!(revision(&handle), Some(rev(0)));

    let listener = send_update
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .unwrap();
    // Built directly: the TS test sends an unvalidated update.
    let update = ServiceProviderUpdate::State {
        instance: None,
        member: "state".to_owned(),
        sequence,
        ops: Arc::from(vec![Op::Replace(json(
            j!({ "selected": null, "revision": sequence }),
        ))]),
    };
    // TS ignores the listener's return value.
    drop(listener(update, &bg()));
    assert_eq!(handle.state_value("state")?, None);
    let reported = errors.get();
    assert_eq!(reported.len(), 1);
    assert!(
        reported[0].to_string().contains("sequence has a gap"),
        "{}",
        reported[0]
    );
    namespace.dispose(&bg()).await?;
    Ok(())
}

#[tokio::test]
async fn clears_replicated_state_after_a_duplicate_operation_sequence() -> Result<(), BoxError> {
    clears_replicated_state_after_an_operation_sequence(0).await
}

#[tokio::test]
async fn clears_replicated_state_after_a_gap_operation_sequence() -> Result<(), BoxError> {
    clears_replicated_state_after_an_operation_sequence(2).await
}

#[tokio::test]
async fn hydrates_cold_replicated_state_replicas_and_replaces_them_across_rebinds(
) -> Result<(), BoxError> {
    let models = models();
    let provider = RemoteServiceProvider::new([ServiceProviderDefinition::singleton(&models)])?;
    let state = models_state(0);
    provider.provide(&models, models_object(&state))?;
    let mut options = binding(
        &[&models],
        create_loopback_service_transport(provider.clone()),
    );
    options.bound = false;
    let namespace = create_remote_service_binding(options)?;
    let handle = namespace.use_service(&models)?;
    let revisions: Recorder<JsonValue> = Recorder::default();
    let record = revisions.clone();
    handle.member("state")?.subscribe(StateListener::new(
        move |value: JsonValue, _cx, _delivery| record.push(value["revision"].clone()),
    ))?;
    let seen = || -> Vec<JsonValue> { revisions.get() };
    let list =
        |values: &[i64]| -> Vec<JsonValue> { values.iter().map(|value| json(j!(value))).collect() };
    assert_eq!(handle.state_value("state")?, None);
    assert_eq!(seen(), list(&[]));

    set_revision(&state, 1);
    namespace.rebind(true, &bg()).await?;
    assert_eq!(revision(&handle), Some(rev(1)));
    assert_eq!(seen(), list(&[1]));
    set_revision(&state, 2);
    assert_eq!(seen(), list(&[1, 2]));

    namespace.rebind(false, &bg()).await?;
    assert_eq!(handle.state_value("state")?, None);
    set_revision(&state, 3);
    assert_eq!(seen(), list(&[1, 2]));
    namespace.rebind(true, &bg()).await?;
    assert_eq!(revision(&handle), Some(rev(3)));
    assert_eq!(seen(), list(&[1, 2, 3]));

    namespace.dispose(&bg()).await?;
    provider.dispose()?;
    Ok(())
}

#[derive(Clone)]
struct Observation {
    question: Option<JsonValue>,
    service: ServiceHandle,
    context: Context,
}

#[tokio::test]
async fn hydrates_keyed_state_before_observe_handlers_and_fences_reused_keys(
) -> Result<(), BoxError> {
    let dialogs = question_dialogs();
    let provider = RemoteServiceProvider::new([ServiceProviderDefinition::keyed(&dialogs)])?;
    assert_eq!(
        crate::catalogue_json(provider.catalogue()),
        json(j!([{ "serviceId": "test.question-dialog", "mode": "keyed" }]))
    );
    let transport = create_loopback_service_transport(provider.clone());
    let (errors, on_error) = errors_recorder();
    let mut options = binding(&[&dialogs], transport);
    options.on_error = Some(on_error);
    let namespace = create_remote_service_binding(options)?;
    let observed: Recorder<Observation> = Recorder::default();
    let record = observed.clone();
    let stop = namespace.observe(
        &dialogs,
        ServiceObserver::new(move |service: ServiceHandle, context| {
            record.push(Observation {
                question: service.state_value("request").unwrap(),
                service,
                context,
            });
        }),
    )?;
    wait_for(|| errors.len() == 0).await;

    let first_request = replicated_state(json(j!({ "question": "First?" })))?;
    let first_submit: Recorder<(Vec<JsonValue>, Context)> = Recorder::default();
    let submits = first_submit.clone();
    let close_first = provider.spawn(
        &dialogs,
        "invocation-1",
        ServiceObject::new()
            .state("request", &first_request)
            .method("submit", move |args, cx| {
                submits.push((args, cx));
                async { Ok::<_, BoxError>(Some(json(j!({ "accepted": true })))) }
            }),
    )?;
    wait_for(|| observed.len() == 1).await;
    assert_eq!(
        observed.get()[0].question,
        Some(json(j!({ "question": "First?" })))
    );

    let first_service = observed.get()[0].service.clone();
    first_request.change(&bg(), |draft| draft.set("question", "Updated?").map(drop))?;
    assert_eq!(
        first_service.state_value("request")?,
        Some(json(j!({ "question": "Updated?" })))
    );
    let result = first_service
        .call("submit", vec![json(j!("yes"))], &bg())?
        .await?;
    assert_eq!(result, Some(json(j!({ "accepted": true }))));
    let calls = first_submit.get();
    assert_eq!(calls.len(), 1);
    assert_eq!(calls[0].0, vec![json(j!("yes"))]);
    assert!(calls[0].1.abort_signal().is_none());

    let retained_first_submit = first_service.member("submit")?;
    close_first.close()?;
    assert!(observed.get()[0].context.aborted());
    assert_message(
        first_service.state_value("request"),
        "observation is closed",
    );
    assert_message(
        retained_first_submit.call(vec![json(j!("late"))], &bg()),
        "observation is closed",
    );

    let second_request = replicated_state(json(j!({ "question": "Again?" })))?;
    let close_second = provider.spawn(
        &dialogs,
        "invocation-1",
        dialog_object(&second_request, false),
    )?;
    wait_for(|| observed.len() == 2).await;
    assert_eq!(
        observed.get()[1].question,
        Some(json(j!({ "question": "Again?" })))
    );
    assert!(!observed.get()[1].service.same(&first_service));
    assert_eq!(errors.len(), 0);

    let second_service = observed.get()[1].service.clone();
    let retained_second_submit = second_service.member("submit")?;
    stop.dispose();
    assert!(observed.get()[1].context.aborted());
    assert_message(
        second_service.state_value("request"),
        "observation is closed",
    );
    assert_message(
        retained_second_submit.call(vec![json(j!("late"))], &bg()),
        "observation is closed",
    );
    close_second.close()?;
    namespace.dispose(&bg()).await?;
    provider.dispose()?;
    Ok(())
}

#[test]
fn rejects_mode_mixing_and_unsupported_members() -> Result<(), BoxError> {
    let models = models();
    let dialogs = question_dialogs();
    let provider = RemoteServiceProvider::new([
        ServiceProviderDefinition::singleton(&models),
        ServiceProviderDefinition::keyed(&dialogs),
    ])?;
    provider.provide(&models, models_object(&models_state(0)))?;
    assert_message(
        provider.spawn(&models, "wrong", ServiceObject::new()),
        "singleton",
    );
    assert_message(
        provider.spawn(
            &dialogs,
            "invalid",
            ServiceObject::new()
                .value("request", json(j!("2026-10-06T00:00:00.000Z")))
                .method("submit", |_args, _cx| async {
                    Ok::<_, BoxError>(Some(json(j!({ "accepted": true }))))
                }),
        ),
        "not remotely exposable",
    );
    provider.dispose()?;
    Ok(())
}
