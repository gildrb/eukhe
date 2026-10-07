//! Port of `test/facets.test.ts`.
//!
//! Deviations:
//! - "rejects missing dependencies, cycles, and asynchronous setup": the
//!   asynchronous-setup case is not ported; a Rust facet setup returns
//!   `Result<(), E>`, so an asynchronous setup does not compile.
//! - "provides arbitrary host services through the facet graph": the
//!   `expect(hostValues).not.toBe(values)` check is omitted; a Rust service
//!   handle and the typed implementation are distinct types, so identity
//!   cannot coincide.
//! - Remote implementations are described `ServiceObject`s; process-local
//!   implementations are typed values read through `ServiceHandle::get`, whose
//!   errors are the TS property-access throws.

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use futures::future::BoxFuture;
use futures::FutureExt;
use serde_json::json as j;

use super::{json, wait_for, Recorder};
use crate::context::{Context, BACKGROUND_CONTEXT};
use crate::error::{BoxError, ChordError};
use crate::services::loopback::create_loopback_service_transport;
use crate::types::{ServiceCatalogueEntry, ServiceMode, ServiceToken, StateListener};
use crate::{
    create_facet_host, create_remote_service_binding, define_facet, define_local_service,
    define_service, FacetOptions, MutableReplicatedState, Outcome, RemoteServiceBinding,
    RemoteServiceBindingOptions, RemoteServiceProvider, RemoteServiceSource,
    RemoteServiceSourceOpenOptions, RemoteServices, Service, ServiceHandle, ServiceImplementation,
    ServiceObject, ServiceObserver, ServiceProviderDefinition, ServiceProviderUpdate,
};

type Step = Result<(), BoxError>;

fn bg() -> Context {
    BACKGROUND_CONTEXT.clone()
}

/// Typed `HostValues` (`use` is a Rust keyword).
#[derive(Clone)]
struct HostValues {
    name: String,
    use_: String,
}

/// Typed `LocalKeyedValue`.
#[derive(Clone)]
struct LocalKeyedValue {
    metadata: HashMap<String, String>,
    value: String,
}

impl LocalKeyedValue {
    fn read(&self) -> String {
        self.value.clone()
    }
}

fn source_service() -> Service<()> {
    define_service("test.experimental.source").unwrap()
}
fn projection_service() -> Service<()> {
    define_service("test.experimental.projection").unwrap()
}
fn keyed_value() -> Service<()> {
    define_service("test.experimental.keyed-value").unwrap()
}
fn watched_service() -> Service<()> {
    define_service("test.experimental.watched").unwrap()
}
fn host_values() -> Service<HostValues> {
    define_local_service("test.experimental.host-values").unwrap()
}
fn local_keyed_value() -> Service<LocalKeyedValue> {
    define_local_service("test.experimental.local-keyed-value").unwrap()
}
fn left_value() -> Service<()> {
    define_service("test.experimental.left-value").unwrap()
}
fn right_value() -> Service<()> {
    define_service("test.experimental.right-value").unwrap()
}
fn combined_value() -> Service<()> {
    define_service("test.experimental.combined-value").unwrap()
}

fn reader(value: &str) -> ServiceObject {
    let value = value.to_owned();
    ServiceObject::new().method("read", move |_args, _cx| {
        let value = value.clone();
        async move { Ok::<_, BoxError>(Some(json(j!(value)))) }
    })
}

fn text(value: Option<crate::JsonValue>) -> String {
    value
        .and_then(|value| value.as_str().map(str::to_owned))
        .unwrap_or_default()
}

async fn read(handle: &ServiceHandle, cx: &Context) -> Result<String, ChordError> {
    Ok(text(handle.call("read", vec![], cx)?.await?))
}

fn sync_error<T>(result: Result<T, ChordError>) -> String {
    match result {
        Ok(_) => panic!("expected a synchronous error"),
        Err(error) => error.to_string(),
    }
}

#[tokio::test]
async fn discovers_setup_dependencies_before_connecting_stable_service_handles() -> Step {
    let trace = Recorder::default();
    let source_handle: Recorder<ServiceHandle> = Recorder::default();
    let projection = {
        let trace = trace.clone();
        let source_handle = source_handle.clone();
        define_facet("projection", move |env| -> Step {
            trace.push("setup projection".to_owned());
            let handle = env.use_service(&source_service())?;
            source_handle.push(handle.clone());
            assert_eq!(
                sync_error(handle.call("read", vec![], &bg())),
                "Facet projection service handles cannot be used while setting_up"
            );
            env.provide(
                &projection_service(),
                ServiceObject::new().method("read", move |_args, cx| {
                    let handle = handle.clone();
                    async move { handle.call("read", vec![], &cx)?.await }
                }),
            )?;
            let activate = trace.clone();
            env.on_activate(move || activate.push("activate projection".to_owned()))?;
            let deactivate = trace.clone();
            env.on_deactivate(move || deactivate.push("dispose projection".to_owned()))?;
            Ok(())
        })
    };
    let source = {
        let trace = trace.clone();
        define_facet("source", move |env| -> Step {
            trace.push("setup source".to_owned());
            env.provide(&source_service(), reader("value"))?;
            let activate = trace.clone();
            env.on_activate(move || activate.push("activate source".to_owned()))?;
            let deactivate = trace.clone();
            env.on_deactivate(move || deactivate.push("dispose source".to_owned()))?;
            Ok(())
        })
    };
    let host = create_facet_host(FacetOptions {
        facets: vec![projection, source],
        ..Default::default()
    })
    .await?;

    assert_eq!(
        trace.get(),
        [
            "setup projection",
            "setup source",
            "activate source",
            "activate projection"
        ]
    );
    assert_eq!(read(&source_handle.get()[0], &bg()).await?, "value");
    let projection = host.services().use_service(&projection_service())?;
    assert_eq!(
        text(projection.invoke("read", vec![], &bg()).await?),
        "value"
    );

    host.dispose().await?;
    assert_eq!(
        trace.get()[trace.len() - 2..],
        ["dispose projection", "dispose source"]
    );
    Ok(())
}

#[tokio::test]
async fn connects_keyed_observations_only_when_the_observing_facet_activates() -> Step {
    let trace = Recorder::default();
    let observer = {
        let trace = trace.clone();
        define_facet("observer", move |env| -> Step {
            let observed = trace.clone();
            env.observe(
                &keyed_value(),
                ServiceObserver::new(move |service, cx| {
                    let observed = observed.clone();
                    Outcome::pending(async move {
                        let value = read(&service, &cx).await?;
                        observed.push(format!("observe {value}"));
                        Ok::<(), ChordError>(())
                    })
                }),
            )?;
            let activate = trace.clone();
            env.on_activate(move || activate.push("activate observer".to_owned()))?;
            Ok(())
        })
    };
    let provider = {
        let trace = trace.clone();
        define_facet("provider", move |env| -> Step {
            let values = env.provide_many(&keyed_value())?;
            let activate = trace.clone();
            env.on_activate(move || -> Result<(), ChordError> {
                activate.push("activate provider".to_owned());
                values.spawn("one", reader("one"))?;
                Ok(())
            })?;
            Ok(())
        })
    };
    let host = create_facet_host(FacetOptions {
        facets: vec![observer, provider],
        ..Default::default()
    })
    .await?;
    wait_for(|| trace.get().iter().any(|entry| entry == "observe one")).await;

    assert_eq!(
        trace.get(),
        ["activate provider", "activate observer", "observe one"]
    );
    let remote_services = create_remote_service_binding(RemoteServiceBindingOptions::new(
        vec![keyed_value().id().to_owned()],
        create_loopback_service_transport(host.services().clone()),
    ))?;
    let remote_values = Recorder::default();
    let record = remote_values.clone();
    remote_services.observe(
        &keyed_value(),
        ServiceObserver::new(move |service, cx| {
            let record = record.clone();
            Outcome::pending(async move {
                record.push(read(&service, &cx).await?);
                Ok::<(), ChordError>(())
            })
        }),
    )?;
    remote_services.ready(&bg()).await?;
    wait_for(|| remote_values.get() == ["one"]).await;

    remote_services.dispose(&bg()).await?;
    host.dispose().await?;
    Ok(())
}

fn keyed_provider(id: &str, value: &'static str) -> Arc<dyn crate::Facet> {
    define_facet(id, move |env| -> Step {
        let values = env.provide_many(&keyed_value())?;
        env.on_activate(move || -> Result<(), ChordError> {
            values.spawn("current", reader(value))?;
            Ok(())
        })?;
        Ok(())
    })
}

#[tokio::test]
async fn routes_remotely_exposable_keyed_services_through_the_host_provider() -> Step {
    let observed: Recorder<(ServiceHandle, Context)> = Recorder::default();
    let consumer = {
        let observed = observed.clone();
        define_facet("remote-keyed-consumer", move |env| -> Step {
            let observed = observed.clone();
            env.observe(
                &keyed_value(),
                ServiceObserver::new(move |service, cx| observed.push((service, cx))),
            )?;
            Ok(())
        })
    };
    let host = create_facet_host(FacetOptions {
        facets: vec![consumer, keyed_provider("remote-keyed-provider", "A")],
        ..Default::default()
    })
    .await?;
    wait_for(|| observed.len() == 1).await;
    let (first_service, first_context) = observed.get()[0].clone();
    assert_eq!(read(&first_service, &first_context).await?, "A");

    host.reload(vec![keyed_provider("remote-keyed-provider", "B")])
        .await?;
    wait_for(|| observed.len() == 2).await;
    assert!(first_context.aborted());
    let error = sync_error(first_service.call("read", vec![], &first_context));
    assert!(error.contains("observation is closed"), "{error}");
    let (second_service, second_context) = observed.get()[1].clone();
    assert_eq!(read(&second_service, &second_context).await?, "B");

    host.dispose().await?;
    assert!(second_context.aborted());
    Ok(())
}

fn failing_keyed_publication(
    kind: &'static str,
    message: &'static str,
) -> crate::types::ServiceUpdateListener {
    Arc::new(
        move |update: ServiceProviderUpdate, _cx: &Context| -> Result<(), ChordError> {
            if update.kind() == kind {
                return Err(ChordError::error(message));
            }
            Ok(())
        },
    )
}

#[tokio::test]
async fn terminates_the_host_when_keyed_replacement_publication_fails() -> Step {
    let host = create_facet_host(FacetOptions {
        facets: vec![keyed_provider("failing-keyed-provider", "A")],
        ..Default::default()
    })
    .await?;
    let subscription = host.services().subscribe(
        keyed_value().id(),
        ServiceMode::Keyed,
        failing_keyed_publication("spawned", "spawn publication failed"),
    )?;
    subscription.activate()?;

    let error = host
        .reload(vec![keyed_provider("failing-keyed-provider", "B")])
        .await
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("Facet reload failed after cutover"),
        "{error}"
    );
    let error = host.reload(vec![]).await.unwrap_err();
    assert!(
        error
            .to_string()
            .contains("Facet host cannot reload while dead"),
        "{error}"
    );
    let error = sync_error(host.services().use_service(&keyed_value()));
    assert!(
        error.contains("Remote service provider is disposed"),
        "{error}"
    );
    host.dispose().await?;
    Ok(())
}

#[tokio::test]
async fn terminates_the_host_when_keyed_retirement_publication_fails() -> Step {
    let host = create_facet_host(FacetOptions {
        facets: vec![keyed_provider("failing-keyed-retirement-provider", "A")],
        ..Default::default()
    })
    .await?;
    let subscription = host.services().subscribe(
        keyed_value().id(),
        ServiceMode::Keyed,
        failing_keyed_publication("closed", "close publication failed"),
    )?;
    subscription.activate()?;

    let error = host
        .reload(vec![keyed_provider(
            "failing-keyed-retirement-provider",
            "B",
        )])
        .await
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("Facet reload failed after cutover"),
        "{error}"
    );
    let error = host.reload(vec![]).await.unwrap_err();
    assert!(
        error
            .to_string()
            .contains("Facet host cannot reload while dead"),
        "{error}"
    );
    host.dispose().await?;
    Ok(())
}

#[tokio::test]
async fn keeps_unrestricted_local_keyed_services_process_local_across_provider_reloads() -> Step {
    let observed: Recorder<(ServiceHandle, Context)> = Recorder::default();
    let consumer = {
        let observed = observed.clone();
        define_facet("local-keyed-consumer", move |env| -> Step {
            let observed = observed.clone();
            env.observe(
                &local_keyed_value(),
                ServiceObserver::new(move |service, cx| observed.push((service, cx))),
            )?;
            Ok(())
        })
    };
    let provider = |value: &'static str| {
        define_facet("local-keyed-provider", move |env| -> Step {
            let values = env.provide_many(&local_keyed_value())?;
            env.on_activate(move || -> Result<(), ChordError> {
                values.spawn(
                    "current",
                    ServiceImplementation::Local(LocalKeyedValue {
                        metadata: HashMap::from([("value".to_owned(), value.to_owned())]),
                        value: value.to_owned(),
                    }),
                )?;
                Ok(())
            })?;
            Ok(())
        })
    };
    let host = create_facet_host(FacetOptions {
        facets: vec![consumer, provider("A")],
        ..Default::default()
    })
    .await?;
    wait_for(|| observed.len() == 1).await;
    let (first_service, first_context) = observed.get()[0].clone();
    assert_eq!(first_service.get::<LocalKeyedValue>()?.read(), "A");
    assert_eq!(
        first_service
            .get::<LocalKeyedValue>()?
            .metadata
            .get("value")
            .map(String::as_str),
        Some("A")
    );
    assert!(!host
        .services()
        .catalogue()
        .iter()
        .any(|entry| entry.service_id == local_keyed_value().id()
            && entry.mode == ServiceMode::Keyed));
    let error = sync_error(host.services().use_service(&local_keyed_value()));
    assert!(error.contains("process-local"), "{error}");

    host.reload(vec![provider("B")]).await?;
    wait_for(|| observed.len() == 2).await;
    assert!(first_context.aborted());
    let error = sync_error(first_service.get::<LocalKeyedValue>());
    assert!(
        error.contains(&format!(
            "Keyed service {} observation is closed",
            local_keyed_value().id()
        )),
        "{error}"
    );
    let (second_service, second_context) = observed.get()[1].clone();
    assert_eq!(second_service.get::<LocalKeyedValue>()?.read(), "B");
    assert_eq!(
        second_service
            .get::<LocalKeyedValue>()?
            .metadata
            .get("value")
            .map(String::as_str),
        Some("B")
    );

    host.dispose().await?;
    assert!(second_context.aborted());
    Ok(())
}

fn state_value(value: &crate::JsonValue) -> i64 {
    value["value"].as_f64().map_or(-1, |number| {
        #[allow(clippy::cast_possible_truncation)] // test values are small integers
        let number = number as i64;
        number
    })
}

#[tokio::test]
async fn keeps_remotely_exposable_local_state_replicas_stable_across_provider_reloads() -> Step {
    let sources: Recorder<MutableReplicatedState> = Recorder::default();
    let revisions: Recorder<i64> = Recorder::default();
    let watched: Recorder<ServiceHandle> = Recorder::default();
    let consumer = {
        let revisions = revisions.clone();
        let watched = watched.clone();
        define_facet("state-consumer", move |env| -> Step {
            let handle = env.use_service(&watched_service())?;
            watched.push(handle.clone());
            let owner = env.clone();
            let revisions = revisions.clone();
            env.on_activate(move || -> Result<(), ChordError> {
                let revisions = revisions.clone();
                let disposer = handle.member("state")?.subscribe(StateListener::new(
                    move |value: crate::JsonValue, _cx: Context, _delivery| {
                        revisions.push(state_value(&value));
                    },
                ))?;
                owner.own_disposer(disposer)
            })?;
            Ok(())
        })
    };
    let provider = |value: i64| {
        let sources = sources.clone();
        define_facet("state-provider", move |env| -> Step {
            let state = env.replicated_state(json(j!({ "value": value })))?;
            sources.push(state.clone());
            env.provide(
                &watched_service(),
                ServiceObject::new().state("state", &state),
            )?;
            Ok(())
        })
    };
    let host = create_facet_host(FacetOptions {
        facets: vec![consumer, provider(1)],
        ..Default::default()
    })
    .await?;
    let handle = watched.get()[0].clone();
    let retained_state = handle.member("state")?;
    assert_eq!(retained_state.value()?, Some(json(j!({ "value": 1 }))));
    assert_eq!(revisions.get(), [1]);

    host.reload(vec![provider(2)]).await?;
    assert!(handle.member("state")?.same(&retained_state));
    assert_eq!(retained_state.value()?, Some(json(j!({ "value": 2 }))));
    assert_eq!(revisions.get(), [1, 2]);
    sources.get()[0].change(&bg(), |draft| draft.set("value", 3))?;
    assert_eq!(retained_state.value()?, Some(json(j!({ "value": 2 }))));
    assert_eq!(revisions.get(), [1, 2]);

    host.dispose().await?;
    assert_eq!(
        sync_error(retained_state.value()),
        "Facet state-consumer service handles cannot be used while dead"
    );
    Ok(())
}

#[tokio::test]
async fn scopes_singleton_service_views_to_each_facet_lifecycle() -> Step {
    let consumer_handles: Recorder<ServiceHandle> = Recorder::default();
    let cleanup_values = Recorder::default();
    let peer_handle: Recorder<ServiceHandle> = Recorder::default();
    let consumer = |generation: &'static str| {
        let consumer_handles = consumer_handles.clone();
        let cleanup_values = cleanup_values.clone();
        define_facet("scoped-consumer", move |env| -> Step {
            let source = env.use_service(&source_service())?;
            assert!(env.use_service(&source_service())?.same(&source));
            consumer_handles.push(source.clone());
            assert_eq!(
                sync_error(source.call("read", vec![], &bg())),
                "Facet scoped-consumer service handles cannot be used while setting_up"
            );
            let cleanup_values = cleanup_values.clone();
            env.on_deactivate(move || {
                Outcome::pending(async move {
                    let value = read(&source, &bg()).await?;
                    cleanup_values.push(format!("{generation}:{value}"));
                    Ok::<(), ChordError>(())
                })
            })?;
            Ok(())
        })
    };
    let peer = {
        let peer_handle = peer_handle.clone();
        define_facet("peer-consumer", move |env| -> Step {
            peer_handle.push(env.use_service(&source_service())?);
            Ok(())
        })
    };
    let provider = define_facet("scoped-provider", |env| -> Step {
        env.provide(&source_service(), reader("value"))?;
        Ok(())
    });
    let host = create_facet_host(FacetOptions {
        facets: vec![consumer("A"), peer, provider],
        ..Default::default()
    })
    .await?;
    let peer_handle = peer_handle.get()[0].clone();
    assert!(!consumer_handles.get()[0].same(&peer_handle));
    let retained_old_read = consumer_handles.get()[0].member("read")?;

    host.reload(vec![consumer("B")]).await?;
    assert_eq!(cleanup_values.get(), ["A:value"]);
    let handles = consumer_handles.get();
    assert!(!handles[1].same(&handles[0]));
    assert_eq!(
        sync_error(handles[0].call("read", vec![], &bg())),
        "Facet scoped-consumer service handles cannot be used while dead"
    );
    assert_eq!(
        sync_error(retained_old_read.call(vec![], &bg())),
        "Facet scoped-consumer service handles cannot be used while dead"
    );
    assert_eq!(read(&handles[1], &bg()).await?, "value");
    assert_eq!(read(&peer_handle, &bg()).await?, "value");

    host.dispose().await?;
    assert_eq!(cleanup_values.get(), ["A:value", "B:value"]);
    assert_eq!(
        sync_error(handles[1].call("read", vec![], &bg())),
        "Facet scoped-consumer service handles cannot be used while dead"
    );
    assert_eq!(
        sync_error(peer_handle.call("read", vec![], &bg())),
        "Facet peer-consumer service handles cannot be used while dead"
    );
    Ok(())
}

#[tokio::test]
async fn owns_resources_registered_during_activation() -> Step {
    let state: Recorder<MutableReplicatedState> = Recorder::default();
    let deliveries = Arc::new(AtomicUsize::new(0));
    let consumer = {
        let deliveries = Arc::clone(&deliveries);
        define_facet("consumer", move |env| -> Step {
            let watched = env.use_service(&watched_service())?;
            let owner = env.clone();
            let deliveries = Arc::clone(&deliveries);
            env.on_activate(move || -> Result<(), ChordError> {
                let disposer = watched.member("state")?.subscribe(StateListener::new(
                    move |_value: crate::JsonValue, _cx: Context, _delivery| {
                        deliveries.fetch_add(1, Ordering::SeqCst);
                    },
                ))?;
                owner.own_disposer(disposer)
            })?;
            Ok(())
        })
    };
    let provider = {
        let state = state.clone();
        define_facet("provider", move |env| -> Step {
            let value = env.replicated_state(json(j!({ "value": 0 })))?;
            state.push(value.clone());
            env.provide(
                &watched_service(),
                ServiceObject::new().state("state", &value),
            )?;
            Ok(())
        })
    };
    let host = create_facet_host(FacetOptions {
        facets: vec![consumer, provider],
        ..Default::default()
    })
    .await?;
    let state = state.get()[0].clone();
    assert_eq!(deliveries.load(Ordering::SeqCst), 1);
    state.change(&bg(), |draft| draft.set("value", 1))?;
    assert_eq!(deliveries.load(Ordering::SeqCst), 2);

    host.dispose().await?;
    state.change(&bg(), |draft| draft.set("value", 2))?;
    assert_eq!(deliveries.load(Ordering::SeqCst), 2);
    Ok(())
}

#[tokio::test]
async fn provides_arbitrary_host_services_through_the_facet_graph() -> Step {
    let values = HostValues {
        name: "session".to_owned(),
        use_: "host value".to_owned(),
    };
    let activated = Arc::new(AtomicUsize::new(0));
    let consumer = {
        let activated = Arc::clone(&activated);
        define_facet("host-service-consumer", move |env| -> Step {
            let handle = env.use_service(&host_values())?;
            assert_eq!(
                sync_error(handle.get::<HostValues>()),
                "Facet host-service-consumer service handles cannot be used while setting_up"
            );
            let activated = Arc::clone(&activated);
            env.on_activate(move || -> Result<(), ChordError> {
                let resolved = handle.get::<HostValues>()?;
                assert_eq!(resolved.name, "session");
                assert_eq!(resolved.use_, "host value");
                activated.fetch_add(1, Ordering::SeqCst);
                Ok(())
            })?;
            Ok(())
        })
    };
    let provider = define_facet("host-service-provider", move |env| -> Step {
        env.provide(&host_values(), ServiceImplementation::Local(values.clone()))?;
        Ok(())
    });
    let host = create_facet_host(FacetOptions {
        facets: vec![consumer, provider],
        ..Default::default()
    })
    .await?;
    assert_eq!(activated.load(Ordering::SeqCst), 1);
    assert_eq!(
        sync_error(host.services().use_service(&host_values())),
        "Service test.experimental.host-values is process-local"
    );
    host.dispose().await?;
    Ok(())
}

/// A binding whose `ready` binds it first (TS `Object.assign(namespace, { ready })`).
struct RebindingServices {
    binding: RemoteServiceBinding,
    disposed: Option<Arc<AtomicUsize>>,
}

impl RemoteServices for RebindingServices {
    fn use_service(&self, service: &ServiceToken) -> Result<ServiceHandle, ChordError> {
        self.binding.use_service(service)
    }

    fn observe(
        &self,
        service: &ServiceToken,
        handler: ServiceObserver,
    ) -> Result<crate::Disposer, ChordError> {
        self.binding.observe(service, handler)
    }

    fn ready(&self, context: &Context) -> BoxFuture<'static, Result<(), ChordError>> {
        let binding = self.binding.clone();
        let context = context.clone();
        async move {
            binding.rebind(true, &context).await?;
            binding.ready(&context).await
        }
        .boxed()
    }

    fn dispose(&self, context: &Context) -> BoxFuture<'static, Result<(), ChordError>> {
        if let Some(disposed) = &self.disposed {
            disposed.fetch_add(1, Ordering::SeqCst);
        }
        self.binding.dispose(context).boxed()
    }
}

/// A source over one pre-built binding (`open` returns it).
struct NamespaceSource {
    binding: RemoteServiceBinding,
    provider: RemoteServiceProvider,
}

impl RemoteServiceSource for NamespaceSource {
    fn accepts_unavailable_services(&self) -> bool {
        false
    }

    fn catalogue(
        &self,
        _cx: &Context,
    ) -> BoxFuture<'static, Result<Vec<ServiceCatalogueEntry>, ChordError>> {
        futures::future::ready(Ok(self.provider.catalogue().to_vec())).boxed()
    }

    fn open(
        &self,
        _options: RemoteServiceSourceOpenOptions,
    ) -> Result<Arc<dyn RemoteServices>, ChordError> {
        Ok(Arc::new(RebindingServices {
            binding: self.binding.clone(),
            disposed: None,
        }))
    }
}

fn unbound_binding(
    service: &Service<()>,
    provider: &RemoteServiceProvider,
) -> Result<RemoteServiceBinding, ChordError> {
    let mut options = RemoteServiceBindingOptions::new(
        vec![service.id().to_owned()],
        create_loopback_service_transport(provider.clone()),
    );
    options.bound = false;
    create_remote_service_binding(options)
}

fn provider_of(service: &Service<()>, value: &str) -> Result<RemoteServiceProvider, ChordError> {
    let provider = RemoteServiceProvider::new([ServiceProviderDefinition::singleton(service)])?;
    provider.provide(service, reader(value))?;
    Ok(provider)
}

#[tokio::test]
async fn combines_connected_services_and_facet_provided_services_in_one_host() -> Step {
    let left_provider = provider_of(&left_value(), "left")?;
    let right_provider = provider_of(&right_value(), "right")?;
    let left_namespace = unbound_binding(&left_value(), &left_provider)?;
    let right_namespace = unbound_binding(&right_value(), &right_provider)?;
    let service_sources: Vec<Arc<dyn RemoteServiceSource>> = vec![
        Arc::new(NamespaceSource {
            binding: left_namespace.clone(),
            provider: left_provider.clone(),
        }),
        Arc::new(NamespaceSource {
            binding: right_namespace.clone(),
            provider: right_provider.clone(),
        }),
    ];
    let facet = define_facet("combined", |env| -> Step {
        let left = env.use_service(&left_value())?;
        let right = env.use_service(&right_value())?;
        env.provide(
            &combined_value(),
            ServiceObject::new().method("read", move |_args, cx| {
                let left = left.clone();
                let right = right.clone();
                async move {
                    let left = read(&left, &cx).await?;
                    let right = read(&right, &cx).await?;
                    Ok::<_, ChordError>(Some(json(j!(format!("{left} {right}")))))
                }
            }),
        )?;
        Ok(())
    });

    let host = create_facet_host(FacetOptions {
        facets: vec![facet],
        service_sources,
        ..Default::default()
    })
    .await?;
    let combined = host.services().use_service(&combined_value())?;
    assert_eq!(
        text(combined.invoke("read", vec![], &bg()).await?),
        "left right"
    );

    host.dispose().await?;
    let (left, right) = futures::join!(
        left_namespace.dispose(&bg()),
        right_namespace.dispose(&bg())
    );
    left?;
    right?;
    left_provider.dispose()?;
    right_provider.dispose()?;
    Ok(())
}

struct DuplicateSource;

impl RemoteServiceSource for DuplicateSource {
    fn accepts_unavailable_services(&self) -> bool {
        false
    }

    fn catalogue(
        &self,
        _cx: &Context,
    ) -> BoxFuture<'static, Result<Vec<ServiceCatalogueEntry>, ChordError>> {
        let entry = ServiceCatalogueEntry {
            service_id: left_value().id().to_owned(),
            mode: ServiceMode::Singleton,
        };
        futures::future::ready(Ok(vec![entry])).boxed()
    }

    fn open(
        &self,
        _options: RemoteServiceSourceOpenOptions,
    ) -> Result<Arc<dyn RemoteServices>, ChordError> {
        Err(ChordError::error("Ambiguous sources must not open"))
    }
}

#[tokio::test]
async fn rejects_a_service_offered_by_multiple_sources() {
    let duplicate: Arc<dyn RemoteServiceSource> = Arc::new(DuplicateSource);
    let consumer = define_facet("duplicate-consumer", |env| -> Step {
        env.use_service(&left_value())?;
        Ok(())
    });
    let error = create_facet_host(FacetOptions {
        facets: vec![consumer],
        service_sources: vec![Arc::clone(&duplicate), duplicate],
        ..Default::default()
    })
    .await
    .unwrap_err();
    let expected = format!(
        "Facet host service {} is offered by more than one source",
        left_value().id()
    );
    assert!(error.to_string().contains(&expected), "{error}");
}

/// A source opening a fresh binding over the current provider.
struct ReopeningSource {
    current: Arc<Mutex<RemoteServiceProvider>>,
    opened: Arc<AtomicUsize>,
    disposed: Arc<AtomicUsize>,
}

impl RemoteServiceSource for ReopeningSource {
    fn accepts_unavailable_services(&self) -> bool {
        false
    }

    fn catalogue(
        &self,
        _cx: &Context,
    ) -> BoxFuture<'static, Result<Vec<ServiceCatalogueEntry>, ChordError>> {
        let catalogue = self
            .current
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .catalogue()
            .to_vec();
        futures::future::ready(Ok(catalogue)).boxed()
    }

    fn open(
        &self,
        options: RemoteServiceSourceOpenOptions,
    ) -> Result<Arc<dyn RemoteServices>, ChordError> {
        self.opened.fetch_add(1, Ordering::SeqCst);
        let provider = self
            .current
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone();
        let mut binding_options = RemoteServiceBindingOptions::new(
            options.services,
            create_loopback_service_transport(provider),
        );
        binding_options.bound = false;
        binding_options.assert_access = Some(options.assert_access);
        binding_options.on_error = Some(options.on_error);
        let binding = create_remote_service_binding(binding_options)?;
        Ok(Arc::new(RebindingServices {
            binding,
            disposed: Some(Arc::clone(&self.disposed)),
        }))
    }
}

#[tokio::test]
async fn reopens_source_bindings_from_changed_catalogues_for_a_replacement_generation() -> Step {
    let left_provider = provider_of(&left_value(), "left")?;
    let right_provider = provider_of(&right_value(), "right")?;
    let current = Arc::new(Mutex::new(left_provider.clone()));
    let opened = Arc::new(AtomicUsize::new(0));
    let disposed = Arc::new(AtomicUsize::new(0));
    let source: Arc<dyn RemoteServiceSource> = Arc::new(ReopeningSource {
        current: Arc::clone(&current),
        opened: Arc::clone(&opened),
        disposed: Arc::clone(&disposed),
    });
    let values = Recorder::default();
    let consumer = |id: &str, service: Service<()>| {
        let values = values.clone();
        define_facet(id, move |env| -> Step {
            let handle = env.use_service(&service)?;
            let values = values.clone();
            env.on_activate(move || {
                Outcome::pending(async move {
                    values.push(read(&handle, &bg()).await?);
                    Ok::<(), ChordError>(())
                })
            })?;
            Ok(())
        })
    };
    let first = create_facet_host(FacetOptions {
        facets: vec![consumer("left-consumer", left_value())],
        service_sources: vec![Arc::clone(&source)],
        ..Default::default()
    })
    .await?;
    first.dispose().await?;

    *current.lock().unwrap_or_else(PoisonError::into_inner) = right_provider.clone();
    let second = create_facet_host(FacetOptions {
        facets: vec![consumer("right-consumer", right_value())],
        service_sources: vec![source],
        ..Default::default()
    })
    .await?;
    second.dispose().await?;

    assert_eq!(values.get(), ["left", "right"]);
    assert_eq!(opened.load(Ordering::SeqCst), 2);
    assert_eq!(disposed.load(Ordering::SeqCst), 2);
    left_provider.dispose()?;
    right_provider.dispose()?;
    Ok(())
}

#[tokio::test]
async fn rejects_missing_dependencies_cycles_and_asynchronous_setup() {
    let activated = Arc::new(AtomicUsize::new(0));
    let missing = {
        let activated = Arc::clone(&activated);
        define_facet("missing", move |env| -> Step {
            env.use_service(&source_service())?;
            let activated = Arc::clone(&activated);
            env.on_activate(move || {
                activated.fetch_add(1, Ordering::SeqCst);
            })?;
            Ok(())
        })
    };
    let error = create_facet_host(FacetOptions {
        facets: vec![missing],
        ..Default::default()
    })
    .await
    .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("Facet missing requires local/test.experimental.source/singleton, but no facet provides it"),
        "{error}"
    );
    assert_eq!(activated.load(Ordering::SeqCst), 0);

    let first = define_facet("first", |env| -> Step {
        env.use_service(&projection_service())?;
        env.provide(&source_service(), reader("first"))?;
        Ok(())
    });
    let second = define_facet("second", |env| -> Step {
        env.use_service(&source_service())?;
        env.provide(&projection_service(), reader("second"))?;
        Ok(())
    });
    let error = create_facet_host(FacetOptions {
        facets: vec![first, second],
        ..Default::default()
    })
    .await
    .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("Facet dependency cycle: first, second"),
        "{error}"
    );
}
