//! Port of `test/facet-loader.test.ts`.
//!
//! `GenerationValue.read` of the local service is a plain method on the typed
//! implementation (read through `handle.get`); the remote one is a described
//! `read` method. TS `rejects.toBe(failure)` compares the error message.

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;

use futures::future::BoxFuture;
use futures::FutureExt;
use serde_json::json as j;

use super::{json, Gate, Recorder};
use crate::context::{Context, BACKGROUND_CONTEXT};
use crate::error::{BoxError, ChordError};
use crate::services::loopback::create_loopback_service_transport;
use crate::types::ServiceMode;
use crate::{
    combine_facet_loaders, create_facet_host, create_remote_service_binding,
    create_static_facet_loader, define_facet, define_local_service, define_service, Facet,
    FacetLoader, FacetOptions, LoadedFacets, Outcome, RemoteServiceBindingOptions, Service,
    ServiceObject, ServiceProviderUpdate,
};

type Step = Result<(), BoxError>;

fn bg() -> Context {
    BACKGROUND_CONTEXT.clone()
}

/// The typed process-local `GenerationValue`.
#[derive(Clone)]
struct GenerationValue {
    name: String,
}

impl GenerationValue {
    fn read(&self) -> String {
        self.name.clone()
    }
}

fn local_generation_value() -> Service<GenerationValue> {
    define_local_service("test.experimental.local-generation-value").unwrap()
}

fn remote_generation_value() -> Service<()> {
    define_service("test.experimental.remote-generation-value").unwrap()
}

fn reader(name: &str) -> ServiceObject {
    let name = name.to_owned();
    ServiceObject::new().method("read", move |_args, _cx| {
        let name = name.clone();
        async move { Ok::<_, BoxError>(Some(json(j!(name)))) }
    })
}

fn empty_facet(id: &str) -> Arc<dyn Facet> {
    define_facet(id, |_env| -> Step { Ok(()) })
}

struct TracingLoader {
    name: &'static str,
    facet: Arc<dyn Facet>,
    trace: Recorder<String>,
}

impl FacetLoader for TracingLoader {
    fn load(&self) -> BoxFuture<'static, Result<LoadedFacets, ChordError>> {
        let name = self.name;
        let facet = Arc::clone(&self.facet);
        let trace = self.trace.clone();
        async move {
            trace.push(format!("load {name}"));
            Ok(LoadedFacets::new(vec![facet], move || {
                let trace = trace.clone();
                async move {
                    trace.push(format!("dispose {name}"));
                    Ok(())
                }
                .boxed()
            }))
        }
        .boxed()
    }
}

fn same_facets(left: &[Arc<dyn Facet>], right: &[Arc<dyn Facet>]) -> bool {
    left.len() == right.len() && left.iter().zip(right).all(|(a, b)| Arc::ptr_eq(a, b))
}

#[tokio::test]
async fn combines_loaded_facets_in_loader_order_and_disposes_generations_in_reverse() -> Step {
    let trace = Recorder::default();
    let first_facet = empty_facet("first");
    let second_facet = empty_facet("second");
    let first = Arc::new(TracingLoader {
        name: "first",
        facet: Arc::clone(&first_facet),
        trace: trace.clone(),
    });
    let second = Arc::new(TracingLoader {
        name: "second",
        facet: Arc::clone(&second_facet),
        trace: trace.clone(),
    });

    let loaded = combine_facet_loaders(vec![first, second]).load().await?;
    assert!(same_facets(&loaded.facets, &[first_facet, second_facet]));
    loaded.dispose().await?;
    loaded.dispose().await?;
    assert_eq!(
        trace.get(),
        [
            "load first",
            "load second",
            "dispose second",
            "dispose first"
        ]
    );
    Ok(())
}

struct FixedLoader {
    facet: Arc<dyn Facet>,
    disposed: Arc<AtomicUsize>,
}

impl FacetLoader for FixedLoader {
    fn load(&self) -> BoxFuture<'static, Result<LoadedFacets, ChordError>> {
        let disposed = Arc::clone(&self.disposed);
        let loaded = LoadedFacets::new(vec![Arc::clone(&self.facet)], move || {
            disposed.fetch_add(1, Ordering::SeqCst);
            futures::future::ready(Ok(())).boxed()
        });
        futures::future::ready(Ok(loaded)).boxed()
    }
}

struct FailingLoader;

impl FacetLoader for FailingLoader {
    fn load(&self) -> BoxFuture<'static, Result<LoadedFacets, ChordError>> {
        futures::future::ready(Err(ChordError::error("load failed"))).boxed()
    }
}

#[tokio::test]
async fn cleans_up_loaded_facets_when_a_later_loader_fails() {
    let disposed = Arc::new(AtomicUsize::new(0));
    let first = Arc::new(FixedLoader {
        facet: empty_facet("first"),
        disposed: Arc::clone(&disposed),
    });
    let error = combine_facet_loaders(vec![first, Arc::new(FailingLoader)])
        .load()
        .await
        .unwrap_err();
    assert_eq!(error.to_string(), "load failed");
    assert_eq!(disposed.load(Ordering::SeqCst), 1);
}

struct GenerationLoader {
    generation: AtomicUsize,
    trace: Recorder<String>,
    replacement_started: Gate,
    replacement_can_continue: Gate,
}

impl FacetLoader for GenerationLoader {
    fn load(&self) -> BoxFuture<'static, Result<LoadedFacets, ChordError>> {
        let name = if self.generation.fetch_add(1, Ordering::SeqCst) == 0 {
            "A"
        } else {
            "B"
        };
        let trace = self.trace.clone();
        let started = self.replacement_started.clone();
        let proceed = self.replacement_can_continue.clone();
        trace.push(format!("load {name}"));
        let setup_trace = trace.clone();
        let facet = define_facet("provider", move |env| -> Step {
            setup_trace.push(format!("setup provider {name}"));
            env.provide(
                &local_generation_value(),
                crate::ServiceImplementation::Local(GenerationValue {
                    name: name.to_owned(),
                }),
            )?;
            env.provide(&remote_generation_value(), reader(name))?;
            let activate_trace = setup_trace.clone();
            let started = started.clone();
            let proceed = proceed.clone();
            env.on_activate(move || {
                Outcome::pending(async move {
                    activate_trace.push(format!("activate provider {name}"));
                    if name == "B" {
                        started.resolve();
                        proceed.wait().await?;
                    }
                    Ok::<(), ChordError>(())
                })
            })?;
            let deactivate_trace = setup_trace.clone();
            env.on_deactivate(move || {
                deactivate_trace.push(format!("deactivate provider {name}"));
            })?;
            Ok(())
        });
        let loaded = LoadedFacets::new(vec![facet], move || {
            trace.push(format!("unload {name}"));
            futures::future::ready(Ok(())).boxed()
        });
        futures::future::ready(Ok(loaded)).boxed()
    }
}

async fn read_remote(handle: &crate::ServiceHandle) -> Result<String, ChordError> {
    let value = handle.call("read", vec![], &bg())?.await?;
    Ok(value
        .and_then(|value| value.as_str().map(str::to_owned))
        .unwrap_or_default())
}

/// The consumer of the local generation value, recording its handle.
fn generation_consumer(
    trace: Recorder<String>,
    local_value: Recorder<crate::ServiceHandle>,
) -> Arc<dyn Facet> {
    define_facet("consumer", move |env| -> Step {
        trace.push("setup consumer".to_owned());
        let handle = env.use_service(&local_generation_value())?;
        local_value.push(handle.clone());
        let activate_trace = trace.clone();
        env.on_activate(move || -> Result<(), ChordError> {
            let value = handle.get::<GenerationValue>()?.read();
            activate_trace.push(format!("activate consumer:{value}"));
            Ok(())
        })?;
        let deactivate_trace = trace.clone();
        env.on_deactivate(move || deactivate_trace.push("deactivate consumer".to_owned()))?;
        Ok(())
    })
}

#[tokio::test]
async fn keeps_local_and_rpc_service_handles_stable_when_their_provider_facet_reloads() -> Step {
    let trace = Recorder::default();
    let local_value: Recorder<crate::ServiceHandle> = Recorder::default();
    let consumer = generation_consumer(trace.clone(), local_value.clone());
    let loader = GenerationLoader {
        generation: AtomicUsize::new(0),
        trace: trace.clone(),
        replacement_started: Gate::new(),
        replacement_can_continue: Gate::new(),
    };

    let loaded_a = loader.load().await?;
    let mut facets = vec![consumer];
    facets.extend(loaded_a.facets.clone());
    let host = create_facet_host(FacetOptions {
        facets,
        ..Default::default()
    })
    .await?;
    let original_local_handle = local_value.get()[0].clone();
    let local_read = || {
        original_local_handle
            .get::<GenerationValue>()
            .map(|value| value.read())
    };
    let remote_services = create_remote_service_binding(RemoteServiceBindingOptions::new(
        vec![remote_generation_value().id().to_owned()],
        create_loopback_service_transport(host.services().clone()),
    ))?;
    let original_remote_handle = remote_services.use_service(&remote_generation_value())?;
    remote_services.ready(&bg()).await?;
    assert_eq!(local_read()?, "A");
    assert_eq!(read_remote(&original_remote_handle).await?, "A");

    let invalid = define_facet("provider", |env| -> Step {
        env.provide(
            &local_generation_value(),
            crate::ServiceImplementation::Local(GenerationValue {
                name: "invalid".to_owned(),
            }),
        )?;
        Ok(())
    });
    let error = host.reload(vec![invalid]).await.unwrap_err();
    assert!(error
        .to_string()
        .contains("Reloaded facet provider must preserve its service requirements and provisions"));
    assert_eq!(local_read()?, "A");
    assert_eq!(read_remote(&original_remote_handle).await?, "A");

    let loaded_b = loader.load().await?;
    let reload = tokio::spawn({
        let host = host.clone();
        let facets = loaded_b.facets.clone();
        async move { host.reload(facets).await }
    });
    loader.replacement_started.wait().await?;
    assert_eq!(local_read()?, "A");
    assert_eq!(read_remote(&original_remote_handle).await?, "A");
    loader.replacement_can_continue.resolve();
    reload.await??;
    loaded_a.dispose().await?;

    assert_eq!(local_value.len(), 1);
    assert!(remote_services
        .use_service(&remote_generation_value())?
        .same(&original_remote_handle));
    assert_eq!(local_read()?, "B");
    assert_eq!(read_remote(&original_remote_handle).await?, "B");

    remote_services.dispose(&bg()).await?;
    host.dispose().await?;
    loaded_b.dispose().await?;
    assert_eq!(
        trace.get(),
        [
            "load A",
            "setup consumer",
            "setup provider A",
            "activate provider A",
            "activate consumer:A",
            "load B",
            "setup provider B",
            "activate provider B",
            "deactivate provider A",
            "unload A",
            "deactivate consumer",
            "deactivate provider B",
            "unload B",
        ]
    );
    Ok(())
}

#[tokio::test]
async fn rejects_remote_singleton_member_shape_changes_before_reload_cutover() -> Step {
    let retained: Recorder<crate::ServiceHandle> = Recorder::default();
    let provider_disposed = Arc::new(AtomicBool::new(false));
    let consumer = {
        let retained = retained.clone();
        define_facet("shape-consumer", move |env| -> Step {
            retained.push(env.use_service(&remote_generation_value())?);
            Ok(())
        })
    };
    let provider = {
        let disposed = Arc::clone(&provider_disposed);
        define_facet("shape-provider", move |env| -> Step {
            env.provide(&remote_generation_value(), reader("A"))?;
            let disposed = Arc::clone(&disposed);
            env.on_deactivate(move || disposed.store(true, Ordering::SeqCst))?;
            Ok(())
        })
    };
    let host = create_facet_host(FacetOptions {
        facets: vec![consumer, provider],
        ..Default::default()
    })
    .await?;

    let renamed = define_facet("shape-provider", |env| -> Step {
        let object = ServiceObject::new().method("renamed", |_args, _cx| async {
            Ok::<_, BoxError>(Some(json(j!("B"))))
        });
        env.provide(&remote_generation_value(), object)?;
        Ok(())
    });
    let error = host.reload(vec![renamed]).await.unwrap_err();
    assert!(
        error
            .to_string()
            .contains("replacement must preserve its member shape"),
        "{error}"
    );
    assert!(!provider_disposed.load(Ordering::SeqCst));
    assert_eq!(read_remote(&retained.get()[0]).await?, "A");

    host.dispose().await?;
    assert!(provider_disposed.load(Ordering::SeqCst));
    Ok(())
}

#[tokio::test]
async fn terminates_the_host_when_old_cleanup_fails_after_cutover() -> Step {
    let provider = |name: &'static str, fail_cleanup: bool| {
        define_facet("cleanup-provider", move |env| -> Step {
            env.provide(&remote_generation_value(), reader(name))?;
            env.on_deactivate(move || -> Result<(), ChordError> {
                if fail_cleanup {
                    return Err(ChordError::error("cleanup failed"));
                }
                Ok(())
            })?;
            Ok(())
        })
    };
    let host = create_facet_host(FacetOptions {
        facets: vec![provider("A", true)],
        ..Default::default()
    })
    .await?;

    let error = host.reload(vec![provider("B", false)]).await.unwrap_err();
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
async fn cleans_failed_candidate_activation_in_reverse_dependency_order() -> Step {
    let trace = Recorder::default();
    let provider = |name: &'static str| {
        let trace = trace.clone();
        define_facet("ordered-provider", move |env| -> Step {
            env.provide(&remote_generation_value(), reader(name))?;
            let activate = trace.clone();
            env.on_activate(move || activate.push(format!("activate provider {name}")))?;
            let deactivate = trace.clone();
            env.on_deactivate(move || deactivate.push(format!("deactivate provider {name}")))?;
            Ok(())
        })
    };
    let consumer = |name: &'static str, fail: bool| {
        let trace = trace.clone();
        define_facet("ordered-consumer", move |env| -> Step {
            env.use_service(&remote_generation_value())?;
            let activate = trace.clone();
            env.on_activate(move || -> Result<(), ChordError> {
                activate.push(format!("activate consumer {name}"));
                if fail {
                    return Err(ChordError::error("consumer activation failed"));
                }
                Ok(())
            })?;
            let deactivate = trace.clone();
            env.on_deactivate(move || deactivate.push(format!("deactivate consumer {name}")))?;
            Ok(())
        })
    };
    let host = create_facet_host(FacetOptions {
        facets: vec![consumer("A", false), provider("A")],
        ..Default::default()
    })
    .await?;
    let before = trace.len();

    let error = host
        .reload(vec![consumer("B", true), provider("B")])
        .await
        .unwrap_err();
    assert_eq!(error.to_string(), "consumer activation failed");
    assert_eq!(
        trace.get()[before..],
        [
            "activate provider B",
            "activate consumer B",
            "deactivate consumer B",
            "deactivate provider B"
        ]
    );
    host.dispose().await?;
    Ok(())
}

#[tokio::test]
async fn terminates_the_host_when_replacement_publication_fails_after_cutover() -> Step {
    let provider = |name: &'static str| {
        define_facet("publication-provider", move |env| -> Step {
            env.provide(&remote_generation_value(), reader(name))?;
            Ok(())
        })
    };
    let host = create_facet_host(FacetOptions {
        facets: vec![provider("A")],
        ..Default::default()
    })
    .await?;
    let subscription = host.services().subscribe(
        remote_generation_value().id(),
        ServiceMode::Singleton,
        Arc::new(
            |_update: ServiceProviderUpdate, _cx: &Context| -> Result<(), ChordError> {
                Err(ChordError::error("publication failed"))
            },
        ),
    )?;
    subscription.activate()?;

    let error = host.reload(vec![provider("B")]).await.unwrap_err();
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
async fn keeps_the_old_generation_active_when_replacement_activation_fails_before_cutover() -> Step
{
    let trace = Recorder::default();
    let retained: Recorder<crate::ServiceHandle> = Recorder::default();
    let consumer = {
        let trace = trace.clone();
        let retained = retained.clone();
        define_facet("terminal-consumer", move |env| -> Step {
            retained.push(env.use_service(&remote_generation_value())?);
            let trace = trace.clone();
            env.on_deactivate(move || trace.push("deactivate consumer".to_owned()))?;
            Ok(())
        })
    };
    let provider = |name: &'static str, fail: bool| {
        let trace = trace.clone();
        define_facet("terminal-provider", move |env| -> Step {
            env.provide(&remote_generation_value(), reader(name))?;
            let activate = trace.clone();
            env.on_activate(move || -> Result<(), ChordError> {
                activate.push(format!("activate {name}"));
                if fail {
                    return Err(ChordError::error("replacement activation failed"));
                }
                Ok(())
            })?;
            let deactivate = trace.clone();
            env.on_deactivate(move || deactivate.push(format!("deactivate {name}")))?;
            Ok(())
        })
    };
    let host = create_facet_host(FacetOptions {
        facets: vec![consumer, provider("A", false)],
        ..Default::default()
    })
    .await?;
    let retained = retained.get()[0].clone();
    assert_eq!(read_remote(&retained).await?, "A");

    let error = host.reload(vec![provider("B", true)]).await.unwrap_err();
    assert_eq!(error.to_string(), "replacement activation failed");
    assert_eq!(trace.get(), ["activate A", "activate B", "deactivate B"]);
    assert_eq!(read_remote(&retained).await?, "A");
    host.reload(vec![]).await?;
    host.dispose().await?;
    assert_eq!(
        trace.get(),
        [
            "activate A",
            "activate B",
            "deactivate B",
            "deactivate consumer",
            "deactivate A"
        ]
    );
    Ok(())
}

#[tokio::test]
async fn creates_a_reusable_static_loader() -> Step {
    let first_facet = empty_facet("first");
    let loader = create_static_facet_loader(vec![Arc::clone(&first_facet)]);
    let first = loader.load().await?;
    let second = loader.load().await?;
    assert!(same_facets(
        &first.facets,
        std::slice::from_ref(&first_facet)
    ));
    assert!(same_facets(
        &second.facets,
        std::slice::from_ref(&first_facet)
    ));
    let (left, right) = futures::join!(first.dispose(), second.dispose());
    left?;
    right?;
    Ok(())
}
