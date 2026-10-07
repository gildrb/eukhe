//! Port of `test/models-runtime.test.ts` (catalog, registry, refresh, and
//! request cases; the auth cases are in `models_runtime_auth.rs`).

mod common;

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use common::{
    api_key, context, env_key_auth, now_f64, oauth, silent_streams, store, test_model,
    test_provider, FnApiKeyAuth, TestOAuth, TestProvider,
};
use eukhe_chord::context::{AbortController, AbortSignal};
use eukhe_pi_ai::auth::{
    AuthOperationOptions, AuthResult, CredentialInfo, CredentialStore, InMemoryCredentialStore,
    ModelAuth, ProviderAuth,
};
use eukhe_pi_ai::models::{
    calculate_cost, create_models, create_provider, has_api, CreateModelsOptions,
    CreateProviderOptions, FetchModelsFn, ModelsPersistence, ModelsPublication,
    ModelsRefreshOptions, ProviderApi,
};
use eukhe_pi_ai::models_store::{
    InMemoryModelsStore, ModelsStore, ModelsStoreEntry, ModelsStoreOperationOptions,
};
use eukhe_pi_ai::types::SimpleStreamOptions;
use eukhe_pi_ai::utils::diagnostics::Thrown;
use eukhe_types::pi_ai::{AnyModel, ModelCost, ModelCostTier, StopReason, Usage, UsageCost};
use futures::future::BoxFuture;
use futures::StreamExt;
use tokio::sync::{oneshot, Notify};

fn ids(models: &[eukhe_types::pi_ai::Model]) -> Vec<String> {
    models.iter().map(|model| model.id.clone()).collect()
}

#[tokio::test]
async fn enumerates_credential_metadata_without_exposing_secrets() {
    let credentials = InMemoryCredentialStore::new();
    store(&credentials, "api-provider", api_key("secret")).await;
    store(
        &credentials,
        "oauth-provider",
        oauth("access", "refresh", now_f64() + 60_000.0),
    )
    .await;

    let listed: Vec<CredentialInfo> = credentials
        .list(AuthOperationOptions::default())
        .await
        .expect("list");
    assert_eq!(
        serde_json::to_value(listed).expect("json"),
        serde_json::json!([
            { "providerId": "api-provider", "type": "api_key" },
            { "providerId": "oauth-provider", "type": "oauth" },
        ])
    );
}

#[test]
fn applies_request_wide_pricing_tiers_above_the_configured_input_threshold() {
    let mut model = test_model("openai", "gpt-5.6-sol");
    model.cost = ModelCost {
        input: 5.0,
        output: 30.0,
        cache_read: 0.5,
        cache_write: 6.25,
        tiers: Some(vec![ModelCostTier {
            input_tokens_above: 272_000,
            input: 10.0,
            output: 45.0,
            cache_read: 1.0,
            cache_write: 12.5,
        }]),
    };
    let create_usage = |cache_write: u64| Usage {
        input: 200_000,
        output: 100_000,
        cache_read: 72_000,
        cache_write,
        total_tokens: 372_000 + cache_write,
        ..Usage::default()
    };

    let short = calculate_cost(&model, &mut create_usage(0));
    assert_eq!(
        (
            short.input,
            short.output,
            short.cache_read,
            short.cache_write
        ),
        (1.0, 3.0, 0.036, 0.0)
    );

    let long = calculate_cost(&model, &mut create_usage(1));
    assert_eq!(
        (long.input, long.output, long.cache_read, long.cache_write),
        (2.0, 4.5, 0.072, 0.000_012_5)
    );
    let _: UsageCost = long;
}

#[test]
fn registers_replaces_and_deletes_providers() {
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        ..TestProvider::default()
    }));
    models.set_provider(test_provider(TestProvider {
        id: "p2".into(),
        ..TestProvider::default()
    }));
    let ids: Vec<String> = models
        .get_providers()
        .iter()
        .map(|p| p.id.clone())
        .collect();
    assert_eq!(ids, ["p1", "p2"]);

    let replacement = test_provider(TestProvider {
        id: "p1".into(),
        ..TestProvider::default()
    });
    let replacement_stream = Arc::clone(&replacement.stream);
    models.set_provider(replacement);
    let stored = models.get_provider("p1").expect("p1");
    assert!(Arc::ptr_eq(&stored.stream, &replacement_stream));
    assert_eq!(models.get_providers().len(), 2);

    models.delete_provider("p1");
    assert!(models.get_provider("p1").is_none());

    models.clear_providers();
    assert_eq!(models.get_providers().len(), 0);
}

#[test]
fn lists_and_finds_models_per_provider() {
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        models: Some(vec![test_model("p1", "m1"), test_model("p1", "m2")]),
        ..TestProvider::default()
    }));
    models.set_provider(test_provider(TestProvider {
        id: "p2".into(),
        models: Some(vec![test_model("p2", "m3")]),
        ..TestProvider::default()
    }));

    assert_eq!(ids(&models.get_models(None)), ["m1", "m2", "m3"]);
    assert_eq!(ids(&models.get_models(Some("p1"))), ["m1", "m2"]);
    assert!(models.get_models(Some("nope")).is_empty());
    assert_eq!(
        models.get_model("p2", "m3").map(|m| m.id),
        Some("m3".to_owned())
    );
    assert!(models.get_model("p2", "missing").is_none());

    let found = AnyModel::Chat(models.get_model("p2", "m3").expect("m3"));
    assert!(!has_api(&found, "openai-completions"));
    assert!(has_api(&found, "test-api"));
}

#[tokio::test]
async fn keeps_chat_reads_independent_from_the_all_model_catalog() {
    let mut provider = test_provider(TestProvider {
        id: "chat-only".into(),
        ..TestProvider::default()
    });
    provider.get_all_models = Some(Arc::new(|| Err(common::error("all models unavailable"))));
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(provider);

    assert_eq!(ids(&models.get_models(Some("chat-only"))), ["model-a"]);
    assert_eq!(
        models.get_model("chat-only", "model-a").map(|m| m.id),
        Some("model-a".to_owned())
    );
    let available = models
        .get_available(Some("chat-only"), AuthOperationOptions::default())
        .await
        .expect("available");
    assert_eq!(ids(&available), ["model-a"]);
    assert!(models.get_all_models(Some("chat-only")).is_empty());
}

#[test]
fn swallows_provider_source_failures_for_both_all_provider_and_single_provider_listing() {
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(test_provider(TestProvider {
        id: "broken".into(),
        get_models: Some(Arc::new(|| Err(common::error("boom")))),
        ..TestProvider::default()
    }));
    models.set_provider(test_provider(TestProvider {
        id: "ok".into(),
        models: Some(vec![test_model("ok", "m1")]),
        ..TestProvider::default()
    }));

    assert_eq!(ids(&models.get_models(None)), ["m1"]);
    assert!(models.get_models(Some("broken")).is_empty());
    // precise failures come from the provider directly
    let broken = models.get_provider("broken").expect("broken");
    assert_eq!((broken.get_models)().expect_err("boom").to_string(), "boom");
}

fn shared_models(
    initial: Vec<eukhe_types::pi_ai::Model>,
) -> Arc<Mutex<Vec<eukhe_types::pi_ai::Model>>> {
    Arc::new(Mutex::new(initial))
}

#[tokio::test]
async fn refresh_updates_every_configured_dynamic_provider_and_reports_failures() {
    let list = shared_models(vec![test_model("dyn", "before")]);
    let refreshes = Arc::new(AtomicUsize::new(0));
    let models = create_models(CreateModelsOptions::default());
    let read_list = Arc::clone(&list);
    let write_list = Arc::clone(&list);
    let counter = Arc::clone(&refreshes);
    models.set_provider(test_provider(TestProvider {
        id: "dyn".into(),
        get_models: Some(Arc::new(move || {
            Ok(read_list
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .clone())
        })),
        refresh_models: Some(Arc::new(move |refresh| {
            let list = Arc::clone(&write_list);
            let counter = Arc::clone(&counter);
            Box::pin(async move {
                if !refresh.allow_network {
                    return Ok(());
                }
                counter.fetch_add(1, Ordering::SeqCst);
                refresh
                    .publish(ModelsPublication {
                        persist: ModelsPersistence::Keep,
                        update: Some(Box::new(move || {
                            *list.lock().unwrap_or_else(PoisonError::into_inner) =
                                vec![test_model("dyn", "after")];
                        })),
                    })
                    .await?;
                Ok(())
            })
        })),
        ..TestProvider::default()
    }));
    models.set_provider(test_provider(TestProvider {
        id: "static".into(),
        models: Some(vec![test_model("static", "s1")]),
        ..TestProvider::default()
    }));

    assert!(models.get_model("dyn", "before").is_some());
    let first = models.refresh(ModelsRefreshOptions::default()).await;
    assert_eq!(first.errors.len(), 0);
    assert_eq!(refreshes.load(Ordering::SeqCst), 1);
    assert!(models.get_model("dyn", "after").is_some());
    assert!(models.get_model("dyn", "before").is_none());

    models.set_provider(test_provider(TestProvider {
        id: "flaky".into(),
        refresh_models: Some(Arc::new(|context| {
            Box::pin(async move {
                if context.allow_network {
                    return Err(common::error("fetch failed"));
                }
                Ok(())
            })
        })),
        ..TestProvider::default()
    }));
    let second = models.refresh(ModelsRefreshOptions::default()).await;
    assert_eq!(refreshes.load(Ordering::SeqCst), 2);
    assert_eq!(
        second.errors.get("flaky").map(ToString::to_string),
        Some("fetch failed".to_owned())
    );
}

#[tokio::test]
async fn restricts_refresh_work_to_selected_providers() {
    let calls: Arc<Mutex<Vec<String>>> = Arc::default();
    let models = create_models(CreateModelsOptions::default());
    for id in ["one", "two"] {
        let calls = Arc::clone(&calls);
        models.set_provider(test_provider(TestProvider {
            id: id.into(),
            refresh_models: Some(Arc::new(move |context| {
                let calls = Arc::clone(&calls);
                Box::pin(async move {
                    calls
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .push(format!(
                            "{id}:{}",
                            if context.allow_network {
                                "network"
                            } else {
                                "cache"
                            }
                        ));
                    Ok(())
                })
            })),
            ..TestProvider::default()
        }));
    }

    let result = models
        .refresh(ModelsRefreshOptions {
            providers: Some(vec!["two".into(), "unknown".into()]),
            ..ModelsRefreshOptions::default()
        })
        .await;

    assert_eq!(result.errors.len(), 0);
    assert_eq!(
        *calls.lock().unwrap_or_else(PoisonError::into_inner),
        ["two:cache", "two:network"]
    );
}

fn fetch_models<F, Fut>(fetch: F) -> FetchModelsFn
where
    F: Fn() -> Fut + Send + Sync + 'static,
    Fut: std::future::Future<Output = Result<Vec<AnyModel>, Thrown>> + Send + 'static,
{
    Arc::new(move |_context| Box::pin(fetch()))
}

#[tokio::test]
async fn restores_cached_models_before_waiting_for_network_auth() {
    let store = Arc::new(InMemoryModelsStore::new());
    store
        .write(
            "dynamic",
            ModelsStoreEntry {
                models: vec![AnyModel::Chat(test_model("dynamic", "cached"))],
                ..ModelsStoreEntry::default()
            },
            ModelsStoreOperationOptions::default(),
        )
        .await
        .expect("write");
    let auth_started = Arc::new(Notify::new());
    let finish_auth = Arc::new(Notify::new());
    let started = Arc::clone(&auth_started);
    let finish = Arc::clone(&finish_auth);
    let provider = create_provider(CreateProviderOptions {
        id: "dynamic".into(),
        auth: ProviderAuth {
            api_key: Some(
                FnApiKeyAuth::new("Blocked auth", move |_| {
                    let started = Arc::clone(&started);
                    let finish = Arc::clone(&finish);
                    async move {
                        started.notify_one();
                        finish.notified().await;
                        Ok(Some(AuthResult {
                            auth: ModelAuth {
                                api_key: Some("key".into()),
                                ..ModelAuth::default()
                            },
                            ..AuthResult::default()
                        }))
                    }
                })
                .arc(),
            ),
            oauth: None,
        },
        fetch_models: Some(fetch_models(|| async {
            Err(common::error("must not fetch"))
        })),
        api: Some(ProviderApi::Single(silent_streams())),
        ..CreateProviderOptions::default()
    })
    .expect("provider");
    let models = create_models(CreateModelsOptions {
        models_store: Some(store),
        ..CreateModelsOptions::default()
    });
    models.set_provider(provider);
    let controller = AbortController::new();
    let refreshing = models.clone();
    let signal = controller.signal();
    let pending = tokio::spawn(async move {
        refreshing
            .refresh(ModelsRefreshOptions {
                providers: Some(vec!["dynamic".into()]),
                signal: Some(signal),
                ..ModelsRefreshOptions::default()
            })
            .await
    });
    auth_started.notified().await;

    assert!(models.get_model("dynamic", "cached").is_some());
    controller.abort(None);
    assert!(pending.await.expect("join").aborted);
    finish_auth.notify_one();
}

/// A models store over one shared entry (the TS object-literal store).
struct SharedEntryStore {
    entry: Arc<Mutex<Option<ModelsStoreEntry>>>,
}

impl ModelsStore for SharedEntryStore {
    fn read(
        &self,
        _id: &str,
        _options: ModelsStoreOperationOptions,
    ) -> BoxFuture<'_, Result<Option<ModelsStoreEntry>, Thrown>> {
        let entry = self
            .entry
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone();
        Box::pin(async move { Ok(entry) })
    }
    fn write(
        &self,
        _id: &str,
        entry: ModelsStoreEntry,
        _options: ModelsStoreOperationOptions,
    ) -> BoxFuture<'_, Result<(), Thrown>> {
        *self.entry.lock().unwrap_or_else(PoisonError::into_inner) = Some(entry);
        Box::pin(async { Ok(()) })
    }
    fn delete(
        &self,
        _id: &str,
        _options: ModelsStoreOperationOptions,
    ) -> BoxFuture<'_, Result<(), Thrown>> {
        *self.entry.lock().unwrap_or_else(PoisonError::into_inner) = None;
        Box::pin(async { Ok(()) })
    }
}

#[tokio::test]
async fn lets_providers_choose_persistent_deletion_and_ephemeral_publication_atomically() {
    let entry = Arc::new(Mutex::new(Some(ModelsStoreEntry {
        models: vec![AnyModel::Chat(test_model("dynamic", "stored"))],
        ..ModelsStoreEntry::default()
    })));
    let state = Arc::new(Mutex::new("initial".to_owned()));
    let models = create_models(CreateModelsOptions {
        models_store: Some(Arc::new(SharedEntryStore {
            entry: Arc::clone(&entry),
        })),
        ..CreateModelsOptions::default()
    });
    let refresh_entry = Arc::clone(&entry);
    let refresh_state = Arc::clone(&state);
    models.set_provider(test_provider(TestProvider {
        id: "dynamic".into(),
        refresh_models: Some(Arc::new(move |context| {
            let entry = Arc::clone(&refresh_entry);
            let state = Arc::clone(&refresh_state);
            Box::pin(async move {
                assert_eq!(
                    context
                        .stored
                        .as_ref()
                        .map(|stored| stored.models[0].id().to_owned()),
                    Some("stored".to_owned())
                );
                let deleted_state = Arc::clone(&state);
                context
                    .publish(ModelsPublication {
                        persist: ModelsPersistence::Delete,
                        update: Some(Box::new(move || {
                            assert!(entry
                                .lock()
                                .unwrap_or_else(PoisonError::into_inner)
                                .is_none());
                            *deleted_state.lock().unwrap_or_else(PoisonError::into_inner) =
                                "deleted".into();
                        })),
                    })
                    .await?;
                context
                    .publish(ModelsPublication {
                        persist: ModelsPersistence::Keep,
                        update: Some(Box::new(move || {
                            *state.lock().unwrap_or_else(PoisonError::into_inner) =
                                "ephemeral".into();
                        })),
                    })
                    .await?;
                Ok(())
            })
        })),
        ..TestProvider::default()
    }));

    let result = models
        .refresh(ModelsRefreshOptions {
            allow_network: Some(false),
            ..ModelsRefreshOptions::default()
        })
        .await;

    assert_eq!(result.errors.len(), 0);
    assert!(entry
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .is_none());
    assert_eq!(
        *state.lock().unwrap_or_else(PoisonError::into_inner),
        "ephemeral"
    );
}

#[tokio::test]
async fn persists_dynamic_catalogs_and_restores_them_without_network_access() {
    let credentials = Arc::new(InMemoryCredentialStore::new());
    let models_store = Arc::new(InMemoryModelsStore::new());
    store(credentials.as_ref(), "dynamic", api_key("key")).await;
    let create_dynamic_provider = |fetch: FetchModelsFn| {
        create_provider(CreateProviderOptions {
            id: "dynamic".into(),
            auth: ProviderAuth {
                api_key: Some(env_key_auth(None).arc()),
                oauth: None,
            },
            fetch_models: Some(fetch),
            api: Some(ProviderApi::Single(silent_streams())),
            ..CreateProviderOptions::default()
        })
        .expect("provider")
    };

    let online = create_models(CreateModelsOptions {
        credentials: Some(credentials.clone()),
        models_store: Some(models_store.clone()),
        ..CreateModelsOptions::default()
    });
    online.set_provider(create_dynamic_provider(fetch_models(|| async {
        Ok(vec![AnyModel::Chat(test_model("dynamic", "fetched"))])
    })));
    assert_eq!(
        online
            .refresh(ModelsRefreshOptions::default())
            .await
            .errors
            .len(),
        0
    );
    assert!(online.get_model("dynamic", "fetched").is_some());

    let offline = create_models(CreateModelsOptions {
        credentials: Some(credentials),
        models_store: Some(models_store),
        ..CreateModelsOptions::default()
    });
    offline.set_provider(create_dynamic_provider(fetch_models(|| async {
        Err(common::error("must not fetch"))
    })));
    let result = offline
        .refresh(ModelsRefreshOptions {
            allow_network: Some(false),
            ..ModelsRefreshOptions::default()
        })
        .await;
    assert_eq!(result.errors.len(), 0);
    assert!(offline.get_model("dynamic", "fetched").is_some());
}

#[tokio::test]
async fn passes_effective_api_key_credentials_and_refresh_options_while_skipping_unconfigured_providers(
) {
    let effective: Arc<Mutex<Option<serde_json::Value>>> = Arc::default();
    let force: Arc<Mutex<Option<bool>>> = Arc::default();
    let unconfigured_refreshes = Arc::new(AtomicUsize::new(0));
    let models = create_models(CreateModelsOptions::default());
    let (seen, seen_force) = (Arc::clone(&effective), Arc::clone(&force));
    models.set_provider(test_provider(TestProvider {
        id: "configured".into(),
        auth: Some(ProviderAuth {
            api_key: Some(env_key_auth(Some("ambient-key")).arc()),
            oauth: None,
        }),
        refresh_models: Some(Arc::new(move |context| {
            let (seen, seen_force) = (Arc::clone(&seen), Arc::clone(&seen_force));
            Box::pin(async move {
                if context.allow_network {
                    *seen.lock().unwrap_or_else(PoisonError::into_inner) =
                        Some(serde_json::to_value(&context.credential).expect("json"));
                    *seen_force.lock().unwrap_or_else(PoisonError::into_inner) = context.force;
                }
                Ok(())
            })
        })),
        ..TestProvider::default()
    }));
    let counter = Arc::clone(&unconfigured_refreshes);
    models.set_provider(test_provider(TestProvider {
        id: "unconfigured".into(),
        auth: Some(ProviderAuth {
            api_key: Some(env_key_auth(None).arc()),
            oauth: None,
        }),
        refresh_models: Some(Arc::new(move |context| {
            let counter = Arc::clone(&counter);
            Box::pin(async move {
                if context.allow_network {
                    counter.fetch_add(1, Ordering::SeqCst);
                }
                Ok(())
            })
        })),
        ..TestProvider::default()
    }));

    models
        .refresh(ModelsRefreshOptions {
            force: Some(true),
            ..ModelsRefreshOptions::default()
        })
        .await;
    assert_eq!(
        *effective.lock().unwrap_or_else(PoisonError::into_inner),
        Some(serde_json::json!({ "type": "api_key", "key": "ambient-key" }))
    );
    assert_eq!(
        *force.lock().unwrap_or_else(PoisonError::into_inner),
        Some(true)
    );
    assert_eq!(unconfigured_refreshes.load(Ordering::SeqCst), 0);
}

#[tokio::test]
async fn refreshes_expired_oauth_before_refreshing_models() {
    let credentials = Arc::new(InMemoryCredentialStore::new());
    let seen: Arc<Mutex<Option<eukhe_pi_ai::auth::Credential>>> = Arc::default();
    store(
        credentials.as_ref(),
        "oauth-dynamic",
        oauth("expired", "refresh", 0.0),
    )
    .await;
    let models = create_models(CreateModelsOptions {
        credentials: Some(credentials.clone()),
        ..CreateModelsOptions::default()
    });
    let record = Arc::clone(&seen);
    models.set_provider(test_provider(TestProvider {
        id: "oauth-dynamic".into(),
        auth: Some(ProviderAuth {
            api_key: None,
            oauth: Some(
                TestOAuth::with_refresh(|_| async {
                    Ok(eukhe_pi_ai::auth::OAuthCredential::new(
                        "rotated",
                        "fresh",
                        now_f64() + 60_000.0,
                    ))
                })
                .arc(),
            ),
        }),
        refresh_models: Some(Arc::new(move |context| {
            let record = Arc::clone(&record);
            Box::pin(async move {
                if context.allow_network {
                    *record.lock().unwrap_or_else(PoisonError::into_inner) =
                        context.credential.clone();
                }
                Ok(())
            })
        })),
        ..TestProvider::default()
    }));

    assert_eq!(
        models
            .refresh(ModelsRefreshOptions::default())
            .await
            .errors
            .len(),
        0
    );
    let Some(eukhe_pi_ai::auth::Credential::OAuth(credential)) =
        seen.lock().unwrap_or_else(PoisonError::into_inner).clone()
    else {
        panic!("oauth credential expected");
    };
    assert_eq!(
        (credential.access.as_str(), credential.refresh.as_str()),
        ("fresh", "rotated")
    );
    let Some(eukhe_pi_ai::auth::Credential::OAuth(stored)) = credentials
        .read("oauth-dynamic", AuthOperationOptions::default())
        .await
        .expect("read")
    else {
        panic!("stored oauth expected");
    };
    assert_eq!(
        (stored.access.as_str(), stored.refresh.as_str()),
        ("fresh", "rotated")
    );
}

async fn wait_for_refresh_token(credentials: &InMemoryCredentialStore, expected: &str) {
    for _ in 0..1000 {
        if let Ok(Some(eukhe_pi_ai::auth::Credential::OAuth(credential))) = credentials
            .read("p1", AuthOperationOptions::default())
            .await
        {
            if credential.refresh == expected {
                return;
            }
        }
        tokio::task::yield_now().await;
    }
    panic!("refresh token {expected} was never persisted");
}

#[tokio::test]
async fn persists_an_oauth_refresh_that_started_before_the_model_refresh_was_cancelled() {
    let credentials = Arc::new(InMemoryCredentialStore::new());
    store(credentials.as_ref(), "p1", oauth("old", "old-refresh", 0.0)).await;
    let controller = AbortController::new();
    let models = create_models(CreateModelsOptions {
        credentials: Some(credentials.clone()),
        ..CreateModelsOptions::default()
    });
    let aborter = controller.clone();
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        auth: Some(ProviderAuth {
            api_key: None,
            oauth: Some(
                TestOAuth::with_refresh(move |credential| {
                    aborter.abort(None);
                    async move {
                        Ok(eukhe_pi_ai::auth::OAuthCredential {
                            access: "new".into(),
                            refresh: "new-refresh".into(),
                            expires: now_f64() + 60_000.0,
                            ..credential
                        })
                    }
                })
                .arc(),
            ),
        }),
        refresh_models: Some(Arc::new(|_| Box::pin(async { Ok(()) }))),
        ..TestProvider::default()
    }));

    let result = models
        .refresh(ModelsRefreshOptions {
            signal: Some(controller.signal()),
            ..ModelsRefreshOptions::default()
        })
        .await;
    assert!(result.aborted);
    wait_for_refresh_token(&credentials, "new-refresh").await;
}

#[tokio::test]
async fn always_gives_providers_a_concrete_signal() {
    let received: Arc<Mutex<Option<AbortSignal>>> = Arc::default();
    let models = create_models(CreateModelsOptions::default());
    let record = Arc::clone(&received);
    models.set_provider(test_provider(TestProvider {
        id: "dynamic".into(),
        refresh_models: Some(Arc::new(move |context| {
            *record.lock().unwrap_or_else(PoisonError::into_inner) = Some(context.signal);
            Box::pin(async { Ok(()) })
        })),
        ..TestProvider::default()
    }));

    let result = models.refresh(ModelsRefreshOptions::default()).await;
    assert!(!result.aborted);
    let signal = received
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("signal");
    assert!(!signal.aborted());
}

/// Records the signal of every storage call.
struct SignalRecordingStore {
    signals: Arc<Mutex<Vec<Option<AbortSignal>>>>,
}

impl ModelsStore for SignalRecordingStore {
    fn read(
        &self,
        _id: &str,
        options: ModelsStoreOperationOptions,
    ) -> BoxFuture<'_, Result<Option<ModelsStoreEntry>, Thrown>> {
        self.signals
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(options.signal);
        Box::pin(async { Ok(None) })
    }
    fn write(
        &self,
        _id: &str,
        _entry: ModelsStoreEntry,
        options: ModelsStoreOperationOptions,
    ) -> BoxFuture<'_, Result<(), Thrown>> {
        self.signals
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(options.signal);
        Box::pin(async { Ok(()) })
    }
    fn delete(
        &self,
        _id: &str,
        options: ModelsStoreOperationOptions,
    ) -> BoxFuture<'_, Result<(), Thrown>> {
        self.signals
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(options.signal);
        Box::pin(async { Ok(()) })
    }
}

#[tokio::test]
async fn binds_model_store_waits_to_the_provider_refresh_signal() {
    let signals: Arc<Mutex<Vec<Option<AbortSignal>>>> = Arc::default();
    let provider_signal: Arc<Mutex<Option<AbortSignal>>> = Arc::default();
    let models = create_models(CreateModelsOptions {
        models_store: Some(Arc::new(SignalRecordingStore {
            signals: Arc::clone(&signals),
        })),
        ..CreateModelsOptions::default()
    });
    let record = Arc::clone(&provider_signal);
    models.set_provider(test_provider(TestProvider {
        id: "dynamic".into(),
        auth: Some(ProviderAuth {
            api_key: Some(env_key_auth(Some("key")).arc()),
            oauth: None,
        }),
        refresh_models: Some(Arc::new(move |context| {
            let record = Arc::clone(&record);
            Box::pin(async move {
                *record.lock().unwrap_or_else(PoisonError::into_inner) =
                    Some(context.signal.clone());
                if !context.allow_network {
                    return Ok(());
                }
                context
                    .publish(ModelsPublication {
                        persist: ModelsPersistence::Write(ModelsStoreEntry {
                            models: vec![AnyModel::Chat(test_model("dynamic", "fresh"))],
                            ..ModelsStoreEntry::default()
                        }),
                        update: None,
                    })
                    .await?;
                Ok(())
            })
        })),
        ..TestProvider::default()
    }));

    let result = models
        .refresh(ModelsRefreshOptions {
            providers: Some(vec!["dynamic".into()]),
            ..ModelsRefreshOptions::default()
        })
        .await;

    assert_eq!(result.errors.len(), 0);
    let signals = signals
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    assert_eq!(signals.len(), 3);
    let provider_signal = provider_signal
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("signal");
    assert!(signals.iter().all(|signal| signal
        .as_ref()
        .is_some_and(|signal| signal.same(&provider_signal))));
}

#[tokio::test]
async fn returns_aborted_state_without_reporting_cancellation_as_a_provider_error() {
    let controller = AbortController::new();
    let models = create_models(CreateModelsOptions::default());
    let aborter = controller.clone();
    models.set_provider(test_provider(TestProvider {
        id: "dynamic".into(),
        refresh_models: Some(Arc::new(move |_context| {
            aborter.abort(None);
            Box::pin(async { Ok(()) })
        })),
        ..TestProvider::default()
    }));

    let result = models
        .refresh(ModelsRefreshOptions {
            signal: Some(controller.signal()),
            ..ModelsRefreshOptions::default()
        })
        .await;
    assert!(result.aborted);
    assert_eq!(result.errors.len(), 0);
}

#[tokio::test]
async fn stops_waiting_on_abort_when_a_provider_ignores_its_signal() {
    let controller = AbortController::new();
    let started = Arc::new(Notify::new());
    let (reject_tx, reject_rx) = oneshot::channel::<Thrown>();
    let reject_rx = Arc::new(tokio::sync::Mutex::new(Some(reject_rx)));
    let calls = Arc::new(AtomicUsize::new(0));
    let models = create_models(CreateModelsOptions::default());
    let (mark, rx, count) = (
        Arc::clone(&started),
        Arc::clone(&reject_rx),
        Arc::clone(&calls),
    );
    models.set_provider(test_provider(TestProvider {
        id: "dynamic".into(),
        refresh_models: Some(Arc::new(move |_context| {
            let (mark, rx, count) = (Arc::clone(&mark), Arc::clone(&rx), Arc::clone(&count));
            Box::pin(async move {
                if count.fetch_add(1, Ordering::SeqCst) != 0 {
                    return Ok(());
                }
                mark.notify_one();
                let receiver = rx.lock().await.take().expect("first call");
                match receiver.await {
                    Ok(error) => Err(error),
                    Err(_) => Ok(()),
                }
            })
        })),
        ..TestProvider::default()
    }));

    let refreshing = models.clone();
    let signal = controller.signal();
    let pending = tokio::spawn(async move {
        refreshing
            .refresh(ModelsRefreshOptions {
                signal: Some(signal),
                ..ModelsRefreshOptions::default()
            })
            .await
    });
    started.notified().await;
    controller.abort(None);

    let result = pending.await.expect("join");
    assert!(result.aborted);
    assert_eq!(result.errors.len(), 0);

    let _ = reject_tx.send(common::error("late provider failure"));
    tokio::task::yield_now().await;
    assert_eq!(result.errors.len(), 0);
}

#[tokio::test]
async fn rejects_late_publication_from_a_superseded_non_cooperative_provider() {
    let store = Arc::new(InMemoryModelsStore::new());
    let state = Arc::new(Mutex::new("initial".to_owned()));
    let calls = Arc::new(AtomicUsize::new(0));
    let first_started = Arc::new(Notify::new());
    let finish_first = Arc::new(Notify::new());
    let models = create_models(CreateModelsOptions {
        models_store: Some(store.clone()),
        ..CreateModelsOptions::default()
    });
    let (state_ref, count, started, finish) = (
        Arc::clone(&state),
        Arc::clone(&calls),
        Arc::clone(&first_started),
        Arc::clone(&finish_first),
    );
    models.set_provider(test_provider(TestProvider {
        id: "dynamic".into(),
        refresh_models: Some(Arc::new(move |context| {
            let (state, count, started, finish) = (
                Arc::clone(&state_ref),
                Arc::clone(&count),
                Arc::clone(&started),
                Arc::clone(&finish),
            );
            Box::pin(async move {
                if !context.allow_network {
                    return Ok(());
                }
                let current = count.fetch_add(1, Ordering::SeqCst) + 1;
                if current == 1 {
                    started.notify_one();
                    finish.notified().await;
                }
                let value = format!("generation-{current}");
                let update_value = value.clone();
                context
                    .publish(ModelsPublication {
                        persist: ModelsPersistence::Write(ModelsStoreEntry {
                            models: vec![AnyModel::Chat(test_model("dynamic", &value))],
                            ..ModelsStoreEntry::default()
                        }),
                        update: Some(Box::new(move || {
                            *state.lock().unwrap_or_else(PoisonError::into_inner) = update_value;
                        })),
                    })
                    .await?;
                Ok(())
            })
        })),
        ..TestProvider::default()
    }));

    let first_models = models.clone();
    let first = tokio::spawn(async move {
        first_models
            .refresh(ModelsRefreshOptions {
                providers: Some(vec!["dynamic".into()]),
                ..ModelsRefreshOptions::default()
            })
            .await
    });
    first_started.notified().await;
    models
        .refresh(ModelsRefreshOptions {
            providers: Some(vec!["dynamic".into()]),
            ..ModelsRefreshOptions::default()
        })
        .await;
    first.await.expect("join");
    finish_first.notify_one();
    for _ in 0..100 {
        tokio::task::yield_now().await;
    }

    assert_eq!(
        *state.lock().unwrap_or_else(PoisonError::into_inner),
        "generation-2"
    );
    let stored = store
        .read("dynamic", ModelsStoreOperationOptions::default())
        .await
        .expect("read")
        .expect("entry");
    assert_eq!(stored.models[0].id(), "generation-2");
}

#[tokio::test]
async fn produces_an_error_stream_for_unknown_providers_instead_of_throwing() {
    let models = create_models(CreateModelsOptions::default());
    let result = models
        .complete_simple(
            &test_model("ghost", "model-a"),
            context(),
            SimpleStreamOptions::default().into(),
        )
        .await;
    assert_eq!(result.stop_reason, StopReason::Error);
    assert!(result
        .error_message
        .expect("message")
        .contains("Unknown provider: ghost"));
}

#[tokio::test]
async fn streams_through_the_provider() {
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        ..TestProvider::default()
    }));
    let model = test_model("p1", "model-a");

    let stream = models.stream_simple(&model, context(), SimpleStreamOptions::default().into());
    let events: Vec<&'static str> = stream
        .events()
        .map(|event| event.type_name())
        .collect()
        .await;
    assert_eq!(events, ["start", "done"]);
    let message = stream.result().await;
    assert_eq!(message.stop_reason, StopReason::Stop);
}
