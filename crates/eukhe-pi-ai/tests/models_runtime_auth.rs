//! Port of `test/models-runtime.test.ts`: auth, login, and request-option
//! cases.

mod common;

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use common::{
    api_key, calls, context, env_key_auth, now_f64, oauth, recorded, store, test_model,
    test_provider, FnApiKeyAuth, TestOAuth, TestProvider,
};
use eukhe_chord::context::{AbortController, AbortError, AbortSignal};
use eukhe_pi_ai::auth::{
    ApiKeyCredential, AuthCheck, AuthEvent, AuthInteraction, AuthOperationOptions, AuthPrompt,
    AuthResolutionOverrides, AuthResult, AuthType, Credential, CredentialInfo, CredentialStore,
    InMemoryCredentialStore, ModelAuth, ModifyFn, OAuthCredential, ProviderAuth,
};
use eukhe_pi_ai::models::{
    create_models, CreateModelsOptions, ModelsError, ModelsErrorCode, ModelsRequestOptions,
};
use eukhe_pi_ai::types::{ProviderEnv, SimpleStreamOptions};
use eukhe_pi_ai::utils::diagnostics::Thrown;
use eukhe_types::pi_ai::{AnyModel, IndexMap, ProviderHeaders, StopReason};
use futures::future::BoxFuture;
use tokio::sync::Notify;

fn code(error: &Thrown) -> ModelsErrorCode {
    error
        .downcast_ref::<ModelsError>()
        .expect("ModelsError")
        .code
}

fn is_abort(error: &Thrown) -> bool {
    error.is::<AbortError>()
}

fn with_signal(signal: &AbortSignal) -> AuthOperationOptions {
    AuthOperationOptions::with_signal(signal.clone())
}

struct TestInteraction {
    signal: Option<AbortSignal>,
}

impl AuthInteraction for TestInteraction {
    fn signal(&self) -> Option<AbortSignal> {
        self.signal.clone()
    }
    fn prompt(&self, _prompt: AuthPrompt) -> BoxFuture<'_, Result<String, Thrown>> {
        Box::pin(async { Ok("unused".to_owned()) })
    }
    fn notify(&self, _event: AuthEvent) {}
}

fn headers(entries: &[(&str, &str)]) -> ProviderHeaders {
    entries
        .iter()
        .map(|(name, value)| ((*name).to_owned(), Some((*value).to_owned())))
        .collect()
}

#[tokio::test]
async fn passes_caller_signals_to_provider_auth_callbacks() {
    let controller = AbortController::new();
    let received: Arc<Mutex<Vec<AbortSignal>>> = Arc::default();
    let (login_seen, check_seen, resolve_seen) = (
        Arc::clone(&received),
        Arc::clone(&received),
        Arc::clone(&received),
    );
    let auth = FnApiKeyAuth::new("Signal auth", move |input| {
        resolve_seen
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(input.signal);
        async {
            Ok(Some(AuthResult {
                auth: ModelAuth {
                    api_key: Some("resolved".into()),
                    ..ModelAuth::default()
                },
                ..AuthResult::default()
            }))
        }
    })
    .with_check(move |input| {
        check_seen
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(input.signal);
        async {
            Ok(Some(AuthCheck {
                source: None,
                kind: AuthType::ApiKey,
            }))
        }
    })
    .with_login(move |interaction| {
        login_seen
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(interaction.signal);
        async { Ok(ApiKeyCredential::with_key("saved")) }
    });
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        auth: Some(ProviderAuth {
            api_key: Some(auth.arc()),
            oauth: None,
        }),
        ..TestProvider::default()
    }));

    models
        .check_auth("p1", with_signal(&controller.signal()))
        .await
        .expect("check");
    models
        .get_auth(
            "p1",
            AuthResolutionOverrides {
                signal: Some(controller.signal()),
                ..AuthResolutionOverrides::default()
            },
        )
        .await
        .expect("auth");
    models
        .login(
            "p1",
            AuthType::ApiKey,
            Arc::new(TestInteraction {
                signal: Some(controller.signal()),
            }),
            None,
        )
        .await
        .expect("login");

    let received = received
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    assert_eq!(received.len(), 3);
    assert!(received
        .iter()
        .all(|signal| signal.same(&controller.signal())));
}

#[tokio::test]
async fn stops_waiting_for_non_cooperative_auth_callbacks() {
    let check_started = Arc::new(Notify::new());
    let finish_check = Arc::new(Notify::new());
    let resolve_started = Arc::new(Notify::new());
    let finish_resolve = Arc::new(Notify::new());
    let (cs, cf, rs, rf) = (
        Arc::clone(&check_started),
        Arc::clone(&finish_check),
        Arc::clone(&resolve_started),
        Arc::clone(&finish_resolve),
    );
    let auth = FnApiKeyAuth::new("Blocked auth", move |_| {
        let (started, finish) = (Arc::clone(&rs), Arc::clone(&rf));
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
    .with_check(move |_| {
        let (started, finish) = (Arc::clone(&cs), Arc::clone(&cf));
        async move {
            started.notify_one();
            finish.notified().await;
            Ok(Some(AuthCheck {
                source: None,
                kind: AuthType::ApiKey,
            }))
        }
    });
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        auth: Some(ProviderAuth {
            api_key: Some(auth.arc()),
            oauth: None,
        }),
        ..TestProvider::default()
    }));

    let available_controller = AbortController::new();
    let available_models = models.clone();
    let available_signal = available_controller.signal();
    let available = tokio::spawn(async move {
        available_models
            .get_available(None, with_signal(&available_signal))
            .await
    });
    check_started.notified().await;
    available_controller.abort(None);
    assert!(is_abort(
        &available.await.expect("join").expect_err("aborted")
    ));

    let auth_controller = AbortController::new();
    let auth_models = models.clone();
    let auth_signal = auth_controller.signal();
    let auth = tokio::spawn(async move {
        auth_models
            .get_auth(
                "p1",
                AuthResolutionOverrides {
                    signal: Some(auth_signal),
                    ..AuthResolutionOverrides::default()
                },
            )
            .await
    });
    resolve_started.notified().await;
    auth_controller.abort(None);
    assert!(is_abort(&auth.await.expect("join").expect_err("aborted")));

    finish_check.notify_one();
    finish_resolve.notify_one();
}

#[tokio::test]
async fn cancels_queued_credential_mutations_without_running_them_later() {
    let credentials = Arc::new(InMemoryCredentialStore::new());
    let finish_first = Arc::new(Notify::new());
    let second_ran = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let finish = Arc::clone(&finish_first);
    let first_fn: ModifyFn = Box::new(move |_| {
        Box::pin(async move {
            finish.notified().await;
            Ok(Some(api_key("first")))
        })
    });
    let first_store = Arc::clone(&credentials);
    let first = tokio::spawn(async move {
        first_store
            .modify("p1", first_fn, AuthOperationOptions::default())
            .await
    });
    tokio::task::yield_now().await;
    let controller = AbortController::new();
    let ran = Arc::clone(&second_ran);
    let second_fn: ModifyFn = Box::new(move |_| {
        ran.store(true, Ordering::SeqCst);
        Box::pin(async { Ok(Some(api_key("second"))) })
    });
    let second_store = Arc::clone(&credentials);
    let signal = controller.signal();
    let second = tokio::spawn(async move {
        second_store
            .modify("p1", second_fn, with_signal(&signal))
            .await
    });
    tokio::task::yield_now().await;

    controller.abort(None);
    assert!(is_abort(&second.await.expect("join").expect_err("aborted")));
    finish_first.notify_one();
    first.await.expect("join").expect("first");
    tokio::task::yield_now().await;

    assert!(!second_ran.load(Ordering::SeqCst));
    assert_eq!(
        credentials
            .read("p1", AuthOperationOptions::default())
            .await
            .expect("read"),
        Some(api_key("first"))
    );
}

async fn wait_for_refresh_token(credentials: &InMemoryCredentialStore, expected: &str) {
    for _ in 0..1000 {
        if let Ok(Some(Credential::OAuth(credential))) = credentials
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

// Radius bug report 01a10855-43d8-7447-a710-2acf5ee0b2ee:
// refresh_token_invalidated after a cancelled refresh.
#[tokio::test]
async fn persists_an_oauth_refresh_that_started_before_the_request_was_cancelled() {
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
                    // The provider has rotated old-refresh by the time the
                    // request is cancelled.
                    aborter.abort(None);
                    async move {
                        Ok(OAuthCredential {
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
        ..TestProvider::default()
    }));

    let result = models
        .get_auth(
            "p1",
            AuthResolutionOverrides {
                signal: Some(controller.signal()),
                ..AuthResolutionOverrides::default()
            },
        )
        .await;
    assert!(is_abort(&result.expect_err("aborted")));
    wait_for_refresh_token(&credentials, "new-refresh").await;
}

fn api_key_of(result: Option<AuthResult>) -> Option<String> {
    result.and_then(|result| result.auth.api_key)
}

#[tokio::test]
async fn resolves_auth_stored_credential_owns_the_provider_ambient_only_when_nothing_stored() {
    let credentials = Arc::new(InMemoryCredentialStore::new());
    let models = create_models(CreateModelsOptions {
        credentials: Some(credentials.clone()),
        ..CreateModelsOptions::default()
    });
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        auth: Some(ProviderAuth {
            api_key: Some(env_key_auth(Some("env-key")).arc()),
            oauth: Some(TestOAuth::new().arc()),
        }),
        ..TestProvider::default()
    }));
    let model = test_model("p1", "model-a");

    // model and provider-id overloads resolve the same provider-scoped auth
    let none = AuthResolutionOverrides::default;
    assert_eq!(
        api_key_of(
            models
                .get_auth_for_model(&model, none())
                .await
                .expect("auth")
        )
        .as_deref(),
        Some("env-key")
    );
    assert_eq!(
        api_key_of(models.get_auth("p1", none()).await.expect("auth")).as_deref(),
        Some("env-key")
    );
    let explicit = AuthResolutionOverrides {
        api_key: Some("explicit-key".into()),
        ..AuthResolutionOverrides::default()
    };
    assert_eq!(
        api_key_of(
            models
                .get_auth_for_model(&model, explicit)
                .await
                .expect("auth")
        )
        .as_deref(),
        Some("explicit-key")
    );

    // stored oauth credential (persisted via the single write path): beats ambient env
    store(
        credentials.as_ref(),
        "p1",
        oauth("oauth-token", "r", now_f64() + 10.0 * 60_000.0),
    )
    .await;
    let resolution = models
        .get_auth("p1", none())
        .await
        .expect("auth")
        .expect("configured");
    assert_eq!(resolution.auth.api_key.as_deref(), Some("oauth-token"));
    assert_eq!(resolution.source.as_deref(), Some("OAuth"));

    // stored api-key credential resolves through apiKey auth, beats env
    store(credentials.as_ref(), "p1", api_key("stored-key")).await;
    let api_key_resolution = models
        .get_auth("p1", none())
        .await
        .expect("auth")
        .expect("configured");
    assert_eq!(
        api_key_resolution.auth.api_key.as_deref(),
        Some("stored-key")
    );
    assert_eq!(api_key_resolution.source.as_deref(), Some("stored"));
}

#[tokio::test]
async fn checks_provider_auth_without_refreshing_oauth_and_filters_available_models() {
    let credentials = Arc::new(InMemoryCredentialStore::new());
    let refreshes = Arc::new(AtomicUsize::new(0));
    let models = create_models(CreateModelsOptions {
        credentials: Some(credentials.clone()),
        ..CreateModelsOptions::default()
    });
    models.set_provider(test_provider(TestProvider {
        id: "ambient".into(),
        auth: Some(ProviderAuth {
            api_key: Some(env_key_auth(Some("env-key")).arc()),
            oauth: None,
        }),
        ..TestProvider::default()
    }));
    models.set_provider(test_provider(TestProvider {
        id: "missing".into(),
        auth: Some(ProviderAuth {
            api_key: Some(env_key_auth(None).arc()),
            oauth: None,
        }),
        ..TestProvider::default()
    }));
    let counter = Arc::clone(&refreshes);
    models.set_provider(test_provider(TestProvider {
        id: "oauth".into(),
        auth: Some(ProviderAuth {
            api_key: None,
            oauth: Some(
                TestOAuth::with_refresh(move |credential| {
                    counter.fetch_add(1, Ordering::SeqCst);
                    async move { Ok(credential) }
                })
                .arc(),
            ),
        }),
        ..TestProvider::default()
    }));
    store(
        credentials.as_ref(),
        "oauth",
        oauth("expired", "refresh", 0.0),
    )
    .await;

    let default = AuthOperationOptions::default;
    assert_eq!(
        models
            .check_auth("ambient", default())
            .await
            .expect("check"),
        Some(AuthCheck {
            source: Some("env".into()),
            kind: AuthType::ApiKey,
        })
    );
    assert_eq!(
        models
            .check_auth("missing", default())
            .await
            .expect("check"),
        None
    );
    assert_eq!(
        models.check_auth("oauth", default()).await.expect("check"),
        Some(AuthCheck {
            source: Some("OAuth".into()),
            kind: AuthType::OAuth,
        })
    );
    assert_eq!(refreshes.load(Ordering::SeqCst), 0);
    let providers = |models: Vec<eukhe_types::pi_ai::Model>| -> Vec<String> {
        models.into_iter().map(|model| model.provider).collect()
    };
    assert_eq!(
        providers(
            models
                .get_available(None, default())
                .await
                .expect("available")
        ),
        ["ambient", "oauth"]
    );
    assert_eq!(
        providers(
            models
                .get_available(Some("ambient"), default())
                .await
                .expect("available")
        ),
        ["ambient"]
    );
}

#[tokio::test]
async fn runs_provider_login_and_logout_through_the_credential_store() {
    let credentials = Arc::new(InMemoryCredentialStore::new());
    let auth =
        env_key_auth(None).with_login(|_| async { Ok(ApiKeyCredential::with_key("logged-in")) });
    let models = create_models(CreateModelsOptions {
        credentials: Some(credentials.clone()),
        ..CreateModelsOptions::default()
    });
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        auth: Some(ProviderAuth {
            api_key: Some(auth.arc()),
            oauth: None,
        }),
        ..TestProvider::default()
    }));

    let credential = models
        .login(
            "p1",
            AuthType::ApiKey,
            Arc::new(TestInteraction { signal: None }),
            None,
        )
        .await
        .expect("login");
    assert_eq!(credential, api_key("logged-in"));
    assert_eq!(
        credentials
            .read("p1", AuthOperationOptions::default())
            .await
            .expect("read"),
        Some(credential)
    );

    models
        .logout("p1", AuthOperationOptions::default())
        .await
        .expect("logout");
    assert_eq!(
        credentials
            .read("p1", AuthOperationOptions::default())
            .await
            .expect("read"),
        None
    );
}

#[tokio::test]
async fn a_stored_credential_without_a_matching_handler_blocks_ambient_fallback() {
    let credentials = Arc::new(InMemoryCredentialStore::new());
    let models = create_models(CreateModelsOptions {
        credentials: Some(credentials.clone()),
        ..CreateModelsOptions::default()
    });
    // provider has only apiKey auth, but an oauth credential is stored (stale config)
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        auth: Some(ProviderAuth {
            api_key: Some(env_key_auth(Some("env-key")).arc()),
            oauth: None,
        }),
        ..TestProvider::default()
    }));
    store(credentials.as_ref(), "p1", oauth("a", "r", 0.0)).await;

    assert_eq!(
        models
            .get_auth("p1", AuthResolutionOverrides::default())
            .await
            .expect("auth"),
        None
    );
}

#[tokio::test]
async fn refreshes_expired_oauth_credentials_and_persists_the_rotated_credential() {
    let credentials = Arc::new(InMemoryCredentialStore::new());
    let oauth_auth = TestOAuth::with_refresh(|credential| async move {
        Ok(OAuthCredential {
            access: "new-token".into(),
            expires: now_f64() + 60.0 * 60_000.0,
            ..credential
        })
    });
    let models = create_models(CreateModelsOptions {
        credentials: Some(credentials.clone()),
        ..CreateModelsOptions::default()
    });
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        auth: Some(ProviderAuth {
            api_key: None,
            oauth: Some(oauth_auth.arc()),
        }),
        ..TestProvider::default()
    }));
    store(credentials.as_ref(), "p1", oauth("old-token", "r", 0.0)).await;

    let resolution = models
        .get_auth("p1", AuthResolutionOverrides::default())
        .await
        .expect("auth");
    assert_eq!(api_key_of(resolution).as_deref(), Some("new-token"));
    let Some(Credential::OAuth(stored)) = credentials
        .read("p1", AuthOperationOptions::default())
        .await
        .expect("read")
    else {
        panic!("oauth");
    };
    assert_eq!(stored.access, "new-token");
}

fn counting_refresh(counter: &Arc<AtomicUsize>) -> TestOAuth {
    let counter = Arc::clone(counter);
    TestOAuth::with_refresh(move |credential| {
        counter.fetch_add(1, Ordering::SeqCst);
        async move {
            Ok(OAuthCredential {
                access: "new-token".into(),
                expires: now_f64() + 60.0 * 60_000.0,
                ..credential
            })
        }
    })
}

#[tokio::test]
async fn refreshes_oauth_credentials_with_less_than_five_minutes_remaining() {
    let credentials = Arc::new(InMemoryCredentialStore::new());
    let refreshes = Arc::new(AtomicUsize::new(0));
    let models = create_models(CreateModelsOptions {
        credentials: Some(credentials.clone()),
        ..CreateModelsOptions::default()
    });
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        auth: Some(ProviderAuth {
            api_key: None,
            oauth: Some(counting_refresh(&refreshes).arc()),
        }),
        ..TestProvider::default()
    }));
    store(
        credentials.as_ref(),
        "p1",
        oauth("old-token", "r", now_f64() + 60_000.0),
    )
    .await;

    let resolution = models
        .get_auth("p1", AuthResolutionOverrides::default())
        .await
        .expect("auth");
    assert_eq!(api_key_of(resolution).as_deref(), Some("new-token"));
    assert_eq!(refreshes.load(Ordering::SeqCst), 1);
}

#[tokio::test]
async fn honors_a_callers_longer_oauth_minimum_validity() {
    let credentials = Arc::new(InMemoryCredentialStore::new());
    let refreshes = Arc::new(AtomicUsize::new(0));
    let models = create_models(CreateModelsOptions {
        credentials: Some(credentials.clone()),
        ..CreateModelsOptions::default()
    });
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        auth: Some(ProviderAuth {
            api_key: None,
            oauth: Some(counting_refresh(&refreshes).arc()),
        }),
        ..TestProvider::default()
    }));
    store(
        credentials.as_ref(),
        "p1",
        oauth("old-token", "r", now_f64() + 10.0 * 60_000.0),
    )
    .await;

    let resolution = models
        .get_auth(
            "p1",
            AuthResolutionOverrides {
                min_oauth_validity_ms: Some(30.0 * 60_000.0),
                ..AuthResolutionOverrides::default()
            },
        )
        .await
        .expect("auth");
    assert_eq!(api_key_of(resolution).as_deref(), Some("new-token"));
    assert_eq!(refreshes.load(Ordering::SeqCst), 1);
}

#[tokio::test]
async fn rejects_with_code_oauth_when_refresh_fails_preserving_the_stored_credential() {
    let credentials = Arc::new(InMemoryCredentialStore::new());
    let models = create_models(CreateModelsOptions {
        credentials: Some(credentials.clone()),
        ..CreateModelsOptions::default()
    });
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        auth: Some(ProviderAuth {
            api_key: None,
            oauth: Some(
                TestOAuth::with_refresh(|_| async { Err(common::error("invalid_grant")) }).arc(),
            ),
        }),
        ..TestProvider::default()
    }));
    store(credentials.as_ref(), "p1", oauth("old", "r", 0.0)).await;

    let error = models
        .get_auth("p1", AuthResolutionOverrides::default())
        .await
        .expect_err("oauth");
    assert_eq!(code(&error), ModelsErrorCode::Oauth);
    // credential preserved for retry / re-login
    let Some(Credential::OAuth(stored)) = credentials
        .read("p1", AuthOperationOptions::default())
        .await
        .expect("read")
    else {
        panic!("oauth");
    };
    assert_eq!(stored.access, "old");
}

#[tokio::test]
async fn serializes_concurrent_oauth_refreshes_through_store_modify_no_double_refresh() {
    let credentials = Arc::new(InMemoryCredentialStore::new());
    store(credentials.as_ref(), "p1", oauth("old", "r1", 0.0)).await;
    let refreshes = Arc::new(AtomicUsize::new(0));
    let counter = Arc::clone(&refreshes);
    let oauth_auth = TestOAuth::with_refresh(move |_| {
        let count = counter.fetch_add(1, Ordering::SeqCst) + 1;
        async move {
            tokio::task::yield_now().await;
            Ok(OAuthCredential::new(
                "r2",
                format!("new-{count}"),
                now_f64() + 60.0 * 60_000.0,
            ))
        }
    });
    let models = create_models(CreateModelsOptions {
        credentials: Some(credentials.clone()),
        ..CreateModelsOptions::default()
    });
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        auth: Some(ProviderAuth {
            api_key: None,
            oauth: Some(oauth_auth.arc()),
        }),
        ..TestProvider::default()
    }));

    let (a, b) = tokio::join!(
        models.get_auth("p1", AuthResolutionOverrides::default()),
        models.get_auth("p1", AuthResolutionOverrides::default())
    );
    assert_eq!(refreshes.load(Ordering::SeqCst), 1);
    assert_eq!(api_key_of(a.expect("a")).as_deref(), Some("new-1"));
    assert_eq!(api_key_of(b.expect("b")).as_deref(), Some("new-1"));
}

/// Counts `modify` calls of an in-memory store.
struct CountingStore {
    base: InMemoryCredentialStore,
    modifies: Arc<AtomicUsize>,
}

impl CredentialStore for CountingStore {
    fn read<'a>(
        &'a self,
        provider_id: &'a str,
        options: AuthOperationOptions,
    ) -> BoxFuture<'a, Result<Option<Credential>, Thrown>> {
        self.base.read(provider_id, options)
    }
    fn list(
        &self,
        options: AuthOperationOptions,
    ) -> BoxFuture<'_, Result<Vec<CredentialInfo>, Thrown>> {
        self.base.list(options)
    }
    fn modify<'a>(
        &'a self,
        provider_id: &'a str,
        f: ModifyFn,
        options: AuthOperationOptions,
    ) -> BoxFuture<'a, Result<Option<Credential>, Thrown>> {
        self.modifies.fetch_add(1, Ordering::SeqCst);
        self.base.modify(provider_id, f, options)
    }
    fn delete<'a>(
        &'a self,
        provider_id: &'a str,
        options: AuthOperationOptions,
    ) -> BoxFuture<'a, Result<(), Thrown>> {
        self.base.delete(provider_id, options)
    }
}

#[tokio::test]
async fn valid_oauth_tokens_resolve_without_touching_modify() {
    let modifies = Arc::new(AtomicUsize::new(0));
    let base = InMemoryCredentialStore::new();
    store(
        &base,
        "p1",
        oauth("valid", "r", now_f64() + 10.0 * 60_000.0),
    )
    .await;
    let models = create_models(CreateModelsOptions {
        credentials: Some(Arc::new(CountingStore {
            base,
            modifies: Arc::clone(&modifies),
        })),
        ..CreateModelsOptions::default()
    });
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        auth: Some(ProviderAuth {
            api_key: None,
            oauth: Some(TestOAuth::new().arc()),
        }),
        ..TestProvider::default()
    }));

    let resolution = models
        .get_auth("p1", AuthResolutionOverrides::default())
        .await
        .expect("auth");
    assert_eq!(api_key_of(resolution).as_deref(), Some("valid"));
    assert_eq!(modifies.load(Ordering::SeqCst), 0);
}

/// A store whose reads or modifications fail.
struct FailingStore {
    stored: Option<Credential>,
    fail_read: bool,
}

impl CredentialStore for FailingStore {
    fn read<'a>(
        &'a self,
        _id: &'a str,
        _options: AuthOperationOptions,
    ) -> BoxFuture<'a, Result<Option<Credential>, Thrown>> {
        let result = if self.fail_read {
            Err(common::error("disk on fire"))
        } else {
            Ok(self.stored.clone())
        };
        Box::pin(async move { result })
    }
    fn list(
        &self,
        _options: AuthOperationOptions,
    ) -> BoxFuture<'_, Result<Vec<CredentialInfo>, Thrown>> {
        Box::pin(async { Ok(Vec::new()) })
    }
    fn modify<'a>(
        &'a self,
        _id: &'a str,
        _f: ModifyFn,
        _options: AuthOperationOptions,
    ) -> BoxFuture<'a, Result<Option<Credential>, Thrown>> {
        let result = if self.fail_read {
            Ok(None)
        } else {
            Err(common::error("disk on fire"))
        };
        Box::pin(async move { result })
    }
    fn delete<'a>(
        &'a self,
        _id: &'a str,
        _options: AuthOperationOptions,
    ) -> BoxFuture<'a, Result<(), Thrown>> {
        Box::pin(async { Ok(()) })
    }
}

#[tokio::test]
async fn wraps_credential_store_failures_in_models_error() {
    // read failure
    let models = create_models(CreateModelsOptions {
        credentials: Some(Arc::new(FailingStore {
            stored: None,
            fail_read: true,
        })),
        ..CreateModelsOptions::default()
    });
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        auth: Some(ProviderAuth {
            api_key: Some(env_key_auth(Some("env-key")).arc()),
            oauth: None,
        }),
        ..TestProvider::default()
    }));
    let error = models
        .get_auth("p1", AuthResolutionOverrides::default())
        .await
        .expect_err("auth");
    assert_eq!(code(&error), ModelsErrorCode::Auth);

    // modify failure during refresh
    let oauth_models = create_models(CreateModelsOptions {
        credentials: Some(Arc::new(FailingStore {
            stored: Some(oauth("old", "r", 0.0)),
            fail_read: false,
        })),
        ..CreateModelsOptions::default()
    });
    oauth_models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        auth: Some(ProviderAuth {
            api_key: None,
            oauth: Some(TestOAuth::new().arc()),
        }),
        ..TestProvider::default()
    }));
    let error = oauth_models
        .get_auth("p1", AuthResolutionOverrides::default())
        .await
        .expect_err("auth");
    assert_eq!(code(&error), ModelsErrorCode::Auth);
}

#[tokio::test]
async fn keeps_the_underlying_reason_in_wrapped_oauth_refresh_errors() {
    let credentials = Arc::new(InMemoryCredentialStore::new());
    store(credentials.as_ref(), "p1", oauth("old", "r", 0.0)).await;
    let models = create_models(CreateModelsOptions {
        credentials: Some(credentials),
        ..CreateModelsOptions::default()
    });
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        auth: Some(ProviderAuth {
            api_key: None,
            oauth: Some(
                TestOAuth::with_refresh(|_| async {
                    Err(common::error("token refresh failed (400): invalid_grant"))
                })
                .arc(),
            ),
        }),
        ..TestProvider::default()
    }));

    let error = models
        .get_auth("p1", AuthResolutionOverrides::default())
        .await
        .expect_err("oauth");
    assert!(error
        .to_string()
        .contains("OAuth refresh failed for p1: token refresh failed (400): invalid_grant"));
}

#[tokio::test]
async fn wraps_api_key_auth_failures_in_models_error() {
    let failing = FnApiKeyAuth::new("Failing", |_| async { Err(common::error("nope")) });
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        auth: Some(ProviderAuth {
            api_key: Some(failing.arc()),
            oauth: None,
        }),
        ..TestProvider::default()
    }));
    let error = models
        .get_auth("p1", AuthResolutionOverrides::default())
        .await
        .expect_err("auth");
    assert_eq!(code(&error), ModelsErrorCode::Auth);
}

#[tokio::test]
async fn uses_explicit_request_api_key_and_env_during_provider_auth_resolution() {
    let recorded_calls = calls();
    let auth = FnApiKeyAuth::new("Scoped", |input| async move {
        let account = match input
            .credential
            .as_ref()
            .and_then(|credential| credential.env.as_ref())
            .and_then(|env| env.get("ACCOUNT_ID"))
        {
            Some(account) => Some(account.clone()),
            None => input.ctx.env("ACCOUNT_ID").await,
        };
        let (Some(key), Some(account)) = (
            input
                .credential
                .as_ref()
                .and_then(|credential| credential.key.clone()),
            account,
        ) else {
            return Ok(None);
        };
        Ok(Some(AuthResult {
            auth: ModelAuth {
                api_key: Some(key),
                base_url: Some(format!("https://example.test/{account}")),
                ..ModelAuth::default()
            },
            env: Some(ProviderEnv::from([("ACCOUNT_ID".to_owned(), account)])),
            source: None,
        }))
    });
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        auth: Some(ProviderAuth {
            api_key: Some(auth.arc()),
            oauth: None,
        }),
        calls: Some(recorded_calls.clone()),
        ..TestProvider::default()
    }));
    let model = test_model("p1", "model-a");

    let mut options = SimpleStreamOptions::default();
    options.stream.request.api_key = Some("explicit-key".into());
    options.stream.request.env = Some(ProviderEnv::from([(
        "ACCOUNT_ID".to_owned(),
        "acct".to_owned(),
    )]));
    models
        .complete_simple(&model, context(), options.into())
        .await;

    let calls = recorded(&recorded_calls);
    assert_eq!(calls[0].model.base_url, "https://example.test/acct");
    assert_eq!(
        calls[0].options.request.api_key.as_deref(),
        Some("explicit-key")
    );
    assert_eq!(
        calls[0].options.request.env,
        Some(ProviderEnv::from([(
            "ACCOUNT_ID".to_owned(),
            "acct".to_owned()
        )]))
    );
}

#[tokio::test]
async fn merges_resolved_auth_into_stream_options_explicit_options_win_per_field() {
    let recorded_calls = calls();
    let auth = FnApiKeyAuth::new("Test", |_| async {
        Ok(Some(AuthResult {
            auth: ModelAuth {
                api_key: Some("resolved-key".into()),
                headers: Some(headers(&[
                    ("Authorization", "Bearer resolved-key"),
                    ("x-a", "auth"),
                    ("x-b", "auth"),
                ])),
                base_url: Some("https://auth.test/v1".into()),
            },
            ..AuthResult::default()
        }))
    });
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        auth: Some(ProviderAuth {
            api_key: Some(auth.arc()),
            oauth: None,
        }),
        calls: Some(recorded_calls.clone()),
        ..TestProvider::default()
    }));
    let model = test_model("p1", "model-a");

    let mut options = SimpleStreamOptions::default();
    options.stream.request.api_key = Some("explicit-key".into());
    options.stream.request.headers = Some(headers(&[
        ("authorization", "Explicit token"),
        ("x-b", "explicit"),
    ]));
    let result = models
        .complete_simple(&model, context(), options.into())
        .await;
    assert_eq!(result.stop_reason, StopReason::Stop);
    let calls = recorded(&recorded_calls);
    assert_eq!(calls.len(), 1);
    assert_eq!(
        calls[0].options.request.api_key.as_deref(),
        Some("explicit-key")
    );
    assert_eq!(
        calls[0].options.request.headers,
        Some(headers(&[
            ("authorization", "Explicit token"),
            ("x-a", "auth"),
            ("x-b", "explicit")
        ]))
    );
    assert_eq!(calls[0].model.base_url, "https://auth.test/v1");

    // without explicit options, resolved auth applies
    let result2 = models
        .complete_simple(&model, context(), SimpleStreamOptions::default().into())
        .await;
    assert_eq!(result2.stop_reason, StopReason::Stop);
    assert_eq!(
        recorded(&recorded_calls)[1]
            .options
            .request
            .api_key
            .as_deref(),
        Some("resolved-key")
    );
}

#[tokio::test]
async fn adds_model_headers_only_for_model_auth_and_transforms_assembled_headers_once() {
    let recorded_calls = calls();
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        auth: Some(ProviderAuth {
            api_key: Some(env_key_auth(Some("key")).arc()),
            oauth: None,
        }),
        calls: Some(recorded_calls.clone()),
        ..TestProvider::default()
    }));
    let mut model = test_model("p1", "model-a");
    model.headers = Some(IndexMap::from([
        ("x-model".to_owned(), "model".to_owned()),
        ("x-shared".to_owned(), "model".to_owned()),
    ]));

    let provider_auth = models
        .get_auth("p1", AuthResolutionOverrides::default())
        .await
        .expect("auth")
        .expect("configured");
    assert_eq!(provider_auth.auth.headers, None);
    let model_auth = models
        .get_auth_for_model(
            &AnyModel::Chat(model.clone()),
            AuthResolutionOverrides::default(),
        )
        .await
        .expect("auth")
        .expect("configured");
    assert_eq!(
        model_auth.auth.headers,
        Some(headers(&[("x-model", "model"), ("x-shared", "model")]))
    );

    let transforms = Arc::new(AtomicUsize::new(0));
    let counter = Arc::clone(&transforms);
    let mut options = SimpleStreamOptions::default();
    options.stream.request.headers = Some(headers(&[
        ("x-explicit", "explicit"),
        ("X-Shared", "explicit"),
    ]));
    models
        .complete_simple(
            &model,
            context(),
            ModelsRequestOptions {
                options,
                transform_headers: Some(Arc::new(move |mut assembled: ProviderHeaders| {
                    counter.fetch_add(1, Ordering::SeqCst);
                    assert_eq!(
                        assembled,
                        headers(&[
                            ("x-model", "model"),
                            ("x-explicit", "explicit"),
                            ("X-Shared", "explicit")
                        ])
                    );
                    assembled.insert("x-transformed".into(), Some("yes".into()));
                    Box::pin(async move { Ok(assembled) })
                })),
            },
        )
        .await;

    assert_eq!(transforms.load(Ordering::SeqCst), 1);
    assert_eq!(
        recorded(&recorded_calls)[0].options.request.headers,
        Some(headers(&[
            ("x-model", "model"),
            ("x-explicit", "explicit"),
            ("X-Shared", "explicit"),
            ("x-transformed", "yes"),
        ]))
    );
    // `transformHeaders` never reaches the provider: the provider options type has no such field.
}
