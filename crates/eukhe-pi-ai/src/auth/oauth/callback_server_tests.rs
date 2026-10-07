//! Port of `test/oauth-callback-server.test.ts`.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{AbortController, AbortSignal};
use tokio::sync::oneshot;

use super::{
    start_oauth_callback_server, wait_for_callback_or_manual_input, CallbackOrManual, CompleteFn,
    OAuthCallbackServer, OAuthCallbackServerOptions,
};
use crate::auth::errors::js_error;
use crate::auth::oauth::test_support::{native_get, native_request, Page, TestInteraction};
use crate::auth::types::{AuthPrompt, ProviderAuthInteraction};
use crate::utils::diagnostics::Thrown;

fn callback_url(redirect_uri: &str, params: &[(&str, &str)]) -> String {
    let mut url = url::Url::parse(redirect_uri).expect("redirect uri");
    for (key, value) in params {
        url.query_pairs_mut().append_pair(key, value);
    }
    url.to_string()
}

fn completed(prefix: &'static str) -> CompleteFn<String> {
    Arc::new(move |code| Box::pin(async move { Ok(format!("{prefix}{code}")) }))
}

fn base_options() -> OAuthCallbackServerOptions<String> {
    OAuthCallbackServerOptions {
        provider_name: "Example".to_owned(),
        host: "127.0.0.1".to_owned(),
        port: 0,
        path: "/callback".to_owned(),
        redirect_host: None,
        state: Some("expected-state".to_owned()),
        complete: completed("completed:"),
        signal: None,
        timeout_ms: None,
    }
}

async fn start(options: OAuthCallbackServerOptions<String>) -> OAuthCallbackServer<String> {
    start_oauth_callback_server(options)
        .await
        .expect("server starts")
}

fn interaction(
    prompt: impl Fn(AuthPrompt) -> futures::future::BoxFuture<'static, Result<String, Thrown>>
        + Send
        + Sync
        + 'static,
    signal: Option<AbortSignal>,
) -> ProviderAuthInteraction {
    TestInteraction::provider(
        signal.unwrap_or_else(|| AbortController::new().signal()),
        prompt,
        |_| {},
    )
}

/// A manual prompt that stays open until its signal aborts.
fn pending_prompt(
    on_prompt: Option<Arc<Mutex<Option<AbortSignal>>>>,
) -> impl Fn(AuthPrompt) -> futures::future::BoxFuture<'static, Result<String, Thrown>> + Send + Sync
{
    move |prompt| {
        if let Some(slot) = &on_prompt {
            *slot.lock().unwrap_or_else(PoisonError::into_inner) = prompt.signal.clone();
        }
        Box::pin(async move {
            if let Some(signal) = prompt.signal {
                signal.cancelled().await;
            } else {
                std::future::pending::<()>().await;
            }
            Err(js_error("prompt aborted"))
        })
    }
}

#[tokio::test]
async fn ignores_stray_requests_and_resolves_with_the_completed_code() {
    let server = start(base_options()).await;
    let pattern = regex_like_redirect(&server.redirect_uri, "127.0.0.1");
    assert!(pattern, "{}", server.redirect_uri);

    let other = url::Url::parse(&server.redirect_uri)
        .expect("uri")
        .join("/other")
        .expect("join");
    let wrong_path = native_get(other.as_str()).await;
    assert_eq!(wrong_path.status, 404);
    let wrong_state = native_get(&callback_url(
        &server.redirect_uri,
        &[("code", "c"), ("state", "other")],
    ))
    .await;
    assert_eq!(wrong_state.status, 400);
    assert_eq!(
        wrong_state.content_type.as_deref(),
        Some("text/html; charset=utf-8")
    );
    assert!(wrong_state.body.contains("State mismatch."));
    let post = native_request(
        "POST",
        &callback_url(
            &server.redirect_uri,
            &[("code", "c"), ("state", "expected-state")],
        ),
    )
    .await;
    assert_eq!(post.status, 404);
    let missing_code = native_get(&callback_url(
        &server.redirect_uri,
        &[("state", "expected-state")],
    ))
    .await;
    assert_eq!(missing_code.status, 400);

    let success = native_get(&callback_url(
        &server.redirect_uri,
        &[("code", "the-code"), ("state", "expected-state")],
    ))
    .await;
    assert_eq!(success.status, 200);
    assert_eq!(
        success.content_type.as_deref(),
        Some("text/html; charset=utf-8")
    );
    assert!(success.body.contains("Authentication successful"));
    assert!(success.body.contains("Signed in to Example."));
    assert!(success.body.contains("fill=\"#F09082\""));
    assert!(success.body.contains("fill=\"#4D9ABF\""));
    assert!(success.body.contains("fill=\"#F1BE58\""));
    assert_eq!(
        server.wait().await.expect("wait"),
        Some("completed:the-code".to_owned())
    );
    server.close();
}

/// `^http://<host>:\d+/callback$`.
fn regex_like_redirect(uri: &str, host: &str) -> bool {
    uri.strip_prefix(&format!("http://{host}:"))
        .and_then(|rest| rest.strip_suffix("/callback"))
        .is_some_and(|port| !port.is_empty() && port.bytes().all(|byte| byte.is_ascii_digit()))
}

#[tokio::test]
async fn uses_the_redirect_host_and_skips_the_state_check_when_none_is_expected() {
    let server = start(OAuthCallbackServerOptions {
        redirect_host: Some("localhost".to_owned()),
        state: None,
        ..base_options()
    })
    .await;
    assert!(regex_like_redirect(&server.redirect_uri, "localhost"));
    // `localhost` may resolve to ::1 first; the server listens on 127.0.0.1.
    let uri = server.redirect_uri.replace("localhost", "127.0.0.1");
    let response = native_get(&callback_url(&uri, &[("code", "no-state")])).await;
    assert_eq!(response.status, 200);
    assert_eq!(
        server.wait().await.expect("wait"),
        Some("completed:no-state".to_owned())
    );
    server.close();
}

#[tokio::test]
async fn shows_completion_failures_on_the_page_and_rejects_the_wait() {
    let server = start(OAuthCallbackServerOptions {
        complete: Arc::new(|_| Box::pin(async { Err(js_error("token exchange failed")) })),
        ..base_options()
    })
    .await;
    let failure = native_get(&callback_url(
        &server.redirect_uri,
        &[("code", "c"), ("state", "expected-state")],
    ))
    .await;
    assert_eq!(failure.status, 502);
    assert!(failure.body.contains("Example sign-in failed."));
    assert!(failure.body.contains("token exchange failed"));
    let error = server.wait().await.expect_err("rejects");
    assert!(error.to_string().contains("token exchange failed"));
    server.close();
}

#[tokio::test]
async fn rejects_the_wait_when_the_provider_redirects_with_an_error() {
    let server = start(base_options()).await;
    let failure = native_get(&callback_url(
        &server.redirect_uri,
        &[
            ("error", "access_denied"),
            ("error_description", "User denied access"),
            ("state", "expected-state"),
        ],
    ))
    .await;
    assert_eq!(failure.status, 400);
    assert!(failure.body.contains("User denied access"));
    let error = server.wait().await.expect_err("rejects");
    assert!(error
        .to_string()
        .contains("Example authorization failed: User denied access"));
    server.close();
}

#[tokio::test]
async fn completes_only_the_first_callback() {
    let (finish_tx, finish_rx) = oneshot::channel::<oneshot::Sender<String>>();
    let finish_tx = Arc::new(Mutex::new(Some(finish_tx)));
    let server = start(OAuthCallbackServerOptions {
        complete: Arc::new(move |_| {
            let finish_tx = Arc::clone(&finish_tx);
            Box::pin(async move {
                let (value_tx, value_rx) = oneshot::channel();
                if let Some(sender) = finish_tx
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .take()
                {
                    let _ = sender.send(value_tx);
                }
                value_rx.await.map_err(|error| js_error(error.to_string()))
            })
        }),
        ..base_options()
    })
    .await;
    let url = callback_url(
        &server.redirect_uri,
        &[("code", "c"), ("state", "expected-state")],
    );
    let first_url = url.clone();
    let first = tokio::spawn(async move { native_get(&first_url).await });
    let finish_exchange = finish_rx.await.expect("exchange started");
    let second = native_get(&url).await;
    assert_eq!(second.status, 409);
    // A claimed callback keeps completing even when the caller switches to manual input.
    server.cancel();
    finish_exchange.send("done".to_owned()).expect("send");
    let first: Page = first.await.expect("join");
    assert_eq!(first.status, 200);
    assert_eq!(server.wait().await.expect("wait"), Some("done".to_owned()));
    server.close();
}

#[tokio::test]
async fn resolves_with_undefined_after_cancel() {
    let server = start(base_options()).await;
    server.cancel();
    assert_eq!(server.wait().await.expect("wait"), None);
    let late = native_get(&callback_url(
        &server.redirect_uri,
        &[("code", "c"), ("state", "expected-state")],
    ))
    .await;
    assert_eq!(late.status, 409);
    server.close();
}

#[tokio::test]
async fn rejects_the_wait_on_abort_and_on_timeout() {
    let controller = AbortController::new();
    let aborted = start(OAuthCallbackServerOptions {
        signal: Some(controller.signal()),
        ..base_options()
    })
    .await;
    controller.abort(None);
    let error = aborted.wait().await.expect_err("aborted");
    assert_eq!(error.to_string(), "Login cancelled");
    aborted.close();

    let timed_out = start(OAuthCallbackServerOptions {
        timeout_ms: Some(10),
        ..base_options()
    })
    .await;
    let error = timed_out.wait().await.expect_err("timed out");
    assert_eq!(error.to_string(), "Example sign-in timed out");
    timed_out.close();

    let already_aborted = AbortController::new();
    already_aborted.abort(None);
    let error = start_oauth_callback_server(OAuthCallbackServerOptions {
        signal: Some(already_aborted.signal()),
        ..base_options()
    })
    .await
    .expect_err("already aborted");
    assert_eq!(error.to_string(), "Login cancelled");
}

#[tokio::test]
async fn fails_instead_of_picking_another_port_when_the_requested_port_is_taken() {
    let blocker = tokio::net::TcpListener::bind("127.0.0.1:0")
        .await
        .expect("blocker binds");
    let port = blocker.local_addr().expect("addr").port();
    let error = start_oauth_callback_server(OAuthCallbackServerOptions {
        port,
        ..base_options()
    })
    .await
    .expect_err("port taken");
    let io = error
        .downcast_ref::<std::io::Error>()
        .expect("io error (EADDRINUSE)");
    assert_eq!(io.kind(), std::io::ErrorKind::AddrInUse);
}

fn plain_options() -> OAuthCallbackServerOptions<String> {
    OAuthCallbackServerOptions {
        state: None,
        complete: completed(""),
        ..base_options()
    }
}

#[tokio::test]
async fn returns_the_browser_callback_and_aborts_the_manual_prompt() {
    let manual_signal = Arc::new(Mutex::new(None));
    let server = start(plain_options()).await;
    let auth = interaction(pending_prompt(Some(Arc::clone(&manual_signal))), None);
    let wait_server = server.clone();
    let placeholder = server.redirect_uri.clone();
    let result = tokio::spawn(async move {
        wait_for_callback_or_manual_input(&auth, Some(&wait_server), "paste", &placeholder).await
    });
    native_get(&callback_url(
        &server.redirect_uri,
        &[("code", "from-browser")],
    ))
    .await;
    assert_eq!(
        result.await.expect("join").expect("result"),
        CallbackOrManual::Callback {
            value: "from-browser".to_owned()
        }
    );
    let signal = manual_signal
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("prompted");
    assert!(signal.aborted());
    server.close();
}

#[tokio::test]
async fn returns_pasted_input_and_stops_waiting_for_the_browser() {
    let server = start(plain_options()).await;
    let auth = interaction(|_| Box::pin(async { Ok("pasted".to_owned()) }), None);
    let result =
        wait_for_callback_or_manual_input(&auth, Some(&server), "paste", &server.redirect_uri)
            .await
            .expect("result");
    assert_eq!(
        result,
        CallbackOrManual::Manual {
            input: "pasted".to_owned()
        }
    );
    server.close();
}

#[tokio::test]
async fn uses_only_the_manual_prompt_without_a_callback_server() {
    let auth = interaction(|_| Box::pin(async { Ok("pasted".to_owned()) }), None);
    let result = wait_for_callback_or_manual_input::<String>(
        &auth,
        None,
        "paste",
        "http://localhost/callback",
    )
    .await
    .expect("result");
    assert_eq!(
        result,
        CallbackOrManual::Manual {
            input: "pasted".to_owned()
        }
    );
}

#[tokio::test]
async fn propagates_manual_prompt_failures() {
    let server = start(plain_options()).await;
    let auth = interaction(
        |_| Box::pin(async { Err(js_error("prompt cancelled")) }),
        None,
    );
    let error =
        wait_for_callback_or_manual_input(&auth, Some(&server), "paste", &server.redirect_uri)
            .await
            .expect_err("fails");
    assert_eq!(error.to_string(), "prompt cancelled");
    server.close();
}
