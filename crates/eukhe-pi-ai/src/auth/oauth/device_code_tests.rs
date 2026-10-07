//! Port of `test/oauth-device-code.test.ts`. Fake timers become tokio paused
//! time; poll times are recorded as milliseconds since the flow started.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{AbortController, AbortSignal};
use tokio::time::Instant;

use super::{poll_oauth_device_code_flow, OAuthDeviceCodePollOptions, OAuthDeviceCodePollResult};

fn never_aborted_signal() -> AbortSignal {
    AbortController::new().signal()
}

fn options(
    interval: f64,
    expires: f64,
    wait_before_first_poll: bool,
) -> OAuthDeviceCodePollOptions {
    OAuthDeviceCodePollOptions {
        interval_seconds: Some(interval),
        expires_in_seconds: Some(expires),
        wait_before_first_poll,
        signal: never_aborted_signal(),
    }
}

/// Runs the flow with scripted results and returns the value and poll times.
async fn run(
    options: OAuthDeviceCodePollOptions,
    results: Vec<OAuthDeviceCodePollResult<&'static str>>,
) -> (&'static str, Vec<u128>) {
    let start = Instant::now();
    let poll_times = Arc::new(Mutex::new(Vec::new()));
    let results = Arc::new(Mutex::new(results.into_iter()));
    let times = Arc::clone(&poll_times);
    let value = poll_oauth_device_code_flow(options, move || {
        let times = Arc::clone(&times);
        let results = Arc::clone(&results);
        async move {
            times
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(start.elapsed().as_millis());
            let next = results
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .next();
            Ok(next.expect("Unexpected extra poll"))
        }
    })
    .await
    .expect("flow completes");
    let times = poll_times
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    (value, times)
}

#[tokio::test(start_paused = true)]
async fn polls_immediately_and_returns_the_completed_value() {
    let (value, times) = run(
        options(2.0, 30.0, false),
        vec![
            OAuthDeviceCodePollResult::Pending,
            OAuthDeviceCodePollResult::Complete { value: "token" },
        ],
    )
    .await;
    assert_eq!(value, "token");
    assert_eq!(times, vec![0, 2000]);
}

#[tokio::test(start_paused = true)]
async fn can_wait_before_the_first_poll() {
    let (value, times) = run(
        options(2.0, 30.0, true),
        vec![OAuthDeviceCodePollResult::Complete { value: "token" }],
    )
    .await;
    assert_eq!(value, "token");
    assert_eq!(times, vec![2000]);
}

#[tokio::test(start_paused = true)]
async fn increases_the_interval_by_5_seconds_after_slow_down_without_a_server_interval() {
    let (value, times) = run(
        options(2.0, 900.0, false),
        vec![
            OAuthDeviceCodePollResult::SlowDown {
                interval_seconds: None,
            },
            OAuthDeviceCodePollResult::Complete { value: "token" },
        ],
    )
    .await;
    assert_eq!(value, "token");
    assert_eq!(times, vec![0, 7000]);
}

#[tokio::test(start_paused = true)]
async fn honors_a_server_provided_slow_down_interval() {
    let (value, times) = run(
        options(2.0, 900.0, false),
        vec![
            OAuthDeviceCodePollResult::SlowDown {
                interval_seconds: Some(30.0),
            },
            OAuthDeviceCodePollResult::Complete { value: "token" },
        ],
    )
    .await;
    assert_eq!(value, "token");
    assert_eq!(times, vec![0, 30000]);
}

#[tokio::test(start_paused = true)]
async fn cancels_an_in_flight_wait() {
    let controller = AbortController::new();
    let mut opts = options(5.0, 30.0, false);
    opts.signal = controller.signal();
    let flow = tokio::spawn(poll_oauth_device_code_flow(opts, || async {
        Ok(OAuthDeviceCodePollResult::<()>::Pending)
    }));
    tokio::task::yield_now().await;
    controller.abort(None);
    let error = flow.await.expect("join").expect_err("cancelled");
    assert_eq!(error.to_string(), "Login cancelled");
}
