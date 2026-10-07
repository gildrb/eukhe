//! Port of `test/bedrock-error-metadata.test.ts`. The SDK failures the TS
//! test fakes are produced by the local server: a non-2xx response, an
//! exception frame, an error frame, a connection drop.
//!
//! "modeled mid-stream exception": the TS mock throws a bare object; the real
//! SDK (verified against `@aws-sdk/client-bedrock-runtime` 3.1127) throws a
//! modeled `ThrottlingException`, whose code is known, so the diagnostic also
//! carries `errorCode`.

use eukhe_pi_ai::api::bedrock_converse_stream::stream;
use eukhe_types::pi_ai::{AssistantMessage, CacheRetention, StopReason};
use serde_json::{json, Value};

use super::support::{
    aborted_signal, context_of, error_frame, event_frame, exception_frame, find_diagnostic,
    get_model, mock_env, options, user, with_base_url, EnvGuard, MockBedrock, Reply,
};

const DIAGNOSTIC_TYPE: &str = "bedrock_response_failure";
const VALIDATION_MESSAGE: &str = "The provided model identifier is invalid.";
const REQUEST_ID: &str = "11111111-2222-3333-4444-555555555555";

async fn run_bedrock(
    reply: Reply,
    signal: Option<eukhe_chord::context::AbortSignal>,
) -> AssistantMessage {
    let server = MockBedrock::start(vec![reply]).await;
    let model = with_base_url(
        &get_model("amazon-bedrock", "us.anthropic.claude-opus-4-8"),
        &server.url,
    );
    let mut options = options(json!({}));
    options.stream.cache_retention = Some(CacheRetention::None);
    options.stream.request.env = Some(mock_env());
    options.stream.request.signal = signal;
    stream(&model, &context_of(vec![user("hello")]), options)
        .result()
        .await
}

fn validation_reply(status: u16, error_type: &str, request_id: &str) -> Reply {
    Reply::json(
        status,
        &[
            ("x-amzn-errortype", error_type),
            ("x-amzn-requestid", request_id),
        ],
        &json!({ "message": VALIDATION_MESSAGE }),
    )
}

/// Fails after `messageStart`, with `tail` as the next body bytes.
fn failing_stream(tail: Vec<u8>) -> Reply {
    let mut body = event_frame(&json!({ "messageStart": { "role": "assistant" } }));
    body.extend(tail);
    Reply::events(&[("x-amzn-requestid", REQUEST_ID)], body)
}

fn details(message: &AssistantMessage) -> Option<Value> {
    find_diagnostic(message, DIAGNOSTIC_TYPE).map(|diagnostic| diagnostic["details"].clone())
}

#[tokio::test]
async fn records_status_error_code_and_request_id_for_a_non_2xx_from_client_send() {
    let _env = EnvGuard::new(&[]).await;
    let message = run_bedrock(
        validation_reply(400, "ValidationException", REQUEST_ID),
        None,
    )
    .await;
    let diagnostic = find_diagnostic(&message, DIAGNOSTIC_TYPE).expect("diagnostic");
    assert_eq!(message.stop_reason, StopReason::Error);
    assert_eq!(
        diagnostic["details"],
        json!({ "status": 400, "errorCode": "ValidationException", "requestId": REQUEST_ID })
    );
    assert!(diagnostic.get("error").is_none());
    let mut keys: Vec<&String> = diagnostic.as_object().expect("object").keys().collect();
    keys.sort();
    assert_eq!(keys, ["details", "timestamp", "type"]);
}

#[tokio::test]
async fn leaves_error_message_untouched_so_retry_classification_is_unaffected() {
    let _env = EnvGuard::new(&[]).await;
    let message = run_bedrock(
        validation_reply(400, "ValidationException", REQUEST_ID),
        None,
    )
    .await;
    assert_eq!(
        message.error_message.as_deref(),
        Some(format!("Validation error: {VALIDATION_MESSAGE}").as_str())
    );
}

#[tokio::test]
async fn reports_the_error_code_and_request_id_for_a_modeled_mid_stream_exception() {
    let _env = EnvGuard::new(&[]).await;
    let message = run_bedrock(
        failing_stream(exception_frame(
            "throttlingException",
            &json!({ "message": "Too many requests, please wait." }),
        )),
        None,
    )
    .await;
    assert_eq!(message.stop_reason, StopReason::Error);
    assert_eq!(
        details(&message),
        Some(json!({ "errorCode": "ThrottlingException", "requestId": REQUEST_ID }))
    );
}

#[tokio::test]
async fn captures_the_error_code_for_an_unmodeled_mid_stream_error() {
    let _env = EnvGuard::new(&[]).await;
    let message = run_bedrock(
        failing_stream(error_frame(
            "ModelStreamErrorException",
            "Model stream terminated unexpectedly.",
        )),
        None,
    )
    .await;
    assert_eq!(
        details(&message),
        Some(json!({ "errorCode": "ModelStreamErrorException", "requestId": REQUEST_ID }))
    );
}

#[tokio::test]
async fn does_not_report_a_transport_failure_name_as_a_provider_error_code() {
    let _env = EnvGuard::new(&[]).await;
    let body = event_frame(&json!({ "messageStart": { "role": "assistant" } }));
    let message = run_bedrock(
        Reply::Truncated {
            headers: vec![("x-amzn-requestid".into(), REQUEST_ID.into())],
            body,
        },
        None,
    )
    .await;
    assert_eq!(details(&message), Some(json!({ "requestId": REQUEST_ID })));
}

#[tokio::test]
async fn emits_no_diagnostic_when_the_failure_carries_no_provider_metadata() {
    let _env = EnvGuard::new(&[]).await;
    let message = run_bedrock(Reply::Hangup, None).await;
    assert_eq!(message.stop_reason, StopReason::Error);
    assert_eq!(message.error_message.as_deref(), Some("socket hang up"));
    assert_eq!(find_diagnostic(&message, DIAGNOSTIC_TYPE), None);
}

#[tokio::test]
async fn emits_no_diagnostic_for_an_aborted_turn() {
    let _env = EnvGuard::new(&[]).await;
    let message = run_bedrock(
        validation_reply(400, "ValidationException", REQUEST_ID),
        Some(aborted_signal()),
    )
    .await;
    assert_eq!(message.stop_reason, StopReason::Aborted);
    assert_eq!(find_diagnostic(&message, DIAGNOSTIC_TYPE), None);
}

#[tokio::test]
async fn drops_header_derived_values_that_exceed_the_length_bound() {
    let _env = EnvGuard::new(&[]).await;
    let code = format!("{}Exception", "E".repeat(5000));
    let request_id = "R".repeat(5000);
    let message = run_bedrock(validation_reply(400, &code, &request_id), None).await;
    assert_eq!(details(&message), Some(json!({ "status": 400 })));
}

#[tokio::test]
async fn omits_the_sdks_unknown_placeholder_instead_of_reporting_it_as_a_code() {
    let _env = EnvGuard::new(&[]).await;
    let message = run_bedrock(
        Reply::json(
            403,
            &[("x-amzn-requestid", REQUEST_ID)],
            &json!({ "message": VALIDATION_MESSAGE }),
        ),
        None,
    )
    .await;
    assert_eq!(
        details(&message),
        Some(json!({ "status": 403, "requestId": REQUEST_ID }))
    );
}
