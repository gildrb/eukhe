//! Port of `test/bedrock-custom-headers.test.ts`. TS inspects the registered
//! Smithy build middleware; here the local server records the headers the
//! request actually carried. The middleware's "request without a headers
//! object" guard has no Rust counterpart (every request has headers).

use eukhe_pi_ai::api::bedrock_converse_stream::{stream, stream_simple};
use eukhe_pi_ai::types::SimpleStreamOptions;
use eukhe_types::pi_ai::{CacheRetention, ProviderHeaders};
use serde_json::json;

use super::support::{
    context_of, event_stream, get_model, mock_env, options, user, with_base_url, CapturedRequest,
    EnvGuard, MockBedrock, Reply,
};

fn reply() -> Reply {
    Reply::events(
        &[],
        event_stream(&[
            json!({ "messageStart": { "role": "assistant" } }),
            json!({ "messageStop": { "stopReason": "end_turn" } }),
        ]),
    )
}

fn headers(pairs: &[(&str, &str)]) -> ProviderHeaders {
    pairs
        .iter()
        .map(|(key, value)| ((*key).to_owned(), Some((*value).to_owned())))
        .collect()
}

async fn drive_bedrock(custom: Option<ProviderHeaders>) -> CapturedRequest {
    let server = MockBedrock::start(vec![reply()]).await;
    let model = with_base_url(
        &get_model("amazon-bedrock", "us.anthropic.claude-opus-4-8"),
        &server.url,
    );
    let mut options = options(json!({}));
    options.stream.cache_retention = Some(CacheRetention::None);
    options.stream.request.env = Some(mock_env());
    options.stream.request.headers = custom;
    stream(&model, &context_of(vec![user("hello")]), options)
        .result()
        .await;
    server.requests().remove(0)
}

fn signed_headers(request: &CapturedRequest) -> Vec<String> {
    let authorization = request.header("authorization").expect("authorization");
    let start = authorization
        .find("SignedHeaders=")
        .expect("signed headers")
        + 14;
    let end = authorization[start..].find(',').expect("comma") + start;
    authorization[start..end]
        .split(';')
        .map(str::to_owned)
        .collect()
}

#[tokio::test]
async fn vc1_injects_the_caller_header_before_signing() {
    let _env = EnvGuard::new(&[]).await;
    let request = drive_bedrock(Some(headers(&[("x-custom", "v")]))).await;
    assert_eq!(request.header("x-custom"), Some("v"));
    assert!(signed_headers(&request).contains(&"x-custom".to_owned()));
    assert_eq!(request.method, "POST");
    assert_eq!(
        request.path,
        "/model/us.anthropic.claude-opus-4-8/converse-stream"
    );
    assert!(request.body.starts_with("{\"messages\":"));
}

#[tokio::test]
async fn vc2_skips_reserved_headers_case_insensitively_while_applying_allowed_ones() {
    let _env = EnvGuard::new(&[]).await;
    let request = drive_bedrock(Some(headers(&[
        ("authorization", "evil"),
        ("x-amz-date", "evil"),
        ("x-allowed", "ok"),
        ("Authorization", "evil2"),
        ("X-Amz-Date", "evil2"),
        ("HOST", "evil3"),
    ])))
    .await;
    assert!(request
        .header("authorization")
        .is_some_and(|value| value.starts_with("AWS4-HMAC-SHA256 ")));
    assert!(request
        .header("x-amz-date")
        .is_some_and(|value| !value.starts_with("evil")));
    assert!(request
        .header("host")
        .is_some_and(|value| value.starts_with("127.0.0.1:")));
    assert_eq!(request.header("x-allowed"), Some("ok"));
    for name in ["authorization", "x-amz-date", "host"] {
        assert_eq!(
            request
                .headers
                .iter()
                .filter(|(key, _)| key == name)
                .count(),
            1,
            "{name}"
        );
    }
}

#[tokio::test]
async fn vc3_adds_no_header_when_headers_is_undefined_or_empty() {
    let _env = EnvGuard::new(&[]).await;
    let baseline = drive_bedrock(None).await;
    let empty = drive_bedrock(Some(ProviderHeaders::new())).await;
    let names = |request: &CapturedRequest| {
        request
            .headers
            .iter()
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(names(&baseline), names(&empty));
    assert!(baseline.header("x-custom").is_none());
}

#[tokio::test]
async fn vc4_stream_simple_forwards_headers_end_to_end() {
    let _env = EnvGuard::new(&[]).await;
    let server = MockBedrock::start(vec![reply()]).await;
    let model = with_base_url(
        &get_model("amazon-bedrock", "us.anthropic.claude-opus-4-8"),
        &server.url,
    );
    let mut options = SimpleStreamOptions::default();
    options.stream.request.env = Some(mock_env());
    options.stream.request.headers = Some(headers(&[("x-custom", "v")]));
    stream_simple(&model, &context_of(vec![user("hello")]), options)
        .result()
        .await;
    assert_eq!(server.requests()[0].header("x-custom"), Some("v"));
}
