use futures::StreamExt;
use reqwest::header::HeaderMap;
use serde_json::json;

use super::sse::{sse_json_stream, LineDecoder, SseDecoder};
use super::{api_error_message, status_error};
use crate::utils::diagnostics::{ErrorObject, SdkValue};

fn body(chunks: &[&str]) -> futures::stream::BoxStream<'static, Result<Vec<u8>, String>> {
    let chunks: Vec<Result<Vec<u8>, String>> = chunks
        .iter()
        .map(|chunk| Ok(chunk.as_bytes().to_vec()))
        .collect();
    futures::stream::iter(chunks).boxed()
}

#[test]
fn line_decoder_splits_lf_cr_and_crlf_across_chunks() {
    let mut decoder = LineDecoder::default();
    assert_eq!(decoder.decode(b"a\r"), Vec::<String>::new());
    assert_eq!(decoder.decode(b"\nb\rc\n"), vec!["a", "b", "c"]);
    assert_eq!(decoder.decode(b"tail"), Vec::<String>::new());
    assert_eq!(decoder.flush(), vec!["tail"]);
}

#[test]
fn sse_decoder_joins_data_lines_and_skips_comments() {
    let mut decoder = SseDecoder::default();
    assert_eq!(decoder.decode(": comment"), None);
    assert_eq!(decoder.decode("event: response.created"), None);
    assert_eq!(decoder.decode("data: {\"a\":"), None);
    assert_eq!(decoder.decode("data:1}"), None);
    let sse = decoder.decode("").expect("event");
    assert_eq!(sse.event.as_deref(), Some("response.created"));
    assert_eq!(sse.data, "{\"a\":\n1}");
    assert_eq!(decoder.decode(""), None);
}

#[tokio::test]
async fn stream_yields_json_until_done_sentinel() {
    let events: Vec<_> = sse_json_stream(
        body(&[
            "data: {\"type\":\"a\"}\n\nda",
            "ta: [DONE]\n\ndata: {\"type\":\"b\"}\n\n",
        ]),
        HeaderMap::new(),
        None,
    )
    .collect()
    .await;
    assert_eq!(events.len(), 1);
    assert_eq!(events[0].as_ref().expect("event"), &json!({ "type": "a" }));
}

#[tokio::test]
async fn stream_flushes_a_final_event_without_blank_line() {
    let events: Vec<_> = sse_json_stream(body(&["data: {\"x\":1}"]), HeaderMap::new(), None)
        .collect()
        .await;
    assert_eq!(events.len(), 1);
    assert_eq!(events[0].as_ref().expect("event"), &json!({ "x": 1 }));
}

#[tokio::test]
async fn error_event_becomes_api_error() {
    let events: Vec<_> = sse_json_stream(
        body(&["event: error\ndata: {\"error\":{\"message\":\"boom\",\"code\":\"x\"}}\n\n"]),
        HeaderMap::new(),
        None,
    )
    .collect()
    .await;
    let error = events[0].as_ref().expect_err("error");
    let object = error.downcast_ref::<ErrorObject>().expect("ErrorObject");
    assert_eq!(object.message, "boom");
    assert_eq!(object.status, Some(None));
    assert_eq!(
        object.error,
        Some(SdkValue::Json(json!({ "message": "boom", "code": "x" })))
    );
}

#[tokio::test]
async fn malformed_json_is_a_syntax_error() {
    let events: Vec<_> = sse_json_stream(body(&["data: {nope\n\n"]), HeaderMap::new(), None)
        .collect()
        .await;
    let error = events[0].as_ref().expect_err("error");
    let object = error.downcast_ref::<ErrorObject>().expect("ErrorObject");
    assert_eq!(object.name, "SyntaxError");
    assert_eq!(
        object.message,
        "Error reading response: malformed server-sent event JSON."
    );
}

#[test]
fn api_error_messages_follow_make_message() {
    assert_eq!(
        api_error_message(Some(400), Some(&json!({ "message": "bad" })), None),
        "400 bad"
    );
    assert_eq!(
        api_error_message(Some(500), None, Some("")),
        "500 status code (no body)"
    );
    assert_eq!(
        api_error_message(Some(429), Some(&json!({ "code": 1 })), None),
        "429 {\"code\":1}"
    );
    assert_eq!(
        api_error_message(None, None, None),
        "(no status code or body)"
    );
}

#[test]
fn status_error_unwraps_the_error_body() {
    let error = status_error(
        401,
        "{\"error\":{\"message\":\"Invalid key\"}}",
        HeaderMap::new(),
    );
    assert_eq!(error.message, "401 Invalid key");
    assert_eq!(error.status, Some(Some(json!(401))));
    let plain = status_error(502, "Bad Gateway", HeaderMap::new());
    assert_eq!(plain.message, "502 Bad Gateway");
    assert_eq!(plain.error, None);
}
