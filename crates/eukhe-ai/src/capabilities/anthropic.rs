//! The Anthropic dialect: token counting (`POST /v1/messages/count_tokens`),
//! the model catalog (`GET /v1/models`), and server-side web search
//! (`POST /v1/messages` with the `web_search_20250305` tool).

use eukhe_types::pi_ai::{JsonObject, JsonValue, ProviderHeaders, TranscriptContext};
use serde_json::json;

use super::http::{api_key, count, header_source, send, unexpected, unversioned_root, Body, Call};
use super::{ListedModel, TokenCount, WebSearchRequest, WebSearchResult, WebSource};
use crate::api::anthropic_messages::params::build_params;
use crate::api::anthropic_messages::{is_oauth_token, AnthropicOptions};
use crate::api::classifier_shared::error;
use crate::types::{Model, ProviderRequestOptions, StreamOptions};
use crate::utils::diagnostics::Thrown;

const LABEL: &str = "Anthropic";

/// The request fields `count_tokens` accepts out of a messages request.
const COUNT_FIELDS: [&str; 6] = [
    "model",
    "messages",
    "system",
    "tools",
    "tool_choice",
    "thinking",
];

/// The output cap of a web search answer.
const WEB_SEARCH_MAX_TOKENS: u64 = 4096;

/// The page size of the model catalog (the API maximum).
const MODELS_PAGE_LIMIT: u32 = 1000;

/// The version and auth headers: OAuth tokens go as a bearer with the
/// OAuth beta, API keys as `x-api-key`.
fn auth_headers(key: &str) -> ProviderHeaders {
    let version = ("anthropic-version", "2023-06-01".to_owned());
    if is_oauth_token(key) {
        header_source([
            version,
            ("authorization", format!("Bearer {key}")),
            ("anthropic-beta", "oauth-2025-04-20".to_owned()),
        ])
    } else {
        header_source([version, ("x-api-key", key.to_owned())])
    }
}

/// The input tokens `context` costs on `model`.
#[tracing::instrument(skip_all, fields(model = %model.id))]
pub(crate) async fn count_tokens(
    model: &Model,
    context: &TranscriptContext,
    options: &ProviderRequestOptions,
) -> Result<TokenCount, Thrown> {
    let key = api_key(model, options)?;
    let chat_options = AnthropicOptions {
        stream: StreamOptions {
            request: options.clone(),
            ..StreamOptions::default()
        },
        ..AnthropicOptions::default()
    };
    let params = build_params(
        model,
        context.messages(),
        is_oauth_token(key),
        &chat_options,
    )?;
    let payload: JsonObject = params
        .into_iter()
        .filter(|(field, _)| COUNT_FIELDS.contains(&field.as_str()))
        .collect();
    let body = send(
        model,
        options,
        Call {
            label: LABEL,
            url: format!(
                "{}/v1/messages/count_tokens",
                unversioned_root(&model.base_url)
            ),
            defaults: auth_headers(key),
            body: Body::Post(JsonValue::Object(payload)),
        },
    )
    .await?;
    let input_tokens =
        count(body.get("input_tokens")).ok_or_else(|| unexpected(LABEL, "token count"))?;
    Ok(TokenCount { input_tokens })
}

/// Every model the key can use, across all catalog pages.
#[tracing::instrument(skip_all, fields(model = %model.id))]
pub(crate) async fn list_models(
    model: &Model,
    options: &ProviderRequestOptions,
) -> Result<Vec<ListedModel>, Thrown> {
    let key = api_key(model, options)?;
    let root = unversioned_root(&model.base_url);
    let mut listed = Vec::new();
    let mut after: Option<String> = None;
    loop {
        let url = match &after {
            Some(last) => format!("{root}/v1/models?limit={MODELS_PAGE_LIMIT}&after_id={last}"),
            None => format!("{root}/v1/models?limit={MODELS_PAGE_LIMIT}"),
        };
        let body = send(
            model,
            options,
            Call {
                label: LABEL,
                url,
                defaults: auth_headers(key),
                body: Body::Get,
            },
        )
        .await?;
        let data = body
            .get("data")
            .and_then(JsonValue::as_array)
            .ok_or_else(|| unexpected(LABEL, "model list"))?;
        for item in data {
            let id = item
                .get("id")
                .and_then(JsonValue::as_str)
                .ok_or_else(|| unexpected(LABEL, "model list"))?;
            listed.push(ListedModel {
                id: id.to_owned(),
                name: item
                    .get("display_name")
                    .and_then(JsonValue::as_str)
                    .map(str::to_owned),
                context_window: count(item.get("max_input_tokens")),
                max_output_tokens: count(item.get("max_tokens")),
            });
        }
        let has_more = body.get("has_more").and_then(JsonValue::as_bool) == Some(true);
        let last_id = body
            .get("last_id")
            .and_then(JsonValue::as_str)
            .map(str::to_owned);
        match (has_more, last_id) {
            (true, Some(last)) => after = Some(last),
            (true, None) => return Err(unexpected(LABEL, "model list page")),
            (false, _) => return Ok(listed),
        }
    }
}

/// Adds `url` to `sources` unless an earlier source has it.
fn add_source(sources: &mut Vec<WebSource>, entry: &JsonValue) {
    let Some(url) = entry.get("url").and_then(JsonValue::as_str) else {
        return;
    };
    if sources.iter().any(|source| source.url == url) {
        return;
    }
    sources.push(WebSource {
        url: url.to_owned(),
        title: entry
            .get("title")
            .and_then(JsonValue::as_str)
            .map(str::to_owned),
    });
}

/// The answer to `request.query`, researched with Anthropic's server-side
/// web search tool.
#[tracing::instrument(skip_all, fields(model = %model.id))]
pub(crate) async fn web_search(
    model: &Model,
    request: &WebSearchRequest,
    options: &ProviderRequestOptions,
) -> Result<WebSearchResult, Thrown> {
    let key = api_key(model, options)?;
    let mut tool = json!({ "type": "web_search_20250305", "name": "web_search" });
    if let Some(max_uses) = request.max_searches {
        tool["max_uses"] = json!(max_uses);
    }
    let body = send(
        model,
        options,
        Call {
            label: LABEL,
            url: format!("{}/v1/messages", unversioned_root(&model.base_url)),
            defaults: auth_headers(key),
            body: Body::Post(json!({
                "model": model.id,
                "max_tokens": model.max_tokens.min(WEB_SEARCH_MAX_TOKENS),
                "messages": [{ "role": "user", "content": request.query }],
                "tools": [tool],
            })),
        },
    )
    .await?;
    let blocks = body
        .get("content")
        .and_then(JsonValue::as_array)
        .ok_or_else(|| unexpected(LABEL, "web search answer"))?;
    let mut answer = String::new();
    let mut sources = Vec::new();
    for block in blocks {
        match block.get("type").and_then(JsonValue::as_str) {
            Some("text") => {
                if let Some(text) = block.get("text").and_then(JsonValue::as_str) {
                    answer.push_str(text);
                }
                for citation in block
                    .get("citations")
                    .and_then(JsonValue::as_array)
                    .into_iter()
                    .flatten()
                {
                    add_source(&mut sources, citation);
                }
            }
            Some("web_search_tool_result") => match block.get("content") {
                Some(JsonValue::Array(results)) => {
                    for result in results.iter().filter(|result| {
                        result.get("type").and_then(JsonValue::as_str) == Some("web_search_result")
                    }) {
                        add_source(&mut sources, result);
                    }
                }
                Some(failure) => {
                    let code = failure
                        .get("error_code")
                        .and_then(JsonValue::as_str)
                        .unwrap_or("unknown");
                    return Err(error(format!("{LABEL} web search failed: {code}")));
                }
                None => return Err(unexpected(LABEL, "web search result")),
            },
            Some(_) | None => {}
        }
    }
    Ok(WebSearchResult { answer, sources })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::capabilities::mock_server::{headers, model, options, serve, Recorded, Reply};
    use crate::utils::transcript::normalize_context;

    fn claude(root: &str) -> Model {
        model("anthropic", "anthropic-messages", "claude-sonnet-4-5", root)
    }

    #[tokio::test]
    async fn count_tokens_posts_the_count_fields_of_the_chat_request() {
        let (root, server) = serve(vec![Reply::ok(json!({ "input_tokens": 21 }))]).await;
        let context = normalize_context(
            serde_json::from_value(json!({
                "systemPrompt": "Be brief.",
                "messages": [{ "role": "user", "content": "Hello", "timestamp": 0 }],
            }))
            .expect("a context"),
        );
        let counted = count_tokens(
            &claude(&format!("{root}/v1")),
            &context,
            &options("sk-ant-api"),
        )
        .await
        .expect("count");
        assert_eq!(counted, TokenCount { input_tokens: 21 });
        assert_eq!(
            server.await.expect("server"),
            vec![Recorded {
                method: "POST".to_owned(),
                path: "/v1/messages/count_tokens".to_owned(),
                headers: headers([
                    ("accept", "application/json"),
                    ("anthropic-version", "2023-06-01"),
                    ("content-type", "application/json"),
                    ("x-api-key", "sk-ant-api"),
                ]),
                body: Some(json!({
                    "model": "claude-sonnet-4-5",
                    "messages": [{
                        "role": "user",
                        "content": [{ "type": "text", "text": "Hello", "cache_control": { "type": "ephemeral" } }]
                    }],
                    "system": [{ "type": "text", "text": "Be brief.", "cache_control": { "type": "ephemeral" } }],
                })),
            }]
        );
    }

    #[tokio::test]
    async fn list_models_follows_pages_with_an_oauth_token() {
        let (root, server) = serve(vec![
            Reply::ok(json!({
                "data": [{
                    "type": "model",
                    "id": "claude-opus-4-1",
                    "display_name": "Claude Opus 4.1",
                    "created_at": "2025-08-05T00:00:00Z",
                    "max_input_tokens": 200_000,
                    "max_tokens": 32_000
                }],
                "has_more": true,
                "first_id": "claude-opus-4-1",
                "last_id": "claude-opus-4-1"
            })),
            Reply::ok(json!({
                "data": [{
                    "type": "model",
                    "id": "claude-haiku-4-5",
                    "display_name": "Claude Haiku 4.5",
                    "created_at": "2025-10-01T00:00:00Z"
                }],
                "has_more": false,
                "first_id": "claude-haiku-4-5",
                "last_id": "claude-haiku-4-5"
            })),
        ])
        .await;
        let listed = list_models(&claude(&root), &options("sk-ant-oat01-token"))
            .await
            .expect("models");
        assert_eq!(
            listed,
            vec![
                ListedModel {
                    id: "claude-opus-4-1".to_owned(),
                    name: Some("Claude Opus 4.1".to_owned()),
                    context_window: Some(200_000),
                    max_output_tokens: Some(32_000),
                },
                ListedModel {
                    id: "claude-haiku-4-5".to_owned(),
                    name: Some("Claude Haiku 4.5".to_owned()),
                    context_window: None,
                    max_output_tokens: None,
                },
            ]
        );
        let oauth = headers([
            ("accept", "application/json"),
            ("anthropic-beta", "oauth-2025-04-20"),
            ("anthropic-version", "2023-06-01"),
            ("authorization", "Bearer sk-ant-oat01-token"),
        ]);
        assert_eq!(
            server.await.expect("server"),
            vec![
                Recorded {
                    method: "GET".to_owned(),
                    path: "/v1/models?limit=1000".to_owned(),
                    headers: oauth.clone(),
                    body: None,
                },
                Recorded {
                    method: "GET".to_owned(),
                    path: "/v1/models?limit=1000&after_id=claude-opus-4-1".to_owned(),
                    headers: oauth,
                    body: None,
                },
            ]
        );
    }

    #[tokio::test]
    async fn web_search_collects_the_answer_and_deduplicated_sources() {
        let (root, server) = serve(vec![Reply::ok(json!({
            "type": "message",
            "role": "assistant",
            "content": [
                { "type": "server_tool_use", "id": "srvtoolu_1", "name": "web_search", "input": { "query": "rust release" } },
                {
                    "type": "web_search_tool_result",
                    "tool_use_id": "srvtoolu_1",
                    "content": [
                        { "type": "web_search_result", "url": "https://blog.rust-lang.org/a", "title": "Rust 1.90", "encrypted_content": "x" },
                        { "type": "web_search_result", "url": "https://example.com/b", "title": "News", "encrypted_content": "y" }
                    ]
                },
                {
                    "type": "text",
                    "text": "Rust 1.90 shipped.",
                    "citations": [
                        { "type": "web_search_result_location", "url": "https://blog.rust-lang.org/a", "title": "Rust 1.90", "cited_text": "1.90" },
                        { "type": "web_search_result_location", "url": "https://example.org/c", "title": "Other", "cited_text": "c" }
                    ]
                },
                { "type": "text", "text": " It is stable." }
            ]
        }))])
        .await;
        let result = web_search(
            &claude(&root),
            &WebSearchRequest {
                query: "latest rust release".to_owned(),
                max_searches: Some(3),
            },
            &options("sk-ant-api"),
        )
        .await
        .expect("answer");
        assert_eq!(
            result,
            WebSearchResult {
                answer: "Rust 1.90 shipped. It is stable.".to_owned(),
                sources: vec![
                    WebSource {
                        url: "https://blog.rust-lang.org/a".to_owned(),
                        title: Some("Rust 1.90".to_owned()),
                    },
                    WebSource {
                        url: "https://example.com/b".to_owned(),
                        title: Some("News".to_owned()),
                    },
                    WebSource {
                        url: "https://example.org/c".to_owned(),
                        title: Some("Other".to_owned()),
                    },
                ],
            }
        );
        assert_eq!(
            server.await.expect("server"),
            vec![Recorded {
                method: "POST".to_owned(),
                path: "/v1/messages".to_owned(),
                headers: headers([
                    ("accept", "application/json"),
                    ("anthropic-version", "2023-06-01"),
                    ("content-type", "application/json"),
                    ("x-api-key", "sk-ant-api"),
                ]),
                body: Some(json!({
                    "model": "claude-sonnet-4-5",
                    "max_tokens": 4096,
                    "messages": [{ "role": "user", "content": "latest rust release" }],
                    "tools": [{ "type": "web_search_20250305", "name": "web_search", "max_uses": 3 }],
                })),
            }]
        );
    }

    #[tokio::test]
    async fn web_search_fails_with_the_tool_error_code() {
        let (root, server) = serve(vec![Reply::ok(json!({
            "type": "message",
            "content": [{
                "type": "web_search_tool_result",
                "tool_use_id": "srvtoolu_1",
                "content": { "type": "web_search_tool_result_error", "error_code": "max_uses_exceeded" }
            }]
        }))])
        .await;
        let failure = web_search(
            &claude(&root),
            &WebSearchRequest {
                query: "anything".to_owned(),
                max_searches: None,
            },
            &options("sk-ant-api"),
        )
        .await
        .expect_err("a tool error");
        assert_eq!(
            failure.to_string(),
            "Anthropic web search failed: max_uses_exceeded"
        );
        assert_eq!(
            server.await.expect("server"),
            vec![Recorded {
                method: "POST".to_owned(),
                path: "/v1/messages".to_owned(),
                headers: headers([
                    ("accept", "application/json"),
                    ("anthropic-version", "2023-06-01"),
                    ("content-type", "application/json"),
                    ("x-api-key", "sk-ant-api"),
                ]),
                body: Some(json!({
                    "model": "claude-sonnet-4-5",
                    "max_tokens": 4096,
                    "messages": [{ "role": "user", "content": "anything" }],
                    "tools": [{ "type": "web_search_20250305", "name": "web_search" }],
                })),
            }]
        );
    }
}
