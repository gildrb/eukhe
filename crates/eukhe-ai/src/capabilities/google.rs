//! The Gemini API dialect (`google-generative-ai`): token counting
//! (`POST /models/{id}:countTokens`), model listing (`GET /models`),
//! embeddings (`POST /models/{id}:batchEmbedContents`), and grounded web
//! search (`POST /models/{id}:generateContent` with the `google_search`
//! tool). The base URL already names the API version.

use eukhe_types::pi_ai::{JsonObject, JsonValue, TranscriptContext};
use serde_json::json;

use super::http::{api_key, count, header_source, send, trimmed, unexpected, Body, Call};
use super::{
    EmbedRequest, Embeddings, ListedModel, TokenCount, WebSearchRequest, WebSearchResult, WebSource,
};
use crate::api::constrained_sampling::{StrictPlan, StrictSupport};
use crate::api::google_shared::{convert_messages, convert_tools, ToolSchemaField};
use crate::quirks::Quirks;
use crate::types::{Model, ProviderRequestOptions};
use crate::utils::diagnostics::Thrown;
use crate::utils::sanitize_unicode::sanitize_surrogates;
use crate::utils::text::get_system_message_text;
use crate::utils::transcript::{get_current_tools, get_initial_system_message};

const LABEL: &str = "Google";
const API_KEY_HEADER: &str = "x-goog-api-key";
const MODEL_PREFIX: &str = "models/";

/// The input tokens of `context` (messages, system prompt, and tools) on
/// `model`.
#[tracing::instrument(skip_all, fields(model = %model.id))]
pub(crate) async fn count_tokens(
    model: &Model,
    context: &TranscriptContext,
    options: &ProviderRequestOptions,
) -> Result<TokenCount, Thrown> {
    let key = api_key(model, options)?;
    let mut request = JsonObject::new();
    request.insert("model".into(), format!("{MODEL_PREFIX}{}", model.id).into());
    request.insert("contents".into(), convert_messages(model, context).into());
    let system = get_initial_system_message(context.messages())
        .map(get_system_message_text)
        .unwrap_or_default();
    if !system.is_empty() {
        request.insert(
            "systemInstruction".into(),
            json!({ "parts": [{ "text": sanitize_surrogates(&system) }] }),
        );
    }
    let tools = get_current_tools(context.messages());
    let quirks = Quirks::of(model);
    let strict_plan = StrictPlan::new(
        &tools,
        StrictSupport {
            supported: quirks.google_validated_tools().unwrap_or(false),
            cap: quirks.strict_cap(),
        },
        None,
    )?;
    if let Some(declarations) =
        convert_tools(&tools, ToolSchemaField::ParametersJsonSchema, &strict_plan)?
    {
        request.insert("tools".into(), declarations.into());
    }
    let body = send(
        model,
        options,
        Call {
            label: LABEL,
            url: format!(
                "{}/models/{}:countTokens",
                trimmed(&model.base_url),
                model.id
            ),
            defaults: header_source([(API_KEY_HEADER, key.to_owned())]),
            body: Body::Post(json!({ "generateContentRequest": request })),
        },
    )
    .await?;
    let input_tokens =
        count(body.get("totalTokens")).ok_or_else(|| unexpected(LABEL, "token count"))?;
    Ok(TokenCount { input_tokens })
}

/// Every model the key can use, across all pages.
#[tracing::instrument(skip_all, fields(model = %model.id))]
pub(crate) async fn list_models(
    model: &Model,
    options: &ProviderRequestOptions,
) -> Result<Vec<ListedModel>, Thrown> {
    let key = api_key(model, options)?;
    let mut listed = Vec::new();
    let mut page_token: Option<String> = None;
    loop {
        let mut url = format!("{}/models?pageSize=1000", trimmed(&model.base_url));
        if let Some(token) = &page_token {
            url.push_str("&pageToken=");
            url.extend(url::form_urlencoded::byte_serialize(token.as_bytes()));
        }
        let body = send(
            model,
            options,
            Call {
                label: LABEL,
                url,
                defaults: header_source([(API_KEY_HEADER, key.to_owned())]),
                body: Body::Get,
            },
        )
        .await?;
        let models = body
            .get("models")
            .map_or(Ok(&[][..]), |models| {
                models.as_array().map(Vec::as_slice).ok_or(())
            })
            .map_err(|()| unexpected(LABEL, "model list"))?;
        for item in models {
            let name = item
                .get("name")
                .and_then(JsonValue::as_str)
                .ok_or_else(|| unexpected(LABEL, "model list"))?;
            listed.push(ListedModel {
                id: name.strip_prefix(MODEL_PREFIX).unwrap_or(name).to_owned(),
                name: item
                    .get("displayName")
                    .and_then(JsonValue::as_str)
                    .map(str::to_owned),
                context_window: count(item.get("inputTokenLimit")),
                max_output_tokens: count(item.get("outputTokenLimit")),
            });
        }
        page_token = body
            .get("nextPageToken")
            .and_then(JsonValue::as_str)
            .filter(|token| !token.is_empty())
            .map(str::to_owned);
        if page_token.is_none() {
            return Ok(listed);
        }
    }
}

/// One embedding per input of `request`, in input order. Gemini reports no
/// token usage for embeddings.
#[tracing::instrument(skip_all, fields(model = %request.model))]
pub(crate) async fn embed(
    model: &Model,
    request: &EmbedRequest,
    options: &ProviderRequestOptions,
) -> Result<Embeddings, Thrown> {
    let key = api_key(model, options)?;
    let embedding_model = format!("{MODEL_PREFIX}{}", request.model);
    let requests: Vec<JsonValue> = request
        .inputs
        .iter()
        .map(|text| json!({ "model": embedding_model, "content": { "parts": [{ "text": text }] } }))
        .collect();
    let body = send(
        model,
        options,
        Call {
            label: LABEL,
            url: format!(
                "{}/models/{}:batchEmbedContents",
                trimmed(&model.base_url),
                request.model
            ),
            defaults: header_source([(API_KEY_HEADER, key.to_owned())]),
            body: Body::Post(json!({ "requests": requests })),
        },
    )
    .await?;
    let vectors = body
        .get("embeddings")
        .and_then(JsonValue::as_array)
        .ok_or_else(|| unexpected(LABEL, "embedding response"))?
        .iter()
        .map(|embedding| {
            embedding
                .get("values")
                .and_then(JsonValue::as_array)
                .and_then(|values| values.iter().map(JsonValue::as_f64).collect())
                .ok_or_else(|| unexpected(LABEL, "embedding response"))
        })
        .collect::<Result<Vec<Vec<f64>>, Thrown>>()?;
    Ok(Embeddings {
        model: request.model.clone(),
        vectors,
        input_tokens: None,
    })
}

/// A Google Search grounded answer to `request.query` from `model`.
/// `request.max_searches` is ignored: the Gemini `google_search` tool has
/// no search-count field.
#[tracing::instrument(skip_all, fields(model = %model.id))]
pub(crate) async fn web_search(
    model: &Model,
    request: &WebSearchRequest,
    options: &ProviderRequestOptions,
) -> Result<WebSearchResult, Thrown> {
    let key = api_key(model, options)?;
    let body = send(
        model,
        options,
        Call {
            label: LABEL,
            url: format!(
                "{}/models/{}:generateContent",
                trimmed(&model.base_url),
                model.id
            ),
            defaults: header_source([(API_KEY_HEADER, key.to_owned())]),
            body: Body::Post(json!({
                "contents": [{ "role": "user", "parts": [{ "text": request.query }] }],
                "tools": [{ "google_search": {} }],
            })),
        },
    )
    .await?;
    let candidate = body
        .get("candidates")
        .and_then(|candidates| candidates.get(0))
        .ok_or_else(|| unexpected(LABEL, "search response"))?;
    let answer: String = candidate
        .pointer("/content/parts")
        .and_then(JsonValue::as_array)
        .map(|parts| {
            parts
                .iter()
                .filter(|part| part.get("thought") != Some(&JsonValue::Bool(true)))
                .filter_map(|part| part.get("text").and_then(JsonValue::as_str))
                .collect()
        })
        .unwrap_or_default();
    let mut sources: Vec<WebSource> = Vec::new();
    let chunks = candidate
        .pointer("/groundingMetadata/groundingChunks")
        .and_then(JsonValue::as_array)
        .map_or(&[][..], Vec::as_slice);
    for web in chunks.iter().filter_map(|chunk| chunk.get("web")) {
        let Some(url) = web.get("uri").and_then(JsonValue::as_str) else {
            continue;
        };
        if sources.iter().any(|source| source.url == url) {
            continue;
        }
        sources.push(WebSource {
            url: url.to_owned(),
            title: web
                .get("title")
                .and_then(JsonValue::as_str)
                .map(str::to_owned),
        });
    }
    Ok(WebSearchResult { answer, sources })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api::google_shared::test_support::context;
    use crate::capabilities::mock_server::{headers, model, options, serve, Recorded, Reply};

    const API: &str = "google-generative-ai";

    fn gemini(root: &str, id: &str) -> Model {
        model("google", API, id, &format!("{root}/v1beta"))
    }

    fn get(path: &str) -> Recorded {
        Recorded {
            method: "GET".to_owned(),
            path: path.to_owned(),
            headers: headers([
                ("accept", "application/json"),
                ("x-goog-api-key", "gemini-key"),
            ]),
            body: None,
        }
    }

    fn post(path: &str, body: JsonValue) -> Recorded {
        Recorded {
            method: "POST".to_owned(),
            path: path.to_owned(),
            headers: headers([
                ("accept", "application/json"),
                ("content-type", "application/json"),
                ("x-goog-api-key", "gemini-key"),
            ]),
            body: Some(body),
        }
    }

    #[tokio::test]
    async fn count_tokens_covers_the_system_prompt_and_tools() {
        let (root, server) = serve(vec![Reply::ok(json!({ "totalTokens": 42 }))]).await;
        let model = gemini(&root, "gemini-2.5-flash");
        let context = context(&json!({
            "systemPrompt": "Be brief.",
            "messages": [{ "role": "user", "content": "hello", "timestamp": 0 }],
            "tools": [{
                "name": "lookup",
                "description": "Look a word up",
                "parameters": {
                    "type": "object",
                    "properties": { "word": { "type": "string" } },
                    "required": ["word"]
                }
            }]
        }));
        let counted = count_tokens(&model, &context, &options("gemini-key"))
            .await
            .expect("count");
        assert_eq!(counted, TokenCount { input_tokens: 42 });
        assert_eq!(
            server.await.expect("server"),
            vec![post(
                "/v1beta/models/gemini-2.5-flash:countTokens",
                json!({
                    "generateContentRequest": {
                        "model": "models/gemini-2.5-flash",
                        "contents": [{ "role": "user", "parts": [{ "text": "hello" }] }],
                        "systemInstruction": { "parts": [{ "text": "Be brief." }] },
                        "tools": [{
                            "functionDeclarations": [{
                                "name": "lookup",
                                "description": "Look a word up",
                                "parametersJsonSchema": {
                                    "type": "object",
                                    "properties": { "word": { "type": "string" } },
                                    "required": ["word"]
                                }
                            }]
                        }]
                    }
                })
            )]
        );
    }

    #[tokio::test]
    async fn list_models_follows_the_page_token() {
        let (root, server) = serve(vec![
            Reply::ok(json!({
                "models": [{
                    "name": "models/gemini-2.5-flash",
                    "displayName": "Gemini 2.5 Flash",
                    "inputTokenLimit": 1_048_576,
                    "outputTokenLimit": 65_536
                }],
                "nextPageToken": "page-2"
            })),
            Reply::ok(json!({
                "models": [{ "name": "models/text-embedding-004", "inputTokenLimit": 2_048 }]
            })),
        ])
        .await;
        let model = gemini(&root, "gemini-2.5-flash");
        let listed = list_models(&model, &options("gemini-key"))
            .await
            .expect("models");
        assert_eq!(
            listed,
            vec![
                ListedModel {
                    id: "gemini-2.5-flash".to_owned(),
                    name: Some("Gemini 2.5 Flash".to_owned()),
                    context_window: Some(1_048_576),
                    max_output_tokens: Some(65_536),
                },
                ListedModel {
                    id: "text-embedding-004".to_owned(),
                    name: None,
                    context_window: Some(2_048),
                    max_output_tokens: None,
                },
            ]
        );
        assert_eq!(
            server.await.expect("server"),
            vec![
                get("/v1beta/models?pageSize=1000"),
                get("/v1beta/models?pageSize=1000&pageToken=page-2"),
            ]
        );
    }

    #[tokio::test]
    async fn embed_batches_every_input() {
        let (root, server) = serve(vec![Reply::ok(json!({
            "embeddings": [{ "values": [0.5, -0.25] }, { "values": [1.0, 0.0] }]
        }))])
        .await;
        let model = gemini(&root, "gemini-2.5-flash");
        let request = EmbedRequest {
            model: "gemini-embedding-001".to_owned(),
            inputs: vec!["first".to_owned(), "second".to_owned()],
        };
        let embeddings = embed(&model, &request, &options("gemini-key"))
            .await
            .expect("embeddings");
        assert_eq!(
            embeddings,
            Embeddings {
                model: "gemini-embedding-001".to_owned(),
                vectors: vec![vec![0.5, -0.25], vec![1.0, 0.0]],
                input_tokens: None,
            }
        );
        assert_eq!(
            server.await.expect("server"),
            vec![post(
                "/v1beta/models/gemini-embedding-001:batchEmbedContents",
                json!({
                    "requests": [
                        { "model": "models/gemini-embedding-001", "content": { "parts": [{ "text": "first" }] } },
                        { "model": "models/gemini-embedding-001", "content": { "parts": [{ "text": "second" }] } }
                    ]
                })
            )]
        );
    }

    #[tokio::test]
    async fn web_search_grounds_with_google_search() {
        let (root, server) = serve(vec![Reply::ok(json!({
            "candidates": [{
                "content": {
                    "role": "model",
                    "parts": [
                        { "text": "planning", "thought": true },
                        { "text": "Rust 1.90 " },
                        { "text": "shipped." }
                    ]
                },
                "groundingMetadata": {
                    "groundingChunks": [
                        { "web": { "uri": "https://blog.rust-lang.org/a", "title": "Rust Blog" } },
                        { "web": { "uri": "https://example.com/b" } },
                        { "web": { "uri": "https://blog.rust-lang.org/a", "title": "Rust Blog" } }
                    ]
                }
            }]
        }))])
        .await;
        let model = gemini(&root, "gemini-2.5-flash");
        let request = WebSearchRequest {
            query: "latest rust release".to_owned(),
            max_searches: Some(3),
        };
        let result = web_search(&model, &request, &options("gemini-key"))
            .await
            .expect("search");
        assert_eq!(
            result,
            WebSearchResult {
                answer: "Rust 1.90 shipped.".to_owned(),
                sources: vec![
                    WebSource {
                        url: "https://blog.rust-lang.org/a".to_owned(),
                        title: Some("Rust Blog".to_owned()),
                    },
                    WebSource {
                        url: "https://example.com/b".to_owned(),
                        title: None,
                    },
                ],
            }
        );
        assert_eq!(
            server.await.expect("server"),
            vec![post(
                "/v1beta/models/gemini-2.5-flash:generateContent",
                json!({
                    "contents": [{ "role": "user", "parts": [{ "text": "latest rust release" }] }],
                    "tools": [{ "google_search": {} }]
                })
            )]
        );
    }
}
