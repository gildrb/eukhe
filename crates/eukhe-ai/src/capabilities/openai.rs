//! The `OpenAI` dialect, served by `OpenAI` and the hosts that copy its shape
//! (Mistral, xAI, `DeepSeek`, `OpenRouter`, Prime, llama.cpp): every endpoint
//! sits under the base URL's `/v1` root.

use eukhe_types::pi_ai::{JsonObject, JsonValue, ProviderHeaders, TranscriptContext};
use serde_json::json;

use super::http::{api_key, count, header_source, send, unexpected, v1_root, Body, Call};
use super::{
    Compaction, EmbedRequest, Embeddings, GeneratedImage, GeneratedImages, ImageRequest,
    ListedModel, TokenCount, WebSearchRequest, WebSearchResult, WebSource,
};
use crate::api::constrained_sampling::create_grammar_tool_input_properties;
use crate::api::openai_responses::{get_compat, OPENAI_TOOL_CALL_PROVIDERS};
use crate::api::openai_responses_shared::{
    convert_responses_messages, convert_responses_tools, ConvertResponsesMessagesOptions,
    ConvertResponsesToolsOptions,
};
use crate::types::{Model, ProviderRequestOptions};
use crate::utils::diagnostics::Thrown;
use crate::utils::transcript::{get_declared_tools, resolve_transcript_tools};

const LABEL: &str = "OpenAI";

/// `authorization: Bearer <key>` when a key is configured; keyless hosts
/// (llama.cpp) get no auth header.
fn optional_auth(options: &ProviderRequestOptions) -> ProviderHeaders {
    options
        .api_key
        .as_deref()
        .filter(|key| !key.is_empty())
        .map(|key| header_source([("authorization", format!("Bearer {key}"))]))
        .unwrap_or_default()
}

/// The auth header of a key the endpoint requires.
fn required_auth(
    model: &Model,
    options: &ProviderRequestOptions,
) -> Result<ProviderHeaders, Thrown> {
    let key = api_key(model, options)?;
    Ok(header_source([("authorization", format!("Bearer {key}"))]))
}

/// The Responses-API `model`, `input`, and (with `include_tools`) `tools`
/// of `context`, built by the streaming converter.
fn responses_params(
    model: &Model,
    context: &TranscriptContext,
    include_tools: IncludeTools,
) -> Result<JsonObject, Thrown> {
    let compat = get_compat(model);
    let grammar = create_grammar_tool_input_properties(
        Some(&get_declared_tools(context.messages())),
        compat.supports_openai_grammar_tools,
    )?;
    let tool_options = ConvertResponsesToolsOptions {
        strict: None,
        supports_strict_mode: Some(compat.supports_strict_mode),
        supports_openai_grammar_tools: Some(compat.supports_openai_grammar_tools),
        tool_search_result: None,
        strict_cap: crate::quirks::Quirks::of(model).strict_cap(),
    };
    let input = convert_responses_messages(
        model,
        context,
        OPENAI_TOOL_CALL_PROVIDERS,
        &ConvertResponsesMessagesOptions {
            include_system_prompt: None,
            grammar_tool_input_properties: Some(grammar),
            supports_mid_convo_system_messages: Some(compat.supports_mid_convo_system_messages),
            supports_additional_tools: Some(compat.supports_additional_tools),
            supports_tool_search: Some(compat.supports_tool_search),
            tool_options: Some(tool_options),
            explicit_cache_breakpoints: false,
        },
    )?;
    let mut params = JsonObject::new();
    params.insert("model".to_owned(), json!(model.id));
    params.insert("input".to_owned(), JsonValue::Array(input));
    match include_tools {
        IncludeTools::Yes => {
            let transcript_tools = resolve_transcript_tools(
                context.messages(),
                compat.supports_additional_tools || compat.supports_tool_search,
            );
            if !transcript_tools.request_tools.is_empty() {
                params.insert(
                    "tools".to_owned(),
                    JsonValue::Array(convert_responses_tools(
                        &transcript_tools.request_tools,
                        &tool_options,
                    )?),
                );
            }
        }
        IncludeTools::No => {}
    }
    Ok(params)
}

/// Whether [`responses_params`] declares the transcript's tools.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IncludeTools {
    Yes,
    No,
}

/// The input-token count of `context` (`POST /v1/responses/input_tokens`).
#[tracing::instrument(skip_all, fields(model = %model.id))]
pub(crate) async fn count_tokens(
    model: &Model,
    context: &TranscriptContext,
    options: &ProviderRequestOptions,
) -> Result<TokenCount, Thrown> {
    let defaults = required_auth(model, options)?;
    let params = responses_params(model, context, IncludeTools::Yes)?;
    let body = send(
        model,
        options,
        Call {
            label: LABEL,
            url: format!("{}/responses/input_tokens", v1_root(&model.base_url)),
            defaults,
            body: Body::Post(JsonValue::Object(params)),
        },
    )
    .await?;
    let input_tokens =
        count(body.get("input_tokens")).ok_or_else(|| unexpected(LABEL, "token count"))?;
    Ok(TokenCount { input_tokens })
}

/// The provider's models (`GET /v1/models`).
#[tracing::instrument(skip_all, fields(model = %model.id))]
pub(crate) async fn list_models(
    model: &Model,
    options: &ProviderRequestOptions,
) -> Result<Vec<ListedModel>, Thrown> {
    let body = send(
        model,
        options,
        Call {
            label: LABEL,
            url: format!("{}/models", v1_root(&model.base_url)),
            defaults: optional_auth(options),
            body: Body::Get,
        },
    )
    .await?;
    body.get("data")
        .and_then(JsonValue::as_array)
        .ok_or_else(|| unexpected(LABEL, "model list"))?
        .iter()
        .map(|item| {
            let id = item
                .get("id")
                .and_then(JsonValue::as_str)
                .ok_or_else(|| unexpected(LABEL, "model list"))?;
            let name = ["name", "display_name"]
                .into_iter()
                .find_map(|field| item.get(field).and_then(JsonValue::as_str));
            let context_window = ["context_length", "max_context_length", "context_window"]
                .into_iter()
                .find_map(|field| count(item.get(field)));
            let max_output_tokens = count(
                item.get("top_provider")
                    .and_then(|provider| provider.get("max_completion_tokens")),
            );
            Ok(ListedModel {
                id: id.to_owned(),
                name: name.map(str::to_owned),
                context_window,
                max_output_tokens,
            })
        })
        .collect()
}

/// Embeddings of `request.inputs` (`POST /v1/embeddings`).
#[tracing::instrument(skip_all, fields(model = %request.model))]
pub(crate) async fn embed(
    model: &Model,
    request: &EmbedRequest,
    options: &ProviderRequestOptions,
) -> Result<Embeddings, Thrown> {
    let body = send(
        model,
        options,
        Call {
            label: LABEL,
            url: format!("{}/embeddings", v1_root(&model.base_url)),
            defaults: optional_auth(options),
            body: Body::Post(json!({ "model": request.model, "input": request.inputs })),
        },
    )
    .await?;
    let mut indexed = body
        .get("data")
        .and_then(JsonValue::as_array)
        .ok_or_else(|| unexpected(LABEL, "embedding"))?
        .iter()
        .map(|item| {
            let index = count(item.get("index")).ok_or_else(|| unexpected(LABEL, "embedding"))?;
            let vector = item
                .get("embedding")
                .and_then(JsonValue::as_array)
                .ok_or_else(|| unexpected(LABEL, "embedding"))?
                .iter()
                .map(|value| value.as_f64().ok_or_else(|| unexpected(LABEL, "embedding")))
                .collect::<Result<Vec<_>, Thrown>>()?;
            Ok((index, vector))
        })
        .collect::<Result<Vec<_>, Thrown>>()?;
    indexed.sort_by_key(|(index, _)| *index);
    Ok(Embeddings {
        model: body
            .get("model")
            .and_then(JsonValue::as_str)
            .unwrap_or(&request.model)
            .to_owned(),
        vectors: indexed.into_iter().map(|(_, vector)| vector).collect(),
        input_tokens: count(
            body.get("usage")
                .and_then(|usage| usage.get("prompt_tokens")),
        ),
    })
}

/// Images for `request.prompt` (`POST /v1/images/generations`).
#[tracing::instrument(skip_all, fields(model = %request.model))]
pub(crate) async fn generate_image(
    model: &Model,
    request: &ImageRequest,
    options: &ProviderRequestOptions,
) -> Result<GeneratedImages, Thrown> {
    let defaults = required_auth(model, options)?;
    let body = send(
        model,
        options,
        Call {
            label: LABEL,
            url: format!("{}/images/generations", v1_root(&model.base_url)),
            defaults,
            body: Body::Post(json!({
                "model": request.model,
                "prompt": request.prompt,
                "n": request.count,
            })),
        },
    )
    .await?;
    let mime_type = match body.get("output_format").and_then(JsonValue::as_str) {
        Some("png") => Some("image/png"),
        Some("jpeg") => Some("image/jpeg"),
        Some("webp") => Some("image/webp"),
        Some(_) | None => None,
    };
    let images = body
        .get("data")
        .and_then(JsonValue::as_array)
        .ok_or_else(|| unexpected(LABEL, "image generation"))?
        .iter()
        .map(|item| {
            if let Some(data) = item.get("b64_json").and_then(JsonValue::as_str) {
                Ok(GeneratedImage::Base64 {
                    data: data.to_owned(),
                    mime_type: mime_type.map(str::to_owned),
                })
            } else if let Some(url) = item.get("url").and_then(JsonValue::as_str) {
                Ok(GeneratedImage::Url {
                    url: url.to_owned(),
                })
            } else {
                Err(unexpected(LABEL, "image generation"))
            }
        })
        .collect::<Result<Vec<_>, Thrown>>()?;
    Ok(GeneratedImages { images })
}

/// An answer to `request.query` from the `web_search` tool
/// (`POST /v1/responses`).
#[tracing::instrument(skip_all, fields(model = %model.id))]
pub(crate) async fn web_search(
    model: &Model,
    request: &WebSearchRequest,
    options: &ProviderRequestOptions,
) -> Result<WebSearchResult, Thrown> {
    let defaults = required_auth(model, options)?;
    let mut params = JsonObject::new();
    params.insert("model".to_owned(), json!(model.id));
    params.insert("input".to_owned(), json!(request.query));
    params.insert("tools".to_owned(), json!([{ "type": "web_search" }]));
    if let Some(max_searches) = request.max_searches {
        params.insert("max_tool_calls".to_owned(), json!(max_searches));
    }
    let body = send(
        model,
        options,
        Call {
            label: LABEL,
            url: format!("{}/responses", v1_root(&model.base_url)),
            defaults,
            body: Body::Post(JsonValue::Object(params)),
        },
    )
    .await?;
    let output = body
        .get("output")
        .and_then(JsonValue::as_array)
        .ok_or_else(|| unexpected(LABEL, "web search"))?;
    let mut answer = String::new();
    let mut sources: Vec<WebSource> = Vec::new();
    let texts = output
        .iter()
        .filter(|item| item.get("type").and_then(JsonValue::as_str) == Some("message"))
        .filter_map(|item| item.get("content").and_then(JsonValue::as_array))
        .flatten()
        .filter(|part| part.get("type").and_then(JsonValue::as_str) == Some("output_text"));
    for part in texts {
        if let Some(text) = part.get("text").and_then(JsonValue::as_str) {
            answer.push_str(text);
        }
        let citations = part
            .get("annotations")
            .and_then(JsonValue::as_array)
            .into_iter()
            .flatten()
            .filter(|note| note.get("type").and_then(JsonValue::as_str) == Some("url_citation"));
        for citation in citations {
            let Some(url) = citation.get("url").and_then(JsonValue::as_str) else {
                continue;
            };
            if sources.iter().all(|source| source.url != url) {
                sources.push(WebSource {
                    url: url.to_owned(),
                    title: citation
                        .get("title")
                        .and_then(JsonValue::as_str)
                        .map(str::to_owned),
                });
            }
        }
    }
    Ok(WebSearchResult { answer, sources })
}

/// The provider's compacted replacement of `context`
/// (`POST /v1/responses/compact`).
#[tracing::instrument(skip_all, fields(model = %model.id))]
pub(crate) async fn compact(
    model: &Model,
    context: &TranscriptContext,
    options: &ProviderRequestOptions,
) -> Result<Compaction, Thrown> {
    let defaults = required_auth(model, options)?;
    let params = responses_params(model, context, IncludeTools::No)?;
    let body = send(
        model,
        options,
        Call {
            label: LABEL,
            url: format!("{}/responses/compact", v1_root(&model.base_url)),
            defaults,
            body: Body::Post(JsonValue::Object(params)),
        },
    )
    .await?;
    let items = body
        .get("output")
        .and_then(JsonValue::as_array)
        .ok_or_else(|| unexpected(LABEL, "compaction"))?
        .clone();
    Ok(Compaction { items })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::capabilities::mock_server::{headers, model, options, serve, Recorded, Reply};
    use crate::types::{Context, Message, UserContent, UserMessage};
    use crate::utils::transcript::normalize_context;

    fn context() -> TranscriptContext {
        normalize_context(Context {
            system_prompt: Some("Be brief.".to_owned()),
            messages: vec![Message::User(UserMessage {
                content: UserContent::Text("Hello".to_owned()),
                timestamp: 1,
            })],
            tools: Some(vec![serde_json::from_value(json!({
                "name": "lookup",
                "description": "Look a word up",
                "parameters": {
                    "type": "object",
                    "properties": { "word": { "type": "string" } },
                    "required": ["word"]
                }
            }))
            .expect("tool")]),
        })
    }

    fn openai(root: &str) -> Model {
        model("openai", "openai-responses", "gpt-5", &format!("{root}/v1"))
    }

    fn post(path: &str, key: &str, body: JsonValue) -> Recorded {
        Recorded {
            method: "POST".to_owned(),
            path: path.to_owned(),
            headers: headers([
                ("accept", "application/json"),
                ("authorization", &format!("Bearer {key}")),
                ("content-type", "application/json"),
            ]),
            body: Some(body),
        }
    }

    #[tokio::test]
    async fn count_tokens_posts_the_responses_input() {
        let (root, server) = serve(vec![Reply::ok(json!({
            "object": "response.input_tokens",
            "input_tokens": 42
        }))])
        .await;
        let count = count_tokens(&openai(&root), &context(), &options("sk-test"))
            .await
            .expect("count");
        assert_eq!(count, TokenCount { input_tokens: 42 });
        assert_eq!(
            server.await.expect("server"),
            vec![post(
                "/v1/responses/input_tokens",
                "sk-test",
                json!({
                    "model": "gpt-5",
                    "input": [
                        { "role": "system", "content": "Be brief." },
                        { "role": "user", "content": [{ "type": "input_text", "text": "Hello" }] }
                    ],
                    "tools": [{
                        "type": "function",
                        "name": "lookup",
                        "description": "Look a word up",
                        "parameters": {
                            "type": "object",
                            "properties": { "word": { "type": "string" } },
                            "required": ["word"]
                        }
                    }]
                })
            )]
        );
    }

    #[tokio::test]
    async fn list_models_reads_openrouter_and_mistral_items() {
        let (root, server) = serve(vec![Reply::ok(json!({
            "object": "list",
            "data": [
                {
                    "id": "openai/gpt-5",
                    "name": "OpenAI: GPT-5",
                    "context_length": 400_000,
                    "top_provider": { "max_completion_tokens": 128_000 }
                },
                {
                    "id": "mistral-large-latest",
                    "object": "model",
                    "max_context_length": 131_072
                },
                { "id": "gpt-4o", "object": "model", "owned_by": "openai" }
            ]
        }))])
        .await;
        let models = list_models(&openai(&root), &options("sk-test"))
            .await
            .expect("models");
        assert_eq!(
            models,
            vec![
                ListedModel {
                    id: "openai/gpt-5".to_owned(),
                    name: Some("OpenAI: GPT-5".to_owned()),
                    context_window: Some(400_000),
                    max_output_tokens: Some(128_000),
                },
                ListedModel {
                    id: "mistral-large-latest".to_owned(),
                    name: None,
                    context_window: Some(131_072),
                    max_output_tokens: None,
                },
                ListedModel {
                    id: "gpt-4o".to_owned(),
                    name: None,
                    context_window: None,
                    max_output_tokens: None,
                },
            ]
        );
        assert_eq!(
            server.await.expect("server"),
            vec![Recorded {
                method: "GET".to_owned(),
                path: "/v1/models".to_owned(),
                headers: headers([
                    ("accept", "application/json"),
                    ("authorization", "Bearer sk-test"),
                ]),
                body: None,
            }]
        );
    }

    #[tokio::test]
    async fn list_models_without_a_key_sends_no_authorization() {
        let (root, server) = serve(vec![Reply::ok(json!({
            "object": "list",
            "data": [{ "id": "qwen3-8b", "object": "model", "owned_by": "llamacpp" }]
        }))])
        .await;
        let model = model(
            "llama.cpp",
            "openai-completions",
            "qwen3-8b",
            &format!("{root}/v1"),
        );
        let mut keyless = options("");
        keyless.api_key = None;
        let models = list_models(&model, &keyless).await.expect("models");
        assert_eq!(
            models,
            vec![ListedModel {
                id: "qwen3-8b".to_owned(),
                name: None,
                context_window: None,
                max_output_tokens: None,
            }]
        );
        assert_eq!(
            server.await.expect("server"),
            vec![Recorded {
                method: "GET".to_owned(),
                path: "/v1/models".to_owned(),
                headers: headers([("accept", "application/json")]),
                body: None,
            }]
        );
    }

    #[tokio::test]
    async fn embed_orders_vectors_by_index() {
        let (root, server) = serve(vec![Reply::ok(json!({
            "object": "list",
            "data": [
                { "object": "embedding", "index": 1, "embedding": [0.5, -0.25] },
                { "object": "embedding", "index": 0, "embedding": [0.125, 1.0] }
            ],
            "model": "text-embedding-3-small",
            "usage": { "prompt_tokens": 4, "total_tokens": 4 }
        }))])
        .await;
        let request = EmbedRequest {
            model: "text-embedding-3-small".to_owned(),
            inputs: vec!["first".to_owned(), "second".to_owned()],
        };
        let embeddings = embed(&openai(&root), &request, &options("sk-test"))
            .await
            .expect("embeddings");
        assert_eq!(
            embeddings,
            Embeddings {
                model: "text-embedding-3-small".to_owned(),
                vectors: vec![vec![0.125, 1.0], vec![0.5, -0.25]],
                input_tokens: Some(4),
            }
        );
        assert_eq!(
            server.await.expect("server"),
            vec![post(
                "/v1/embeddings",
                "sk-test",
                json!({ "model": "text-embedding-3-small", "input": ["first", "second"] })
            )]
        );
    }

    #[tokio::test]
    async fn generate_image_reads_base64_and_url_images() {
        let (root, server) = serve(vec![Reply::ok(json!({
            "created": 1_700_000_000,
            "output_format": "png",
            "data": [
                { "b64_json": "iVBORw0KGgo=" },
                { "url": "https://images.example/cat.png" }
            ]
        }))])
        .await;
        let request = ImageRequest {
            model: "gpt-image-1".to_owned(),
            prompt: "A cat".to_owned(),
            count: 2,
        };
        let images = generate_image(&openai(&root), &request, &options("sk-test"))
            .await
            .expect("images");
        assert_eq!(
            images,
            GeneratedImages {
                images: vec![
                    GeneratedImage::Base64 {
                        data: "iVBORw0KGgo=".to_owned(),
                        mime_type: Some("image/png".to_owned()),
                    },
                    GeneratedImage::Url {
                        url: "https://images.example/cat.png".to_owned(),
                    },
                ]
            }
        );
        assert_eq!(
            server.await.expect("server"),
            vec![post(
                "/v1/images/generations",
                "sk-test",
                json!({ "model": "gpt-image-1", "prompt": "A cat", "n": 2 })
            )]
        );
    }

    #[tokio::test]
    async fn web_search_joins_text_and_dedups_citations() {
        let citation = |url: &str, title: &str| json!({ "type": "url_citation", "start_index": 0, "end_index": 1, "url": url, "title": title });
        let (root, server) = serve(vec![Reply::ok(json!({
            "object": "response",
            "output": [
                { "type": "web_search_call", "id": "ws_1", "status": "completed" },
                {
                    "type": "message",
                    "role": "assistant",
                    "content": [
                        {
                            "type": "output_text",
                            "text": "Rust 1.90 is out. ",
                            "annotations": [
                                citation("https://blog.rust-lang.org/a", "Announcing"),
                                citation("https://news.example/b", "News")
                            ]
                        },
                        {
                            "type": "output_text",
                            "text": "It ships LLD.",
                            "annotations": [citation("https://blog.rust-lang.org/a", "Again")]
                        }
                    ]
                }
            ]
        }))])
        .await;
        let request = WebSearchRequest {
            query: "latest Rust release".to_owned(),
            max_searches: Some(3),
        };
        let result = web_search(&openai(&root), &request, &options("sk-test"))
            .await
            .expect("search");
        assert_eq!(
            result,
            WebSearchResult {
                answer: "Rust 1.90 is out. It ships LLD.".to_owned(),
                sources: vec![
                    WebSource {
                        url: "https://blog.rust-lang.org/a".to_owned(),
                        title: Some("Announcing".to_owned()),
                    },
                    WebSource {
                        url: "https://news.example/b".to_owned(),
                        title: Some("News".to_owned()),
                    },
                ],
            }
        );
        assert_eq!(
            server.await.expect("server"),
            vec![post(
                "/v1/responses",
                "sk-test",
                json!({
                    "model": "gpt-5",
                    "input": "latest Rust release",
                    "tools": [{ "type": "web_search" }],
                    "max_tool_calls": 3
                })
            )]
        );
    }

    #[tokio::test]
    async fn compact_returns_the_output_items() {
        let items = vec![
            json!({ "type": "message", "role": "user", "content": [{ "type": "input_text", "text": "Hello" }] }),
            json!({ "type": "compaction", "id": "cmp_1", "encrypted_content": "opaque" }),
        ];
        let (root, server) = serve(vec![Reply::ok(json!({
            "object": "response.compaction",
            "output": items
        }))])
        .await;
        let compaction = compact(&openai(&root), &context(), &options("sk-test"))
            .await
            .expect("compaction");
        assert_eq!(compaction, Compaction { items });
        assert_eq!(
            server.await.expect("server"),
            vec![post(
                "/v1/responses/compact",
                "sk-test",
                json!({
                    "model": "gpt-5",
                    "input": [
                        { "role": "system", "content": "Be brief." },
                        { "role": "user", "content": [{ "type": "input_text", "text": "Hello" }] }
                    ]
                })
            )]
        );
    }
}
