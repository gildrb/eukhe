//! The llama.cpp dialect: `llama-server`'s native `/tokenize` and
//! `/apply-template` endpoints at the server root (no `/v1`).

use eukhe_types::pi_ai::{JsonValue, ProviderHeaders, TranscriptContext};
use serde_json::json;

use super::http::{api_key, header_source, send, unexpected, Body, Call};
use super::{TokenCount, Tokens};
use crate::api::llama_cpp_classify::llama_server_root;
use crate::api::openai_completions::compat::get_compat;
use crate::api::openai_completions::convert::{
    convert_messages, convert_tools, request_strict_plan, ConvertCompletionsMessagesOptions,
};
use crate::types::{Model, ProviderRequestOptions};
use crate::utils::diagnostics::Thrown;
use crate::utils::transcript::resolve_transcript_tools;

const LABEL: &str = "llama.cpp";

/// `POST <root><path>` with `body`; the bearer header only when a
/// non-empty key is configured (keyless servers are common).
async fn post(
    model: &Model,
    options: &ProviderRequestOptions,
    path: &str,
    body: JsonValue,
) -> Result<JsonValue, Thrown> {
    send(
        model,
        options,
        Call {
            label: LABEL,
            defaults: api_key(model, options).map_or_else(
                |_| ProviderHeaders::default(),
                |key| header_source([("authorization", format!("Bearer {key}"))]),
            ),
            url: format!("{}{path}", llama_server_root(&model.base_url)),
            body: Body::Post(body),
        },
    )
    .await
}

/// The token ids of a `/tokenize` response: plain ids, or `{id, piece}`
/// objects when pieces were requested.
fn token_ids(body: &JsonValue) -> Result<Vec<u64>, Thrown> {
    body.get("tokens")
        .and_then(JsonValue::as_array)
        .ok_or_else(|| unexpected(LABEL, "tokenization"))?
        .iter()
        .map(|token| {
            let id = match token {
                JsonValue::Object(object) => object.get("id"),
                other => Some(other),
            };
            id.and_then(JsonValue::as_u64)
                .ok_or_else(|| unexpected(LABEL, "tokenization"))
        })
        .collect()
}

/// The transcript's input tokens: the chat template rendered by the server
/// (`/apply-template`), tokenized as a chat completion would be.
#[tracing::instrument(skip_all, fields(model = %model.id))]
pub(crate) async fn count_tokens(
    model: &Model,
    context: &TranscriptContext,
    options: &ProviderRequestOptions,
) -> Result<TokenCount, Thrown> {
    let compat = get_compat(model);
    let messages = convert_messages(
        model,
        context,
        &compat,
        &ConvertCompletionsMessagesOptions::default(),
    )?;
    let mut template = json!({ "model": model.id, "messages": messages });
    let transcript_tools = resolve_transcript_tools(
        context.messages(),
        compat.supports_mid_convo_system_messages == Some(true)
            && compat.supports_mid_convo_tool_additions == Some(true),
    );
    if !transcript_tools.request_tools.is_empty() {
        let strict_plan = request_strict_plan(context.messages(), &transcript_tools, &compat)?;
        template["tools"] = JsonValue::Array(convert_tools(
            &transcript_tools.request_tools,
            &compat,
            &strict_plan,
        )?);
    }
    let rendered = post(model, options, "/apply-template", template).await?;
    let prompt = rendered
        .get("prompt")
        .and_then(JsonValue::as_str)
        .ok_or_else(|| unexpected(LABEL, "template"))?;
    let tokenized = post(
        model,
        options,
        "/tokenize",
        json!({
            "model": model.id,
            "content": prompt,
            "add_special": true,
            "parse_special": true,
        }),
    )
    .await?;
    Ok(TokenCount {
        input_tokens: token_ids(&tokenized)?.len() as u64,
    })
}

/// The token ids of `text`, without special tokens.
#[tracing::instrument(skip_all, fields(model = %model.id))]
pub(crate) async fn tokenize(
    model: &Model,
    text: &str,
    options: &ProviderRequestOptions,
) -> Result<Tokens, Thrown> {
    let body = post(
        model,
        options,
        "/tokenize",
        json!({
            "model": model.id,
            "content": text,
            "add_special": false,
            "parse_special": false,
        }),
    )
    .await?;
    Ok(Tokens {
        ids: token_ids(&body)?,
    })
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;
    use crate::capabilities::mock_server::{headers, model, options, serve, Recorded, Reply};
    use crate::types::Context;
    use crate::utils::transcript::normalize_context;

    #[tokio::test]
    async fn tokenize_posts_the_text_without_a_key() {
        let (root, server) = serve(vec![Reply::ok(json!({
            "tokens": [{ "id": 9906, "piece": "Hello" }, { "id": 1917, "piece": " world" }]
        }))])
        .await;
        let model = model(
            "llama.cpp",
            "openai-completions",
            "qwen3",
            &format!("{root}/v1"),
        );
        let tokens = tokenize(&model, "Hello world", &options(""))
            .await
            .expect("tokenize");
        assert_eq!(
            tokens,
            Tokens {
                ids: vec![9906, 1917]
            }
        );
        assert_eq!(
            server.await.expect("server"),
            vec![Recorded {
                method: "POST".to_owned(),
                path: "/tokenize".to_owned(),
                headers: headers([
                    ("accept", "application/json"),
                    ("content-type", "application/json"),
                ]),
                body: Some(json!({
                    "model": "qwen3",
                    "content": "Hello world",
                    "add_special": false,
                    "parse_special": false,
                })),
            }]
        );
    }

    #[tokio::test]
    async fn count_tokens_renders_the_template_and_tokenizes_it() {
        let (root, server) = serve(vec![
            Reply::ok(json!({ "prompt": "<|system|>Be brief.<|user|>Hi<|assistant|>" })),
            Reply::ok(json!({ "tokens": [1, 2, 3, 4, 5] })),
        ])
        .await;
        let model = model("llama.cpp", "openai-completions", "qwen3", &root);
        let context: Context = serde_json::from_value(json!({
            "systemPrompt": "Be brief.",
            "messages": [{ "role": "user", "content": "Hi", "timestamp": 1 }],
        }))
        .expect("context");
        let count = count_tokens(&model, &normalize_context(context), &options("llama-key"))
            .await
            .expect("count");
        assert_eq!(count, TokenCount { input_tokens: 5 });
        let auth = headers([
            ("accept", "application/json"),
            ("authorization", "Bearer llama-key"),
            ("content-type", "application/json"),
        ]);
        assert_eq!(
            server.await.expect("server"),
            vec![
                Recorded {
                    method: "POST".to_owned(),
                    path: "/apply-template".to_owned(),
                    headers: auth.clone(),
                    body: Some(json!({
                        "model": "qwen3",
                        "messages": [
                            { "role": "system", "content": "Be brief." },
                            { "role": "user", "content": "Hi" },
                        ],
                    })),
                },
                Recorded {
                    method: "POST".to_owned(),
                    path: "/tokenize".to_owned(),
                    headers: auth,
                    body: Some(json!({
                        "model": "qwen3",
                        "content": "<|system|>Be brief.<|user|>Hi<|assistant|>",
                        "add_special": true,
                        "parse_special": true,
                    })),
                },
            ]
        );
    }
}
