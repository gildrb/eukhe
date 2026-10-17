//! The xAI dialect: tokenization (`POST /v1/tokenize-text`).

use eukhe_types::pi_ai::JsonValue;
use serde_json::json;

use super::http::{api_key, header_source, send, unexpected, v1_root, Body, Call};
use super::Tokens;
use crate::types::{Model, ProviderRequestOptions};
use crate::utils::diagnostics::Thrown;

const LABEL: &str = "xAI";

/// The token ids of `text` in `model`'s vocabulary.
pub(crate) async fn tokenize(
    model: &Model,
    text: &str,
    options: &ProviderRequestOptions,
) -> Result<Tokens, Thrown> {
    let key = api_key(model, options)?;
    let body = send(
        model,
        options,
        Call {
            label: LABEL,
            url: format!("{}/tokenize-text", v1_root(&model.base_url)),
            defaults: header_source([("authorization", format!("Bearer {key}"))]),
            body: Body::Post(json!({ "text": text, "model": model.id })),
        },
    )
    .await?;
    let ids = body
        .get("token_ids")
        .and_then(JsonValue::as_array)
        .ok_or_else(|| unexpected(LABEL, "tokenization"))?
        .iter()
        .map(|token| {
            token
                .get("token_id")
                .and_then(JsonValue::as_u64)
                .ok_or_else(|| unexpected(LABEL, "tokenization"))
        })
        .collect::<Result<Vec<_>, Thrown>>()?;
    Ok(Tokens { ids })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::capabilities::mock_server::{headers, model, options, serve, Recorded, Reply};

    #[tokio::test]
    async fn tokenize_posts_the_text_and_model() {
        let (root, server) = serve(vec![Reply::ok(json!({
            "token_ids": [
                { "token_id": 13_902, "string_token": "Hello", "token_bytes": [72, 101, 108, 108, 111] },
                { "token_id": 1_117, "string_token": " world", "token_bytes": [32, 119, 111, 114, 108, 100] }
            ]
        }))])
        .await;
        let model = model("xai", "openai-responses", "grok-4", &format!("{root}/v1"));
        let tokens = tokenize(&model, "Hello world", &options("xai-key"))
            .await
            .expect("tokens");
        assert_eq!(
            tokens,
            Tokens {
                ids: vec![13_902, 1_117]
            }
        );
        assert_eq!(
            server.await.expect("server"),
            vec![Recorded {
                method: "POST".to_owned(),
                path: "/v1/tokenize-text".to_owned(),
                headers: headers([
                    ("accept", "application/json"),
                    ("authorization", "Bearer xai-key"),
                    ("content-type", "application/json"),
                ]),
                body: Some(json!({ "text": "Hello world", "model": "grok-4" })),
            }]
        );
    }
}
