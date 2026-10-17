//! The `OpenRouter` dialect: the key's credit usage (`GET /v1/key`) and the
//! images of the `openrouter-images` API as generated images.

use eukhe_types::pi_ai::{AssistantImages, JsonValue, UserContentBlock};

use super::http::{api_key, header_source, send, unexpected, v1_root, Body, Call};
use super::{AccountUsage, GeneratedImage};
use crate::types::{Model, ProviderRequestOptions};
use crate::utils::diagnostics::Thrown;

const LABEL: &str = "OpenRouter";

/// The image blocks of an image-generation result.
pub(crate) fn images_of(output: &AssistantImages) -> Vec<GeneratedImage> {
    output
        .output
        .iter()
        .filter_map(|block| match block {
            UserContentBlock::Image(image) => Some(GeneratedImage::Base64 {
                data: image.data.clone(),
                mime_type: Some(image.mime_type.clone()),
            }),
            UserContentBlock::Text(_) => None,
        })
        .collect()
}

/// The credit usage of the request's API key.
pub(crate) async fn usage(
    model: &Model,
    options: &ProviderRequestOptions,
) -> Result<AccountUsage, Thrown> {
    let key = api_key(model, options)?;
    let body = send(
        model,
        options,
        Call {
            label: LABEL,
            url: format!("{}/key", v1_root(&model.base_url)),
            defaults: header_source([("authorization", format!("Bearer {key}"))]),
            body: Body::Get,
        },
    )
    .await?;
    let data = body
        .get("data")
        .and_then(JsonValue::as_object)
        .ok_or_else(|| unexpected(LABEL, "key"))?;
    Ok(AccountUsage::Credits {
        label: data
            .get("label")
            .and_then(JsonValue::as_str)
            .map(str::to_owned),
        used: data
            .get("usage")
            .and_then(JsonValue::as_f64)
            .ok_or_else(|| unexpected(LABEL, "key usage"))?,
        limit: data.get("limit").and_then(JsonValue::as_f64),
        remaining: data.get("limit_remaining").and_then(JsonValue::as_f64),
        free_tier: data
            .get("is_free_tier")
            .and_then(JsonValue::as_bool)
            .unwrap_or_default(),
    })
}

#[cfg(test)]
mod tests {
    use eukhe_types::pi_ai::{ImageContent, ImagesStopReason, TextContent};
    use serde_json::json;

    use super::*;
    use crate::capabilities::mock_server::{headers, model, options, serve, Recorded, Reply};

    #[tokio::test]
    async fn usage_reads_the_key_endpoint() {
        let (root, server) = serve(vec![Reply::ok(json!({
            "data": {
                "label": "sk-or-v1-abc...xyz",
                "usage": 12.5,
                "limit": 50,
                "limit_remaining": 37.5,
                "is_free_tier": false,
                "usage_daily": 1.25
            }
        }))])
        .await;
        let model = model(
            "openrouter",
            "openai-completions",
            "openai/gpt-5",
            &format!("{root}/api/v1"),
        );
        let usage = usage(&model, &options("or-key")).await.expect("usage");
        assert_eq!(
            usage,
            AccountUsage::Credits {
                label: Some("sk-or-v1-abc...xyz".to_owned()),
                used: 12.5,
                limit: Some(50.0),
                remaining: Some(37.5),
                free_tier: false,
            }
        );
        assert_eq!(
            server.await.expect("server"),
            vec![Recorded {
                method: "GET".to_owned(),
                path: "/api/v1/key".to_owned(),
                headers: headers([
                    ("accept", "application/json"),
                    ("authorization", "Bearer or-key"),
                ]),
                body: None,
            }]
        );
    }

    #[test]
    fn images_of_keeps_the_image_blocks() {
        let output = AssistantImages {
            api: "openrouter-images".to_owned(),
            provider: "openrouter".to_owned(),
            model: "google/gemini-2.5-flash-image".to_owned(),
            output: vec![
                UserContentBlock::Text(TextContent::new("here")),
                UserContentBlock::Image(ImageContent {
                    data: "aGVsbG8=".to_owned(),
                    mime_type: "image/png".to_owned(),
                }),
            ],
            response_id: None,
            usage: None,
            stop_reason: ImagesStopReason::Stop,
            error_message: None,
            timestamp: 0,
        };
        assert_eq!(
            images_of(&output),
            vec![GeneratedImage::Base64 {
                data: "aGVsbG8=".to_owned(),
                mime_type: Some("image/png".to_owned()),
            }]
        );
    }
}
