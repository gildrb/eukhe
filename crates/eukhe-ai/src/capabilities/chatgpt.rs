//! The `ChatGPT` subscription dialect: the models the account's plan serves
//! (`GET /codex/models` under `chatgpt.com/backend-api`), asked with the
//! subscription's OAuth token and its account id.

use eukhe_types::pi_ai::{JsonValue, Modality, ProviderHeaders};

use super::http::{api_key, send, trimmed, unexpected, Body, Call};
use super::ListedModel;
use crate::api::openai_codex_responses::backend_headers;
use crate::types::{Model, ProviderRequestOptions};
use crate::utils::diagnostics::Thrown;

const LABEL: &str = "ChatGPT";

/// The client version the listing names. The backend lists the models it
/// serves to this version: an older one hides newer models.
const CLIENT_VERSION: &str = "0.159.0";

/// The listing URL under `base_url` (`.../backend-api` or
/// `.../backend-api/codex`).
fn models_url(base_url: &str) -> String {
    let base = trimmed(base_url);
    let root = base.strip_suffix("/codex").unwrap_or(base);
    format!("{root}/codex/models?client_version={CLIENT_VERSION}")
}

/// The account's headers plus the client version, as a header source.
fn listing_headers(token: &str) -> Result<ProviderHeaders, Thrown> {
    let mut headers: ProviderHeaders = backend_headers(token)?
        .iter()
        .filter_map(|(name, value)| {
            value
                .to_str()
                .ok()
                .map(|value| (name.as_str().to_owned(), Some(value.to_owned())))
        })
        .collect();
    headers.insert("version".to_owned(), Some(CLIENT_VERSION.to_owned()));
    Ok(headers)
}

/// A non-empty trimmed string field.
fn text(value: Option<&JsonValue>) -> Option<&str> {
    value
        .and_then(JsonValue::as_str)
        .map(str::trim)
        .filter(|text| !text.is_empty())
}

/// Whether an entry reasons: a default level or a supported effort other
/// than `none`.
fn reasons(item: &JsonValue) -> bool {
    let effort = |value: Option<&JsonValue>| {
        text(value).is_some_and(|level| !level.eq_ignore_ascii_case("none"))
    };
    effort(item.get("default_reasoning_level"))
        || item
            .get("supported_reasoning_levels")
            .and_then(JsonValue::as_array)
            .is_some_and(|levels| levels.iter().any(|level| effort(level.get("effort"))))
}

/// The text and image modalities an entry names, in that order; `None`
/// when it names neither.
fn modalities(item: &JsonValue) -> Option<Vec<Modality>> {
    let named = item.get("input_modalities")?.as_array()?;
    let has = |wanted: &str| {
        named
            .iter()
            .any(|value| text(Some(value)).is_some_and(|name| name.eq_ignore_ascii_case(wanted)))
    };
    let input: Vec<Modality> = [Modality::Text, Modality::Image]
        .into_iter()
        .filter(|modality| has(modality.as_str()))
        .collect();
    (!input.is_empty()).then_some(input)
}

/// One listed entry; `None` for an entry without a slug or a hidden one.
fn listed(item: &JsonValue) -> Option<ListedModel> {
    let id = text(item.get("slug")).or_else(|| text(item.get("id")))?;
    let hidden = text(item.get("visibility"))
        .is_some_and(|visibility| matches!(visibility, "hide" | "hidden"));
    if hidden {
        return None;
    }
    Some(ListedModel {
        id: id.to_owned(),
        name: text(item.get("display_name")).map(str::to_owned),
        context_window: item
            .get("context_window")
            .and_then(JsonValue::as_u64)
            .filter(|tokens| *tokens > 0),
        max_output_tokens: None,
        reasoning: Some(reasons(item)),
        input: modalities(item),
        chat: Some(true),
    })
}

/// The models the subscription's plan serves now.
#[tracing::instrument(skip_all, fields(model = %model.id))]
pub(crate) async fn list_models(
    model: &Model,
    options: &ProviderRequestOptions,
) -> Result<Vec<ListedModel>, Thrown> {
    let token = api_key(model, options)?;
    let body = send(
        model,
        options,
        Call {
            label: LABEL,
            url: models_url(&model.base_url),
            defaults: listing_headers(token)?,
            body: Body::Get,
        },
    )
    .await?;
    let entries = ["models", "data"]
        .into_iter()
        .find_map(|field| body.get(field).and_then(JsonValue::as_array))
        .ok_or_else(|| unexpected(LABEL, "model list"))?;
    Ok(entries.iter().filter_map(listed).collect())
}

#[cfg(test)]
mod tests {
    use base64::Engine as _;
    use serde_json::json;

    use super::*;
    use crate::capabilities::mock_server::{model, options, serve, Recorded, Reply};

    /// An unsigned token whose claims name account `acc_test`.
    fn token() -> String {
        let claims = json!({
            "https://api.openai.com/auth": { "chatgpt_account_id": "acc_test" }
        });
        let payload =
            base64::engine::general_purpose::STANDARD_NO_PAD.encode(claims.to_string().as_bytes());
        format!("header.{payload}.signature")
    }

    #[tokio::test]
    async fn list_models_reads_the_plan_listing() {
        let (root, server) = serve(vec![Reply::ok(json!({
            "models": [
                {
                    "slug": "gpt-6.2",
                    "display_name": "GPT-6.2",
                    "context_window": 400_000,
                    "default_reasoning_level": "medium",
                    "input_modalities": ["text", "image"],
                    "visibility": "list"
                },
                {
                    "slug": "gpt-6.2-mini",
                    "supported_reasoning_levels": [{ "effort": "none" }],
                    "input_modalities": ["audio"]
                },
                { "slug": "gpt-internal", "visibility": "hide" },
                { "display_name": "no slug" }
            ]
        }))])
        .await;
        let token = token();
        let listed = list_models(
            &model(
                "openai-codex",
                "openai-codex-responses",
                "gpt-5.5",
                &format!("{root}/backend-api"),
            ),
            &options(&token),
        )
        .await
        .expect("models");
        assert_eq!(
            listed,
            vec![
                ListedModel {
                    id: "gpt-6.2".to_owned(),
                    name: Some("GPT-6.2".to_owned()),
                    context_window: Some(400_000),
                    max_output_tokens: None,
                    reasoning: Some(true),
                    input: Some(vec![Modality::Text, Modality::Image]),
                    chat: Some(true),
                },
                ListedModel {
                    id: "gpt-6.2-mini".to_owned(),
                    name: None,
                    context_window: None,
                    max_output_tokens: None,
                    reasoning: Some(false),
                    input: None,
                    chat: Some(true),
                },
            ]
        );
        let recorded: Vec<Recorded> = server.await.expect("server");
        let [request] = recorded.as_slice() else {
            panic!("one request: {recorded:?}");
        };
        assert_eq!(
            (
                request.method.as_str(),
                request.path.as_str(),
                request.headers.get("authorization").map(String::as_str),
                request
                    .headers
                    .get("chatgpt-account-id")
                    .map(String::as_str),
                request.headers.get("version").map(String::as_str),
            ),
            (
                "GET",
                "/backend-api/codex/models?client_version=0.159.0",
                Some(format!("Bearer {token}").as_str()),
                Some("acc_test"),
                Some(CLIENT_VERSION),
            )
        );
    }

    #[tokio::test]
    async fn list_models_refuses_a_body_without_a_list() {
        let (root, _server) = serve(vec![Reply::ok(json!({ "detail": "x" }))]).await;
        let error = list_models(
            &model(
                "openai-codex",
                "openai-codex-responses",
                "gpt-5.5",
                &format!("{root}/backend-api/codex"),
            ),
            &options(&token()),
        )
        .await
        .expect_err("no list");
        assert_eq!(
            error.to_string(),
            unexpected(LABEL, "model list").to_string()
        );
    }
}
