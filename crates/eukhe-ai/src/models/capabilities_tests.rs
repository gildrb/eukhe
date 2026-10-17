use eukhe_types::pi_ai::Context;
use serde_json::json;

use super::*;
use crate::capabilities::mock_server::{headers, serve, Recorded, Reply};
use crate::capabilities::CapabilitySupport;
use crate::models::{create_models, CreateModelsOptions};
use crate::providers::all::builtin_providers;

fn models() -> Models {
    let models = create_models(CreateModelsOptions::default());
    for provider in builtin_providers() {
        models.set_provider(provider);
    }
    models
}

fn catalog_model(models: &Models, provider: &str, id: &str) -> Model {
    models
        .get_model(provider, id)
        .unwrap_or_else(|| panic!("{provider}/{id} in the catalog"))
}

/// A capabilities row: `native` capabilities with their dialect, every
/// other capability unsupported, in [`Capability::ALL`] order.
fn row(
    provider: &str,
    api: &str,
    base_url: &str,
    native: &[(Capability, Dialect)],
) -> Capabilities {
    Capabilities {
        provider: provider.to_owned(),
        api: api.to_owned(),
        base_url: base_url.to_owned(),
        entries: Capability::ALL
            .into_iter()
            .map(|capability| CapabilitySupport {
                capability,
                support: native
                    .iter()
                    .find(|(native, _)| *native == capability)
                    .map_or(Support::Unsupported, |(_, dialect)| Support::Native {
                        dialect: *dialect,
                        endpoint: dialect.endpoint(capability).expect("an implemented pair"),
                    }),
            })
            .collect(),
    }
}

#[test]
fn a_model_lists_the_capabilities_its_host_rules_give() {
    let models = models();
    let claude = catalog_model(&models, "anthropic", "claude-haiku-4-5");
    let groq = catalog_model(&models, "groq", "llama-3.1-8b-instant");
    assert_eq!(
        (models.capabilities(&claude), models.capabilities(&groq)),
        (
            Capabilities {
                provider: "anthropic".to_owned(),
                api: "anthropic-messages".to_owned(),
                base_url: "https://api.anthropic.com".to_owned(),
                entries: vec![
                    CapabilitySupport {
                        capability: Capability::CountTokens,
                        support: Support::Native {
                            dialect: Dialect::Anthropic,
                            endpoint: "POST /v1/messages/count_tokens",
                        },
                    },
                    CapabilitySupport {
                        capability: Capability::ListModels,
                        support: Support::Native {
                            dialect: Dialect::Anthropic,
                            endpoint: "GET /v1/models",
                        },
                    },
                    CapabilitySupport {
                        capability: Capability::Embed,
                        support: Support::Unsupported,
                    },
                    CapabilitySupport {
                        capability: Capability::GenerateImage,
                        support: Support::Unsupported,
                    },
                    CapabilitySupport {
                        capability: Capability::Tokenize,
                        support: Support::Unsupported,
                    },
                    CapabilitySupport {
                        capability: Capability::Usage,
                        support: Support::Unsupported,
                    },
                    CapabilitySupport {
                        capability: Capability::WebSearch,
                        support: Support::Native {
                            dialect: Dialect::Anthropic,
                            endpoint: "POST /v1/messages (web_search_20250305 tool)",
                        },
                    },
                    CapabilitySupport {
                        capability: Capability::Compact,
                        support: Support::Unsupported,
                    },
                ],
            },
            row(
                "groq",
                "openai-completions",
                "https://api.groq.com/openai/v1",
                &[]
            ),
        )
    );
}

#[test]
fn a_provider_lists_one_row_per_api_and_base_url() {
    let models = models();
    let openrouter = [
        (Capability::ListModels, Dialect::OpenAi),
        (Capability::GenerateImage, Dialect::OpenRouter),
        (Capability::Usage, Dialect::OpenRouter),
    ];
    let mut rows = models.provider_capabilities("openrouter");
    rows.sort_by(|left, right| left.api.cmp(&right.api));
    assert_eq!(
        rows,
        vec![
            row(
                "openrouter",
                "anthropic-messages",
                "https://openrouter.ai/api",
                &openrouter
            ),
            row(
                "openrouter",
                "openai-completions",
                "https://openrouter.ai/api/v1",
                &openrouter
            ),
        ]
    );
    assert_eq!(
        (
            models.provider_capabilities("xai"),
            models.provider_capabilities("no-such-provider")
        ),
        (
            vec![row(
                "xai",
                "openai-responses",
                "https://api.x.ai/v1",
                &[
                    (Capability::ListModels, Dialect::OpenAi),
                    (Capability::GenerateImage, Dialect::OpenAi),
                    (Capability::Tokenize, Dialect::Xai),
                ]
            )],
            Vec::new()
        )
    );
}

fn unsupported_of<T: std::fmt::Debug>(result: Result<T, CapabilityError>) -> Unsupported {
    match result {
        Err(CapabilityError::Unsupported(unsupported)) => unsupported,
        other => panic!("expected Unsupported, got {other:?}"),
    }
}

#[tokio::test]
async fn an_operation_the_provider_lacks_is_unsupported_before_any_auth_or_request() {
    let models = models();
    // groq has no capability rules and no credential: reaching auth would
    // fail with an auth error instead.
    let groq = catalog_model(&models, "groq", "llama-3.1-8b-instant");
    let options = ModelsCapabilityOptions::default;
    let context = || Context {
        system_prompt: None,
        messages: Vec::new(),
        tools: None,
    };
    let embed = EmbedRequest {
        model: "e".to_owned(),
        inputs: vec!["x".to_owned()],
    };
    let image = ImageRequest {
        model: "i".to_owned(),
        prompt: "p".to_owned(),
        count: 1,
    };
    let search = WebSearchRequest {
        query: "q".to_owned(),
        max_searches: None,
    };
    let unsupported = vec![
        unsupported_of(models.count_tokens(&groq, context(), options()).await),
        unsupported_of(models.list_models(&groq, options()).await),
        unsupported_of(models.embed(&groq, &embed, options()).await),
        unsupported_of(models.generate_image(&groq, &image, options()).await),
        unsupported_of(models.tokenize(&groq, "x", options()).await),
        unsupported_of(models.usage(&groq, options()).await),
        unsupported_of(models.web_search(&groq, &search, options()).await),
        unsupported_of(models.compact(&groq, context(), options()).await),
    ];
    assert_eq!(
        unsupported,
        Capability::ALL
            .into_iter()
            .map(|capability| Unsupported {
                capability,
                provider: "groq".to_owned(),
            })
            .collect::<Vec<_>>()
    );
}

#[tokio::test]
async fn an_operation_resolves_auth_and_runs_the_dialect_of_the_host() {
    let (root, server) = serve(vec![Reply::ok(json!({
        "token_ids": [{ "token_id": 7, "string_token": "hi", "token_bytes": [104, 105] }]
    }))])
    .await;
    let models = models();
    let mut grok = catalog_model(&models, "xai", "grok-4.3");
    grok.base_url = format!("{root}/v1");
    let options = ModelsCapabilityOptions::from(CapabilityOptions {
        request: ProviderRequestOptions {
            api_key: Some("xai-key".to_owned()),
            max_retries: Some(0),
            ..ProviderRequestOptions::default()
        },
    });
    let tokens = models.tokenize(&grok, "hi", options).await.expect("tokens");
    assert_eq!(tokens, Tokens { ids: vec![7] });
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
            body: Some(json!({ "text": "hi", "model": "grok-4.3" })),
        }]
    );
}
