//! The `vercel-ai-gateway` provider. Port of `providers/vercel-ai-gateway.ts`.

use eukhe_types::pi_ai::IndexMap;

use super::vercel_ai_gateway_models::{
    VERCEL_AI_GATEWAY_CLASSIFIER_MODELS, VERCEL_AI_GATEWAY_MODELS,
};
use super::{chat_models, classifier_models};
use crate::api::builtin::{anthropic_messages_api, typesafe_system_one_api};
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `vercelAIGatewayProvider()`.
#[must_use]
pub fn vercel_ai_gateway_provider() -> Provider {
    let mut models = chat_models(&VERCEL_AI_GATEWAY_MODELS);
    models.extend(classifier_models(&VERCEL_AI_GATEWAY_CLASSIFIER_MODELS));
    build_provider(CreateProviderOptions {
        id: "vercel-ai-gateway".to_owned(),
        name: Some("Vercel AI Gateway".to_owned()),
        base_url: Some("https://ai-gateway.vercel.sh".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth(
                "Vercel AI Gateway API key",
                &["AI_GATEWAY_API_KEY"],
            )),
            oauth: None,
        },
        models,
        api: Some(ProviderApi::Single(anthropic_messages_api())),
        // AI Gateway serves TypeSafe's System One protocol at /typesafe/v1/systemone.
        classifiers: Some(IndexMap::from([(
            "typesafe-system-one".to_owned(),
            typesafe_system_one_api(),
        )])),
        ..CreateProviderOptions::default()
    })
}
