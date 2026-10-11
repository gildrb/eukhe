//! The `typesafe` provider. Port of `providers/typesafe.ts`.

use eukhe_types::pi_ai::IndexMap;

use super::classifier_models;
use super::typesafe_models::TYPESAFE_CLASSIFIER_MODELS;
use crate::api::builtin::typesafe_system_one_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider};

/// TS `typesafeProvider()`.
#[must_use]
pub fn typesafe_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "typesafe".to_owned(),
        name: Some("TypeSafe".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("TypeSafe API key", &["TYPESAFE_API_KEY"])),
            oauth: None,
        },
        models: classifier_models(&TYPESAFE_CLASSIFIER_MODELS),
        classifiers: Some(IndexMap::from([(
            "typesafe-system-one".to_owned(),
            typesafe_system_one_api(),
        )])),
        ..CreateProviderOptions::default()
    })
}
