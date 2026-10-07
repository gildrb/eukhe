//! Port of `test/bedrock-credentials.test.ts`: the credential priority of the
//! client configuration.

use eukhe_pi_ai::api::bedrock_converse_stream::{client_config, AwsCredentials};
use eukhe_types::pi_ai::CacheRetention;
use serde_json::json;

use super::support::{env, get_model, options, EnvGuard};

fn config_for(
    extra: serde_json::Value,
    scoped: Option<&[(&str, &str)]>,
) -> eukhe_pi_ai::api::bedrock_converse_stream::BedrockClientConfig {
    let model = get_model("amazon-bedrock", "us.anthropic.claude-opus-4-8");
    let mut options = options(extra);
    options.stream.cache_retention = Some(CacheRetention::None);
    options.stream.request.env = scoped.map(env);
    client_config(&model, &options).expect("config")
}

fn example_credentials() -> AwsCredentials {
    AwsCredentials {
        access_key_id: "AKIAEXAMPLE".into(),
        secret_access_key: "secretexample".into(),
        session_token: None,
    }
}

#[tokio::test]
async fn prefers_explicit_and_scoped_profiles_over_ambient_aws_access_keys() {
    let _env = EnvGuard::new(&[
        ("AWS_ACCESS_KEY_ID", "AKIAEXAMPLE"),
        ("AWS_SECRET_ACCESS_KEY", "secretexample"),
    ])
    .await;

    let config = config_for(json!({ "profile": "explicit-profile" }), None);
    assert_eq!(config.profile.as_deref(), Some("explicit-profile"));
    assert_eq!(config.credentials, None);

    let config = config_for(json!({}), Some(&[("AWS_PROFILE", "scoped-profile")]));
    assert_eq!(config.profile.as_deref(), Some("scoped-profile"));
    assert_eq!(config.credentials, None);
}

#[tokio::test]
async fn uses_ambient_aws_access_keys_when_no_profile_is_configured() {
    let _env = EnvGuard::new(&[
        ("AWS_ACCESS_KEY_ID", "AKIAEXAMPLE"),
        ("AWS_SECRET_ACCESS_KEY", "secretexample"),
    ])
    .await;
    let config = config_for(json!({}), None);
    assert_eq!(config.profile, None);
    assert_eq!(config.credentials, Some(example_credentials()));
}

#[tokio::test]
async fn uses_ambient_aws_access_keys_when_only_an_ambient_profile_is_set() {
    let _env = EnvGuard::new(&[
        ("AWS_ACCESS_KEY_ID", "AKIAEXAMPLE"),
        ("AWS_SECRET_ACCESS_KEY", "secretexample"),
        ("AWS_PROFILE", "ambient-profile"),
    ])
    .await;
    let config = config_for(json!({}), None);
    assert_eq!(config.profile.as_deref(), Some("ambient-profile"));
    assert_eq!(config.credentials, Some(example_credentials()));
}
