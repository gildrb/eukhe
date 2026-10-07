//! Port of `test/bedrock-endpoint-resolution.test.ts`.

use eukhe_pi_ai::api::bedrock_converse_stream::{client_config, BedrockClientConfig};
use eukhe_types::pi_ai::{CacheRetention, Model};
use serde_json::json;

use super::support::{env, get_model, options, EnvGuard};

fn config_for(
    model: &Model,
    extra: serde_json::Value,
    scoped: Option<&[(&str, &str)]>,
) -> BedrockClientConfig {
    let mut options = options(extra);
    options.stream.cache_retention = Some(CacheRetention::None);
    options.stream.request.env = scoped.map(env);
    client_config(model, &options).expect("config")
}

fn opus_48() -> Model {
    get_model("amazon-bedrock", "us.anthropic.claude-opus-4-8")
}

fn eu_sonnet() -> Model {
    get_model(
        "amazon-bedrock",
        "eu.anthropic.claude-sonnet-4-5-20250929-v1:0",
    )
}

#[test]
fn assigns_eu_central_1_runtime_urls_to_built_in_eu_inference_profiles() {
    assert_eq!(
        eu_sonnet().base_url,
        "https://bedrock-runtime.eu-central-1.amazonaws.com"
    );
}

#[tokio::test]
async fn does_not_pin_standard_aws_endpoints_when_aws_region_is_configured() {
    let _env = EnvGuard::new(&[("AWS_REGION", "us-east-2")]).await;
    let config = config_for(&opus_48(), json!({}), None);
    assert_eq!(config.region.as_deref(), Some("us-east-2"));
    assert_eq!(config.endpoint, None);
}

#[tokio::test]
async fn derives_region_from_a_built_in_eu_endpoint_when_no_region_or_profile_is_configured() {
    let _env = EnvGuard::new(&[]).await;
    let config = config_for(&eu_sonnet(), json!({}), None);
    assert_eq!(
        config.endpoint.as_deref(),
        Some("https://bedrock-runtime.eu-central-1.amazonaws.com")
    );
    assert_eq!(config.region.as_deref(), Some("eu-central-1"));
}

#[tokio::test]
async fn handles_missing_regions_for_explicit_scoped_and_ambient_profiles() {
    let guard = EnvGuard::new(&[]).await;
    let model = eu_sonnet();

    let config = config_for(&model, json!({ "profile": "bedrock-profile" }), None);
    assert_eq!(config.profile.as_deref(), Some("bedrock-profile"));
    assert_eq!(
        config.endpoint.as_deref(),
        Some("https://bedrock-runtime.eu-central-1.amazonaws.com")
    );
    assert_eq!(config.region.as_deref(), Some("eu-central-1"));

    let config = config_for(
        &model,
        json!({}),
        Some(&[("AWS_PROFILE", "scoped-bedrock-profile")]),
    );
    assert_eq!(config.profile.as_deref(), Some("scoped-bedrock-profile"));
    assert_eq!(
        config.endpoint.as_deref(),
        Some("https://bedrock-runtime.eu-central-1.amazonaws.com")
    );
    assert_eq!(config.region.as_deref(), Some("eu-central-1"));

    guard.set("AWS_PROFILE", "ambient-bedrock-profile");
    let config = config_for(&model, json!({}), None);
    assert_eq!(config.profile.as_deref(), Some("ambient-bedrock-profile"));
    assert_eq!(config.endpoint, None);
    assert_eq!(config.region, None);
}

#[tokio::test]
async fn still_passes_custom_bedrock_endpoints_through_to_the_sdk_client() {
    let _env = EnvGuard::new(&[("AWS_REGION", "us-west-2")]).await;
    let model = Model {
        base_url: "https://bedrock-vpc.example.com".into(),
        ..opus_48()
    };
    let config = config_for(&model, json!({}), None);
    assert_eq!(
        config.endpoint.as_deref(),
        Some("https://bedrock-vpc.example.com")
    );
    assert_eq!(config.region.as_deref(), Some("us-west-2"));
}

#[tokio::test]
async fn extracts_region_from_inference_profile_arn_regardless_of_aws_region() {
    let _env = EnvGuard::new(&[("AWS_REGION", "us-east-1")]).await;
    let model = Model {
        id: "arn:aws:bedrock:us-west-2:123456789012:application-inference-profile/abc123".into(),
        ..opus_48()
    };
    assert_eq!(
        config_for(&model, json!({}), None).region.as_deref(),
        Some("us-west-2")
    );
}

#[tokio::test]
async fn extracts_region_from_govcloud_inference_profile_arn() {
    let _env = EnvGuard::new(&[("AWS_REGION", "us-east-1")]).await;
    let model = Model {
        id:
            "arn:aws-us-gov:bedrock:us-gov-west-1:123456789012:application-inference-profile/abc123"
                .into(),
        ..opus_48()
    };
    assert_eq!(
        config_for(&model, json!({}), None).region.as_deref(),
        Some("us-gov-west-1")
    );
}

#[tokio::test]
async fn preserves_ambient_aws_auth_for_custom_model_ids_through_compat_dispatch() {
    let _env = EnvGuard::new(&[("AWS_PROFILE", "bedrock-profile")]).await;
    let model = Model {
        id: "arn:aws:bedrock:us-east-1:123456789012:application-inference-profile/example".into(),
        ..opus_48()
    };
    let config = config_for(&model, json!({}), None);
    assert_eq!(config.profile.as_deref(), Some("bedrock-profile"));
    assert_eq!(config.token, None);
    assert_eq!(config.auth_scheme_preference, None);
}

#[tokio::test]
async fn uses_the_generic_api_key_option_as_a_bedrock_bearer_token() {
    let _env = EnvGuard::new(&[]).await;
    let mut options = options(json!({}));
    options.stream.cache_retention = Some(CacheRetention::None);
    options.stream.request.api_key = Some("bedrock-api-key".into());
    let config = client_config(&opus_48(), &options).expect("config");
    assert_eq!(config.token.as_deref(), Some("bedrock-api-key"));
    assert_eq!(
        config.auth_scheme_preference,
        Some(vec!["httpBearerAuth".to_owned()])
    );
}
