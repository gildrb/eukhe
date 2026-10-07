//! Port of `test/radius-provider.test.ts`.

mod common;

use std::sync::Arc;

use eukhe_pi_ai::auth::{ApiKeyCredential, Credential, InMemoryCredentialStore};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions, ModelsRefreshOptions};
use eukhe_pi_ai::models_store::{
    InMemoryModelsStore, ModelsStore, ModelsStoreEntry, ModelsStoreOperationOptions,
};
use eukhe_pi_ai::providers::radius::{radius_provider, RadiusProviderOptions};
use eukhe_pi_ai::providers::radius_config::{get_radius_models_from_config, RadiusGatewayConfig};
use eukhe_types::pi_ai::{AnyModel, JsonValue};
use serde_json::json;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpListener;

fn radius_config_json(base_url: &str) -> JsonValue {
    json!({
        "baseUrl": base_url,
        "models": [
            {
                "id": "balanced",
                "name": "Fresh Balanced",
                "reasoning": true,
                "input": ["text"],
                "cost": { "input": 1, "output": 2, "cacheRead": 0.1, "cacheWrite": 0 },
                "contextWindow": 424_242,
                "maxTokens": 32000,
            },
            {
                "id": "organization-only",
                "name": "Organization Only",
                "reasoning": false,
                "input": ["text"],
                "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
                "contextWindow": 128_000,
                "maxTokens": 16000,
            },
        ],
    })
}

fn radius_config() -> RadiusGatewayConfig {
    let value = radius_config_json("https://radius.example/v1");
    RadiusGatewayConfig {
        base_url: value["baseUrl"].as_str().expect("baseUrl").to_owned(),
        models: value["models"]
            .as_array()
            .expect("models")
            .iter()
            .map(|model| model.as_object().cloned().expect("model object"))
            .collect(),
    }
}

/// Serves `body` as JSON for every request.
async fn serve_json(body: JsonValue) -> String {
    let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
    let address = listener.local_addr().expect("address");
    let body = body.to_string();
    tokio::spawn(async move {
        while let Ok((mut socket, _)) = listener.accept().await {
            let body = body.clone();
            tokio::spawn(async move {
                let mut data = Vec::new();
                let mut buf = [0u8; 4096];
                while !data.windows(4).any(|window| window == b"\r\n\r\n") {
                    let n = socket.read(&mut buf).await.unwrap_or(0);
                    if n == 0 {
                        return;
                    }
                    data.extend_from_slice(&buf[..n]);
                }
                let response = format!(
                    "HTTP/1.1 200 OK\r\ncontent-type: application/json\r\ncontent-length: {}\r\nconnection: close\r\n\r\n{body}",
                    body.len()
                );
                socket.write_all(response.as_bytes()).await.ok();
                socket.shutdown().await.ok();
            });
        }
    });
    format!("http://127.0.0.1:{}", address.port())
}

#[test]
fn ships_a_static_public_catalog_for_the_default_gateway() {
    let provider = radius_provider(RadiusProviderOptions::default());
    let models = (provider.get_models)().expect("models");
    assert!(!models.is_empty());
    assert!(models.iter().any(|model| model.id == "balanced"
        && model.provider == "radius"
        && model.api.as_str() == "pi-messages"));
}

#[test]
fn does_not_apply_the_public_radius_catalog_to_custom_gateways() {
    let provider = radius_provider(RadiusProviderOptions {
        id: Some("radius-dev".into()),
        gateway: Some("http://localhost:8788".into()),
        ..RadiusProviderOptions::default()
    });
    assert_eq!((provider.get_models)().expect("models"), Vec::new());
}

/// TS mocks `globalThis.fetch` for the default gateway; the Rust config
/// loader has no injectable fetch, so the refreshed catalog is served by a
/// local gateway instead. A custom gateway has no static baseline, so the
/// overlay check is that the refreshed models are exactly the config's.
#[tokio::test]
async fn overlays_refreshed_models_on_the_static_public_catalog() {
    let gateway = serve_json(radius_config_json("https://radius.example/v1")).await;
    let credentials = InMemoryCredentialStore::new();
    common::store(
        &credentials,
        "radius",
        Credential::ApiKey(ApiKeyCredential::with_key("radius-key")),
    )
    .await;
    let models = create_models(CreateModelsOptions {
        credentials: Some(Arc::new(credentials)),
        ..CreateModelsOptions::default()
    });
    models.set_provider(radius_provider(RadiusProviderOptions {
        gateway: Some(gateway),
        ..RadiusProviderOptions::default()
    }));

    let result = models
        .refresh(ModelsRefreshOptions {
            providers: Some(vec!["radius".into()]),
            ..ModelsRefreshOptions::default()
        })
        .await;

    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let balanced = models.get_model("radius", "balanced").expect("balanced");
    assert_eq!(balanced.name, "Fresh Balanced");
    assert_eq!(balanced.base_url, "https://radius.example/v1");
    assert_eq!(balanced.context_window, 424_242);
    assert!(models.get_model("radius", "organization-only").is_some());
    assert_eq!(
        models.get_models(Some("radius")).len(),
        radius_config().models.len()
    );
}

#[tokio::test]
async fn overlays_a_cached_effective_catalog_without_network_access() {
    let store = InMemoryModelsStore::new();
    store
        .write(
            "radius",
            ModelsStoreEntry {
                models: get_radius_models_from_config("radius", &radius_config())
                    .into_iter()
                    .map(AnyModel::Chat)
                    .collect(),
                checked_at: Some(1_700_000_000_000.0),
                ..ModelsStoreEntry::default()
            },
            ModelsStoreOperationOptions::default(),
        )
        .await
        .expect("write");
    let models = create_models(CreateModelsOptions {
        models_store: Some(Arc::new(store)),
        ..CreateModelsOptions::default()
    });
    models.set_provider(radius_provider(RadiusProviderOptions::default()));

    models
        .refresh(ModelsRefreshOptions {
            providers: Some(vec!["radius".into()]),
            allow_network: Some(false),
            ..ModelsRefreshOptions::default()
        })
        .await;

    assert_eq!(
        models
            .get_model("radius", "balanced")
            .map(|model| model.name),
        Some("Fresh Balanced".to_owned())
    );
    assert!(models.get_model("radius", "organization-only").is_some());
}
