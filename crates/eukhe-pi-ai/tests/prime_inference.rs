//! Tests of the eukhe `prime-inference` provider (ported from the
//! `crates/eukhe-models` prime-inference tests, plus provider refresh
//! behavior in the new `Models` structure).

mod common;

use std::sync::Arc;

use eukhe_pi_ai::auth::{AuthResolutionOverrides, InMemoryCredentialStore};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions, ModelsRefreshOptions};
use eukhe_pi_ai::models_store::{InMemoryModelsStore, ModelsStore, ModelsStoreOperationOptions};
use eukhe_pi_ai::providers::prime_inference::{
    build_prime_inference_models, is_private_prime_inference_model_id,
    parse_prime_inference_model_catalog, prime_inference_provider_with_base_url,
    prime_inference_reasoning_controls, EmptyCatalog, PrimeInferenceEntry, PrivateModels,
};
use eukhe_pi_ai::providers::prime_inference_models::PRIME_INFERENCE_MODELS;
use eukhe_types::pi_ai::{
    CacheControlFormat, Model, ModelThinkingLevel, ThinkingFormat, ThinkingLevelMap,
};
use serde_json::{json, Value};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpListener;

fn wire_entry(id: &str, input: f64, output: f64) -> Value {
    json!({
        "id": id,
        "display_name": id,
        "pricing": {"input_usd_per_mtok": input, "output_usd_per_mtok": output},
        "specs": {
            "context_window": 200_000,
            "max_output_tokens": 32_768,
            "supports_reasoning": true,
            "modalities": {"input": ["text", "image"], "output": ["text"]},
        },
    })
}

fn payload(ids: &[&str]) -> Value {
    json!({"data": ids.iter().map(|id| wire_entry(id, 1.0, 2.0)).collect::<Vec<_>>()})
}

fn compiled() -> Vec<Model> {
    PRIME_INFERENCE_MODELS.values().cloned().collect()
}

#[test]
fn ships_the_compiled_offline_catalog() {
    let models = compiled();
    assert_eq!(models.len(), 110);
    assert_eq!(
        models
            .iter()
            .filter(|model| model.featured == Some(true))
            .count(),
        31
    );
    assert!(models
        .iter()
        .all(|model| model.provider == "prime-inference"
            && model.api == "openai-completions"
            && !is_private_prime_inference_model_id(&model.id)));
}

#[test]
fn private_ids_are_recognized() {
    assert!(is_private_prime_inference_model_id("internal/foo"));
    assert!(is_private_prime_inference_model_id("DEV/bar"));
    assert!(is_private_prime_inference_model_id("x:y"));
    assert!(!is_private_prime_inference_model_id(
        "anthropic/claude-fable-5"
    ));
}

#[test]
fn parse_filters_entries_without_tool_support() {
    let mut with_tools = wire_entry("z-ai/glm-5.3", 1.0, 2.0);
    with_tools["supported_parameters"] =
        json!(["max_tokens", "temperature", "tools", "tool_choice"]);
    let mut without_tools = wire_entry("meta-llama/Llama-3.2-1B-Instruct", 1.0, 2.0);
    without_tools["supported_parameters"] = json!(["max_tokens", "temperature", "top_p"]);
    let undeclared = wire_entry("qwen/qwen3.8-max", 1.0, 4.0);
    let value = json!({"data": [with_tools, without_tools, undeclared]});
    let entries =
        parse_prime_inference_model_catalog(&value, EmptyCatalog::Reject).expect("entries");
    let ids: Vec<&str> = entries.iter().map(|entry| entry.id.as_str()).collect();
    assert_eq!(ids, ["z-ai/glm-5.3", "qwen/qwen3.8-max"]);
}

#[test]
fn parse_drops_bad_entries_and_rejects_duplicates() {
    let value = json!({"data": [
        wire_entry("good", 1.0, 2.0),
        {"id": "no-pricing"},
        {"id": "good", "pricing": {"input_usd_per_mtok": 1.0, "output_usd_per_mtok": 1.0}},
    ]});
    let error =
        parse_prime_inference_model_catalog(&value, EmptyCatalog::Reject).expect_err("duplicate");
    assert!(error.contains("Duplicate"), "{error}");
    let value = json!({"data": [
        wire_entry("good", 1.0, 2.0),
        {"id": "no-pricing"},
        {"id": "", "pricing": {"input_usd_per_mtok": 1.0, "output_usd_per_mtok": 1.0}},
    ]});
    let entries =
        parse_prime_inference_model_catalog(&value, EmptyCatalog::Reject).expect("kept rest");
    assert_eq!(entries.len(), 1);
    assert!(
        parse_prime_inference_model_catalog(&json!({"data": []}), EmptyCatalog::Reject).is_err()
    );
    assert!(parse_prime_inference_model_catalog(&json!({"data": []}), EmptyCatalog::Allow).is_ok());
    assert!(parse_prime_inference_model_catalog(&json!({}), EmptyCatalog::Reject).is_err());
}

#[test]
fn build_gates_on_coverage() {
    let compiled = compiled();
    let ids: Vec<&str> = compiled
        .iter()
        .map(|model| model.id.as_str())
        .take(60)
        .collect();
    let entries =
        parse_prime_inference_model_catalog(&payload(&ids), EmptyCatalog::Reject).expect("entries");
    let built = build_prime_inference_models(&compiled, &entries, PrivateModels::Exclude, None)
        .expect("coverage met (60 >= 55)");
    assert_eq!(built.len(), 60);
    assert!(built
        .iter()
        .all(|model| model.provider == "prime-inference"));

    let thin: Vec<&str> = compiled
        .iter()
        .map(|model| model.id.as_str())
        .take(5)
        .collect();
    let entries = parse_prime_inference_model_catalog(&payload(&thin), EmptyCatalog::Reject)
        .expect("entries");
    assert!(
        build_prime_inference_models(&compiled, &entries, PrivateModels::Exclude, None).is_none(),
        "coverage gate rejects thin fetches"
    );
}

#[test]
fn build_requires_full_specs_without_a_template() {
    let unknown = json!({"data": [{
        "id": "brand/new-model",
        "pricing": {"input_usd_per_mtok": 1.0, "output_usd_per_mtok": 1.0},
    }]});
    let entries =
        parse_prime_inference_model_catalog(&unknown, EmptyCatalog::Reject).expect("entries");
    let built =
        build_prime_inference_models(&compiled(), &entries, PrivateModels::Exclude, Some(0))
            .expect("built");
    assert!(built.is_empty(), "entry without template and specs dropped");
}

#[test]
fn anthropic_entries_get_cache_economics() {
    let compiled = compiled();
    let mut value = payload(
        &compiled
            .iter()
            .map(|model| model.id.as_str())
            .take(60)
            .collect::<Vec<_>>(),
    );
    value["data"].as_array_mut().expect("data").push(wire_entry(
        "anthropic/live-only-model",
        2.0,
        4.0,
    ));
    let entries =
        parse_prime_inference_model_catalog(&value, EmptyCatalog::Reject).expect("entries");
    let built = build_prime_inference_models(&compiled, &entries, PrivateModels::Exclude, None)
        .expect("built");
    let anthropic = built
        .iter()
        .find(|model| model.id == "anthropic/live-only-model")
        .expect("live-only model");
    assert!((anthropic.cost.cache_read - 0.2).abs() < 1e-9);
    assert!((anthropic.cost.cache_write - 2.5).abs() < 1e-9);
    let compat = anthropic
        .compat
        .as_ref()
        .and_then(|compat| compat.as_openai_completions())
        .expect("completions compat");
    assert_eq!(
        compat.cache_control_format,
        Some(CacheControlFormat::Anthropic)
    );
}

#[test]
fn parses_and_sanitizes_live_reasoning_declarations() {
    let value = json!({"data": [{
        "id": "z-ai/glm-5.3",
        "display_name": "GLM 5.3",
        "pricing": {"input_usd_per_mtok": 1.4, "output_usd_per_mtok": 4.4},
        "supported_parameters": ["max_tokens", "reasoning", "reasoning_effort", "tools", 42, null],
        "reasoning": {"supported_efforts": ["low", "high", "max", "high", null], "mandatory": true},
    }]});
    let entries =
        parse_prime_inference_model_catalog(&value, EmptyCatalog::Reject).expect("entries");
    assert_eq!(entries.len(), 1);
    let strings = |values: &[&str]| -> Option<Vec<String>> {
        Some(values.iter().map(|v| (*v).to_owned()).collect())
    };
    assert_eq!(
        entries[0].supported_parameters,
        strings(&["max_tokens", "reasoning", "reasoning_effort", "tools"])
    );
    assert_eq!(
        entries[0].reasoning_efforts,
        strings(&["low", "high", "max"])
    );
    assert_eq!(entries[0].reasoning_mandatory, Some(true));
}

fn declared_entry(
    supported: Option<&[&str]>,
    efforts: Option<&[&str]>,
    mandatory: Option<bool>,
) -> PrimeInferenceEntry {
    PrimeInferenceEntry {
        supported_parameters: supported
            .map(|parameters| parameters.iter().map(|p| (*p).to_owned()).collect()),
        reasoning_efforts: efforts.map(|levels| levels.iter().map(|l| (*l).to_owned()).collect()),
        reasoning_mandatory: mandatory,
        ..PrimeInferenceEntry::default()
    }
}

fn level_map(pairs: &[(ModelThinkingLevel, Option<&str>)]) -> ThinkingLevelMap {
    pairs
        .iter()
        .map(|(level, value)| (*level, value.map(str::to_owned)))
        .collect()
}

#[test]
fn maps_declared_route_shapes_onto_reasoning_controls() {
    use ModelThinkingLevel::{High, Low, Max, Medium, Minimal, Off, Xhigh};
    let controls = prime_inference_reasoning_controls(&declared_entry(
        Some(&["reasoning", "reasoning_effort"]),
        Some(&["low", "high", "max"]),
        Some(true),
    ))
    .expect("effort route declares controls");
    assert!(controls.supports_reasoning_effort);
    assert_eq!(controls.thinking_format, None);
    assert_eq!(
        controls.thinking_level_map,
        Some(level_map(&[
            (Off, None),
            (Minimal, None),
            (Low, Some("low")),
            (Medium, None),
            (High, Some("high")),
            (Xhigh, None),
            (Max, Some("max")),
        ]))
    );

    let controls = prime_inference_reasoning_controls(&declared_entry(
        Some(&["reasoning", "reasoning_effort"]),
        Some(&["xhigh", "high"]),
        None,
    ))
    .expect("effort route declares controls");
    assert!(controls.supports_reasoning_effort);
    assert_eq!(
        controls.thinking_level_map,
        Some(level_map(&[
            (Off, Some("none")),
            (Minimal, None),
            (Low, None),
            (Medium, None),
            (High, Some("high")),
            (Xhigh, Some("xhigh")),
            (Max, None),
        ]))
    );

    // Toggle routes: the reasoning object only, through the openrouter format.
    let toggle_map = level_map(&[
        (Minimal, None),
        (Low, None),
        (Medium, None),
        (Xhigh, None),
        (Max, None),
        (High, Some("high")),
    ]);
    for efforts in [None, Some(&["high"][..])] {
        let controls = prime_inference_reasoning_controls(&declared_entry(
            Some(&["reasoning"]),
            efforts,
            None,
        ))
        .expect("toggle route declares controls");
        assert!(!controls.supports_reasoning_effort);
        assert_eq!(controls.thinking_format, Some(ThinkingFormat::OpenRouter));
        assert_eq!(controls.thinking_level_map, Some(toggle_map.clone()));
    }

    // Reasoning-free route: no reasoning parameter is ever sent.
    let controls =
        prime_inference_reasoning_controls(&declared_entry(Some(&["max_tokens"]), None, None))
            .expect("reasoning-free route declares controls");
    assert!(!controls.supports_reasoning_effort);
    assert_eq!(controls.thinking_format, None);
    assert_eq!(controls.thinking_level_map, None);

    // Route without declarations: no controls; callers keep templates.
    assert!(prime_inference_reasoning_controls(&declared_entry(None, None, None)).is_none());
}

/// Serves one HTTP response per connection: `status` with `body`; returns
/// the base URL and a channel of the raw requests received.
async fn serve(
    status: u16,
    body: String,
) -> (String, tokio::sync::mpsc::UnboundedReceiver<String>) {
    let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
    let address = listener.local_addr().expect("address");
    let (sender, receiver) = tokio::sync::mpsc::unbounded_channel();
    tokio::spawn(async move {
        loop {
            let Ok((mut socket, _)) = listener.accept().await else {
                return;
            };
            let mut buffer = vec![0u8; 16_384];
            let read = socket.read(&mut buffer).await.unwrap_or(0);
            let _ = sender.send(String::from_utf8_lossy(&buffer[..read]).into_owned());
            let response = format!(
                "HTTP/1.1 {status} X\r\ncontent-type: application/json\r\ncontent-length: {}\r\nconnection: close\r\n\r\n{body}",
                body.len()
            );
            let _ = socket.write_all(response.as_bytes()).await;
        }
    });
    (format!("http://{address}"), receiver)
}

#[tokio::test]
async fn refresh_replaces_the_offline_catalog_with_the_live_one() {
    let ids: Vec<String> = compiled()
        .iter()
        .map(|model| model.id.clone())
        .take(60)
        .collect();
    let id_refs: Vec<&str> = ids.iter().map(String::as_str).collect();
    let (base_url, mut requests) = serve(200, payload(&id_refs).to_string()).await;
    let store = Arc::new(InMemoryModelsStore::new());
    let credentials = Arc::new(InMemoryCredentialStore::new());
    common::store(
        credentials.as_ref(),
        "prime-inference",
        common::api_key("pk-test"),
    )
    .await;
    let models = create_models(CreateModelsOptions {
        credentials: Some(credentials),
        models_store: Some(store.clone()),
        ..CreateModelsOptions::default()
    });
    models.set_provider(prime_inference_provider_with_base_url(&base_url));
    assert_eq!(models.get_models(Some("prime-inference")).len(), 110);

    let result = models.refresh(ModelsRefreshOptions::default()).await;
    assert_eq!(result.errors.len(), 0, "{:?}", result.errors);
    assert_eq!(models.get_models(Some("prime-inference")).len(), 60);
    let request = requests.recv().await.expect("request");
    assert!(request.starts_with("GET /models "), "{request}");
    assert!(
        request
            .to_ascii_lowercase()
            .contains("authorization: bearer pk-test"),
        "{request}"
    );
    let stored = store
        .read("prime-inference", ModelsStoreOperationOptions::default())
        .await
        .expect("read")
        .expect("persisted");
    assert_eq!(stored.models.len(), 60);
    assert!(stored.checked_at.is_some());

    // Fresh within the hour: a second refresh does not fetch.
    let again = models.refresh(ModelsRefreshOptions::default()).await;
    assert_eq!(again.errors.len(), 0);
    assert!(requests.try_recv().is_err());
}

#[tokio::test]
async fn unauthorized_refresh_clears_the_persisted_catalog() {
    let (base_url, _requests) = serve(401, "{}".to_owned()).await;
    let store = Arc::new(InMemoryModelsStore::new());
    let credentials = Arc::new(InMemoryCredentialStore::new());
    common::store(
        credentials.as_ref(),
        "prime-inference",
        common::api_key("revoked"),
    )
    .await;
    let models = create_models(CreateModelsOptions {
        credentials: Some(credentials),
        models_store: Some(store.clone()),
        ..CreateModelsOptions::default()
    });
    models.set_provider(prime_inference_provider_with_base_url(&base_url));

    let result = models
        .refresh(ModelsRefreshOptions {
            force: Some(true),
            ..ModelsRefreshOptions::default()
        })
        .await;
    assert_eq!(
        result
            .errors
            .get("prime-inference")
            .map(ToString::to_string)
            .as_deref(),
        Some("Prime Inference model catalog request failed: 401")
    );
    assert!(store
        .read("prime-inference", ModelsStoreOperationOptions::default())
        .await
        .expect("read")
        .is_none());
    assert_eq!(models.get_models(Some("prime-inference")).len(), 110);
}

#[tokio::test]
async fn resolves_the_team_header_from_the_stored_credential_env() {
    let credentials = Arc::new(InMemoryCredentialStore::new());
    common::store(
        credentials.as_ref(),
        "prime-inference",
        eukhe_pi_ai::auth::Credential::ApiKey(eukhe_pi_ai::auth::ApiKeyCredential {
            key: Some("pk".into()),
            env: Some(
                [("PRIME_TEAM_ID".to_owned(), "team-1".to_owned())]
                    .into_iter()
                    .collect(),
            ),
            ..eukhe_pi_ai::auth::ApiKeyCredential::default()
        }),
    )
    .await;
    let models = create_models(CreateModelsOptions {
        credentials: Some(credentials),
        ..CreateModelsOptions::default()
    });
    models.set_provider(prime_inference_provider_with_base_url("http://127.0.0.1:9"));
    let auth = models
        .get_auth("prime-inference", AuthResolutionOverrides::default())
        .await
        .expect("auth")
        .expect("configured");
    assert_eq!(auth.auth.api_key.as_deref(), Some("pk"));
    assert_eq!(
        auth.auth
            .headers
            .and_then(|headers| headers.get("X-Prime-Team-ID").cloned().flatten())
            .as_deref(),
        Some("team-1")
    );
    assert_eq!(auth.source.as_deref(), Some("stored credential"));
}
