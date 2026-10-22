use super::*;

fn model(id: &str, provider: &str, context_window: u64) -> Model {
    serde_json::from_value(serde_json::json!({
        "id": id, "name": id, "api": "openai-completions", "provider": provider,
        "baseUrl": "http://localhost", "reasoning": false, "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": context_window, "maxTokens": 100
    }))
    .unwrap()
}

/// The custom provider the auxiliary model lives under (an `apiKey` on
/// the provider config is configured auth for the registry).
const MODELS_JSON: &str = r#"{
  "providers": {
    "testaux": {
      "baseUrl": "http://localhost:9",
      "apiKey": "aux-key",
      "api": "openai-completions",
      "models": [ { "id": "aux-model", "name": "Aux Model", "contextWindow": 128000 } ]
    }
  }
}"#;

/// One resolver setup: the tempdir must outlive the resolve call (the
/// registry reads models.json on demand), the session's model collection
/// built from the same agent dir, and the session's notices.
struct Setup {
    _dir: tempfile::TempDir,
    context: AuxiliaryModelContext,
    models: Models,
    notices: AuxiliaryNotices,
}

impl Setup {
    fn new(settings: &serde_json::Value) -> Self {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(
            dir.path().join("settings.json"),
            serde_json::to_string_pretty(&settings).unwrap(),
        )
        .unwrap();
        std::fs::write(dir.path().join("models.json"), MODELS_JSON).unwrap();
        let models = crate::durable::create_models(dir.path()).models;
        let context = AuxiliaryModelContext {
            cwd: dir.path().to_path_buf(),
            agent_dir: dir.path().to_path_buf(),
        };
        Self {
            _dir: dir,
            context,
            models,
            notices: AuxiliaryNotices::default(),
        }
    }

    fn resolve(&self, required_context_tokens: Option<u64>) -> AuxiliaryResolution {
        resolve_auxiliary_model(
            &self.context,
            &self.models,
            &self.notices,
            "compaction summary",
            &model("session-model", "faux", 8_000),
            required_context_tokens,
        )
    }
}

/// The model id, key and notice of a resolution.
fn summary(resolution: &AuxiliaryResolution) -> (&str, Option<&str>, Option<&str>) {
    (
        resolution.model.id.as_str(),
        resolution.api_key.as_deref(),
        resolution.notice.as_deref(),
    )
}

/// The session fallback resolves its MERGED headers through the same
/// registry the session's own requests use (Cursor PR #2755: with the
/// provider-side team-header fallback deleted, the fallback summarizer
/// call is the only other path that must carry the stored team).
#[test]
fn the_session_fallback_keeps_the_merged_headers() {
    let setup = Setup::new(&serde_json::json!({}));
    std::fs::write(
        setup.context.agent_dir.join("auth.json"),
        serde_json::json!({
            "prime-inference": {
                "type": "api_key",
                "key": "test-key",
                "primeTeam": { "teamId": "team-1", "name": "Test Team" }
            }
        })
        .to_string(),
    )
    .unwrap();
    let routed = resolve_auxiliary_model(
        &setup.context,
        &setup.models,
        &setup.notices,
        "compaction summary",
        &model("session-model", "prime-inference", 8_000),
        None,
    );
    assert_eq!(summary(&routed), ("session-model", None, None));
    let headers = routed.headers.expect("the fallback keeps merged headers");
    assert_eq!(
        headers.get("X-Prime-Team-ID").map(String::as_str),
        Some("team-1"),
        "the stored team ships on the fallback summarizer call"
    );
}

#[test]
fn unset_or_equal_selectors_keep_the_session_model_without_a_notice() {
    for settings in [
        serde_json::json!({}),
        serde_json::json!({ "auxiliaryModel": "  " }),
        serde_json::json!({ "auxiliaryModel": "Faux/Session-Model" }),
    ] {
        let setup = Setup::new(&settings);
        assert_eq!(
            summary(&setup.resolve(None)),
            ("session-model", None, None),
            "{settings}"
        );
    }
}

#[test]
fn configured_selector_routes_to_the_auxiliary_model() {
    let setup = Setup::new(&serde_json::json!({ "auxiliaryModel": "testaux/aux-model" }));
    let routed = setup.resolve(None);
    // The auxiliary call runs on the auxiliary model's own key, never the
    // session's, and there is nothing to tell.
    assert_eq!(summary(&routed), ("aux-model", Some("aux-key"), None));
    assert_eq!(routed.headers, None);
}

/// A selector that cannot be used falls back to the session model and
/// tells why, once per session for each cause (before, a stderr line of
/// the worker was all).
#[test]
fn a_fallback_tells_its_cause_once_per_session() {
    let setup = Setup::new(&serde_json::json!({ "auxiliaryModel": "testaux/missing" }));
    let notice = "The auxiliaryModel setting \"testaux/missing\" was not used for the compaction summary: no model with a configured key has this name. The session model faux/session-model ran it.";
    assert_eq!(
        summary(&setup.resolve(None)),
        ("session-model", None, Some(notice))
    );
    assert_eq!(
        summary(&setup.resolve(None)),
        ("session-model", None, None),
        "the same cause shows once"
    );
}

#[test]
fn too_small_window_falls_back_and_a_fitting_one_routes() {
    let setup = Setup::new(&serde_json::json!({ "auxiliaryModel": "testaux/aux-model" }));
    // The required size exceeds the auxiliary window (128000): the
    // routing falls back instead of failing over-limit on the wire.
    let notice = "The auxiliaryModel setting \"testaux/aux-model\" was not used for the compaction summary: its context window is too small for the request. The session model faux/session-model ran it.";
    assert_eq!(
        summary(&setup.resolve(Some(200_000))),
        ("session-model", None, Some(notice))
    );
    assert_eq!(
        summary(&setup.resolve(Some(1_000))),
        ("aux-model", Some("aux-key"), None)
    );
}

#[test]
fn selector_outside_the_allowlist_falls_back() {
    let setup = Setup::new(&serde_json::json!({
        "auxiliaryModel": "testaux/aux-model",
        "allowedModels": ["faux/session-model"],
    }));
    let notice = "The auxiliaryModel setting \"testaux/aux-model\" was not used for the compaction summary: allowedModels does not include it. The session model faux/session-model ran it.";
    assert_eq!(
        summary(&setup.resolve(None)),
        ("session-model", None, Some(notice))
    );
}

/// The decision runs the checks in their order, and `find` runs only for
/// another model that `allowedModels` admits.
#[test]
fn the_decision_checks_in_order() {
    let other = || AuxiliarySelector::Other("p/m".to_owned());
    let never = |_: &str| -> Result<Found<u8>, FallbackReason> {
        panic!("find runs only for an admitted selector")
    };
    let allow = ["p/m".to_owned()];
    let deny = ["p/other".to_owned()];
    let cases: Vec<(AuxiliaryRoute<u8>, AuxiliaryRoute<u8>)> = vec![
        (
            decide_auxiliary_route(&AuxiliarySelector::Unset, Some(&deny), None, never),
            AuxiliaryRoute::Session,
        ),
        (
            decide_auxiliary_route(&AuxiliarySelector::SessionModel, None, None, never),
            AuxiliaryRoute::Session,
        ),
        (
            decide_auxiliary_route(&other(), Some(&deny), None, never),
            AuxiliaryRoute::Fallback {
                selector: "p/m".to_owned(),
                reason: FallbackReason::NotAllowed,
            },
        ),
        (
            decide_auxiliary_route(&other(), Some(&allow), Some(9), |_| {
                Err(FallbackReason::NoKey)
            }),
            AuxiliaryRoute::Fallback {
                selector: "p/m".to_owned(),
                reason: FallbackReason::NoKey,
            },
        ),
        (
            decide_auxiliary_route(&other(), None, Some(9), |_| {
                Ok(Found {
                    model: 1,
                    context_window: 8,
                })
            }),
            AuxiliaryRoute::Fallback {
                selector: "p/m".to_owned(),
                reason: FallbackReason::WindowTooSmall,
            },
        ),
        (
            decide_auxiliary_route(&other(), None, Some(9), |_| {
                Ok(Found {
                    model: 1,
                    context_window: 0,
                })
            }),
            AuxiliaryRoute::Routed(1),
        ),
        (
            decide_auxiliary_route(&other(), None, None, |_| {
                Ok(Found {
                    model: 1,
                    context_window: 8,
                })
            }),
            AuxiliaryRoute::Routed(1),
        ),
    ];
    let (got, want): (Vec<_>, Vec<_>) = cases.into_iter().unzip();
    assert_eq!(got, want);
}

mod bridge;
