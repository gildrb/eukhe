use serde_json::json;

use super::{
    compile, Answer, Directive, FamilyOverlap, Layer, Lookup, Query, Quirks, QuirksError, RawRule,
    Rulebook, Value, ValueKind,
};
use crate::capabilities::{Capability, Dialect};
use crate::types::{MaxTokensField, Model, SessionAffinityFormat, ThinkingFormat};

fn model(api: &str, provider: &str, id: &str, base_url: &str) -> Model {
    serde_json::from_value(json!({
        "id": id,
        "name": "",
        "api": api,
        "provider": provider,
        "baseUrl": base_url,
        "reasoning": true,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 128_000,
        "maxTokens": 16384,
    }))
    .unwrap()
}

fn rule(layer: Layer, target: &str, directive: &str, value: serde_json::Value) -> RawRule {
    RawRule {
        layer,
        target: target.to_owned(),
        directive: directive.to_owned(),
        value,
    }
}

const QUERY: Query<'static> = Query {
    family: Some("fam"),
    model: "mod",
    host: Some("host"),
};

#[test]
fn the_shipped_rulebook_compiles() {
    let catalog = crate::models_generated::MODELS
        .values()
        .flat_map(|models| models.values());
    let shipped = Rulebook::from_json(include_str!("rulebook.json"))
        .and_then(|book| book.check_catalog(catalog));
    assert_eq!(shipped, Ok(()));
}

/// Two families that both match a model of the compiled catalog do not
/// pass the catalog check: no family wins by its id.
#[test]
fn families_that_overlap_on_a_catalog_model_are_rejected() {
    let book = Rulebook::from_json(
        r#"{
          "families": [
            { "id": "opus", "on": "names", "match": "opus-4-6" },
            { "id": "claude", "on": "id", "match": "^claude-opus-4-6$" }
          ],
          "hosts": [],
          "rules": []
        }"#,
    )
    .unwrap();
    let catalog = crate::models_generated::MODELS
        .values()
        .flat_map(|models| models.values())
        .filter(|model| model.provider == "anthropic");
    assert_eq!(
        book.check_catalog(catalog),
        Err(vec![QuirksError::FamilyOverlap(FamilyOverlap {
            model: "claude-opus-4-6".to_owned(),
            first: "claude".to_owned(),
            second: "opus".to_owned(),
        })])
    );
}

/// A model outside the catalog that two shipped families match names no
/// family, so neither family's directives apply.
#[test]
fn a_model_two_shipped_families_match_names_no_family() {
    let both = model(
        "openai-completions",
        "local",
        "qwen3-opus-5",
        "http://localhost:8000/v1",
    );
    assert_eq!(
        Rulebook::shipped().query(&both, Lookup::Wire),
        Err(FamilyOverlap {
            model: "qwen3-opus-5".to_owned(),
            first: "claude-adaptive".to_owned(),
            second: "qwen".to_owned(),
        })
    );
    let quirks = Quirks::of(&both);
    assert_eq!(
        (
            quirks.query(),
            quirks.qwen_chat_template(),
            quirks.adaptive_thinking()
        ),
        (
            Query {
                family: None,
                model: "qwen3-opus-5",
                host: Some("loopback"),
            },
            None,
            None
        )
    );
}

#[test]
fn an_unknown_directive_does_not_compile() {
    let errors = compile(&[
        rule(Layer::Host, "a", "store", json!(false)),
        rule(Layer::Host, "a", "stor", json!(false)),
    ])
    .unwrap_err();
    assert_eq!(
        errors,
        vec![QuirksError::UnknownDirective {
            layer: Layer::Host,
            target: "a".to_owned(),
            directive: "stor".to_owned(),
        }]
    );
}

#[test]
fn a_value_of_the_wrong_type_does_not_compile() {
    let errors =
        compile(&[rule(Layer::Family, "f", "thinking_format", json!("nope"))]).unwrap_err();
    assert_eq!(
        errors,
        vec![QuirksError::BadValue {
            layer: Layer::Family,
            target: "f".to_owned(),
            directive: "thinking_format".to_owned(),
            value: json!("nope"),
            kind: ValueKind::ThinkingFormat,
        }]
    );
}

#[test]
fn a_capability_takes_only_a_dialect_that_implements_it_or_false() {
    let errors = compile(&[
        rule(Layer::Host, "h", "usage", json!("anthropic")),
        rule(Layer::Host, "h", "embed", json!(true)),
        rule(Layer::Host, "h", "tokenize", json!("xai")),
        rule(Layer::Model, "m", "tokenize", json!(false)),
    ])
    .unwrap_err();
    assert_eq!(
        errors,
        vec![
            QuirksError::BadValue {
                layer: Layer::Host,
                target: "h".to_owned(),
                directive: "usage".to_owned(),
                value: json!("anthropic"),
                kind: ValueKind::Endpoint(Capability::Usage),
            },
            QuirksError::BadValue {
                layer: Layer::Host,
                target: "h".to_owned(),
                directive: "embed".to_owned(),
                value: json!(true),
                kind: ValueKind::Endpoint(Capability::Embed),
            },
        ]
    );
    let rules = compile(&[
        rule(Layer::Host, "host", "tokenize", json!("xai")),
        rule(Layer::Model, "mod", "tokenize", json!(false)),
    ])
    .unwrap();
    let host_only = Query {
        family: None,
        model: "other",
        host: Some("host"),
    };
    assert_eq!(
        (
            rules.lookup(&host_only, Directive::Endpoint(Capability::Tokenize)),
            rules.lookup(&QUERY, Directive::Endpoint(Capability::Tokenize)),
            rules.lookup(&QUERY, Directive::Endpoint(Capability::Usage)),
        ),
        (
            Answer::Known(&Value::Endpoint(Some(Dialect::Xai))),
            Answer::Known(&Value::Endpoint(Some(Dialect::Xai))),
            Answer::Unknown,
        )
    );
    let model_only = Query {
        family: None,
        model: "mod",
        host: None,
    };
    assert_eq!(
        rules.lookup(&model_only, Directive::Endpoint(Capability::Tokenize)),
        Answer::Known(&Value::Endpoint(None))
    );
}

#[test]
fn two_rules_of_one_layer_and_target_with_different_values_do_not_compile() {
    let errors = compile(&[
        rule(Layer::Model, "m", "strict_cap", json!(20)),
        rule(Layer::Model, "m", "strict_cap", json!(20)),
        rule(Layer::Model, "m", "strict_cap", json!(8)),
    ])
    .unwrap_err();
    assert_eq!(
        errors,
        vec![QuirksError::Clash {
            layer: Layer::Model,
            target: "m".to_owned(),
            directive: "strict_cap".to_owned(),
            first: json!(20),
            second: json!(8),
        }]
    );
    // Other layers or targets with other values are no clash.
    assert!(compile(&[
        rule(Layer::Model, "m", "strict_cap", json!(20)),
        rule(Layer::Host, "m", "strict_cap", json!(8)),
        rule(Layer::Model, "n", "strict_cap", json!(8)),
    ])
    .is_ok());
}

#[test]
fn the_highest_layer_that_applies_answers_and_none_is_unknown() {
    let rules = [
        rule(Layer::Family, "fam", "store", json!(false)),
        rule(Layer::Model, "mod", "store", json!(true)),
        rule(Layer::Family, "fam", "strict_tools", json!(true)),
        rule(Layer::Host, "host", "strict_tools", json!(false)),
        rule(Layer::Host, "other", "reasoning_effort", json!(false)),
    ];
    let compiled = compile(&rules).unwrap();
    let answers: Vec<Answer<'_>> = [
        Directive::Store,
        Directive::StrictTools,
        Directive::ReasoningEffort,
    ]
    .into_iter()
    .map(|directive| compiled.lookup(&QUERY, directive))
    .collect();
    assert_eq!(
        answers,
        vec![
            Answer::Known(&Value::Bool(true)),
            Answer::Known(&Value::Bool(false)),
            Answer::Unknown,
        ]
    );
}

#[test]
fn the_order_of_the_rules_changes_no_answer() {
    let rules = vec![
        rule(
            Layer::Family,
            "fam",
            "max_tokens_field",
            json!("max_tokens"),
        ),
        rule(
            Layer::Model,
            "mod",
            "max_tokens_field",
            json!("max_completion_tokens"),
        ),
        rule(
            Layer::Model,
            "mod",
            "max_tokens_field",
            json!("max_completion_tokens"),
        ),
        rule(Layer::Host, "host", "thinking_format", json!("zai")),
        rule(Layer::Family, "fam", "thinking_format", json!("qwen")),
    ];
    let forward = compile(&rules).unwrap();
    let mut reversed_rules = rules;
    reversed_rules.reverse();
    let reversed = compile(&reversed_rules).unwrap();
    for directive in Directive::ALL {
        assert_eq!(
            forward.lookup(&QUERY, *directive),
            reversed.lookup(&QUERY, *directive),
            "{directive:?}"
        );
    }
}

#[test]
fn a_rulebook_with_an_unknown_field_or_target_fails_loudly() {
    let unknown_field = Rulebook::from_json(
        r#"{ "families": [], "hosts": [{ "id": "h", "url": ["x"] }], "rules": [] }"#,
    )
    .unwrap_err();
    assert!(
        matches!(unknown_field.as_slice(), [QuirksError::Format(message)] if message.contains("unknown field `url`")),
        "{unknown_field:?}"
    );
    let undefined = Rulebook::from_json(
        r#"{ "families": [], "hosts": [], "rules": [{ "layer": "host", "target": "h", "set": { "store": false } }] }"#,
    )
    .unwrap_err();
    assert_eq!(
        undefined,
        vec![QuirksError::UndefinedTarget {
            layer: Layer::Host,
            target: "h".to_owned(),
        }]
    );
}

#[test]
fn a_query_names_the_host_by_api_then_provider_then_longest_url() {
    let book = Rulebook::from_json(
        r#"{
          "families": [
            { "id": "b-family", "on": "id", "match": "^gemini-2" },
            { "id": "a-family", "on": "id", "match": "^gemini-3" },
            { "id": "c-family", "on": "names", "match": "opus-4-6" }
          ],
          "hosts": [
            { "id": "by-api", "apis": ["only-api"] },
            { "id": "by-provider", "providers": ["prov"] },
            { "id": "short", "urls": ["example.com"] },
            { "id": "long", "urls": ["api.example.com"] }
          ],
          "rules": []
        }"#,
    )
    .unwrap();
    let cases = [
        model(
            "only-api",
            "prov",
            "gemini-3-pro",
            "https://api.example.com",
        ),
        model("chat", "prov", "gemini-2", "https://api.example.com"),
        model("chat", "other", "x", "https://API.example.com/v1"),
        model(
            "chat",
            "other",
            "us.anthropic.claude-opus-4-6-v1:0",
            "https://www.example.com",
        ),
        model("chat", "other", "x", "https://elsewhere.test"),
    ];
    let queries: Vec<Result<Query<'_>, FamilyOverlap>> = cases
        .iter()
        .map(|model| book.query(model, Lookup::Wire))
        .collect();
    assert_eq!(
        queries,
        [
            Ok(Query {
                family: Some("a-family"),
                model: "gemini-3-pro",
                host: Some("by-api"),
            }),
            Ok(Query {
                family: Some("b-family"),
                model: "gemini-2",
                host: Some("by-provider"),
            }),
            Ok(Query {
                family: None,
                model: "x",
                host: Some("long"),
            }),
            Ok(Query {
                family: Some("c-family"),
                model: "us.anthropic.claude-opus-4-6-v1:0",
                host: Some("short"),
            }),
            Ok(Query {
                family: None,
                model: "x",
                host: None,
            }),
        ]
    );
}

#[test]
fn a_wire_lookup_skips_a_host_of_scope_capabilities() {
    let book = Rulebook::from_json(
        r#"{
          "families": [],
          "hosts": [
            { "id": "caps", "providers": ["prov"], "urls": ["caps.test"], "scope": "capabilities" },
            { "id": "local", "urls": ["//localhost"] }
          ],
          "rules": [
            { "layer": "host", "target": "caps", "set": { "tokenize": "llama-cpp" } },
            { "layer": "host", "target": "local", "set": { "store": false } }
          ]
        }"#,
    )
    .unwrap();
    let at_localhost = model("chat", "prov", "m", "http://localhost:8080/v1");
    let on_lan = model("chat", "prov", "m", "http://192.168.1.20:8080/v1");
    let by_url = model("chat", "other", "m", "https://caps.test/v1");
    let hosts = |model: &Model| {
        [Lookup::Wire, Lookup::Capabilities]
            .map(|lookup| book.query(model, lookup).unwrap().host.map(str::to_owned))
    };
    let caps = Some("caps".to_owned());
    assert_eq!(
        [hosts(&at_localhost), hosts(&on_lan), hosts(&by_url)],
        [
            [Some("local".to_owned()), caps.clone()],
            [None, caps.clone()],
            [None, caps],
        ]
    );
}

#[test]
fn a_host_of_scope_capabilities_sets_only_capability_directives() {
    let errors = Rulebook::from_json(
        r#"{
          "families": [],
          "hosts": [{ "id": "caps", "providers": ["prov"], "scope": "capabilities" }],
          "rules": [
            { "layer": "host", "target": "caps", "set": { "tokenize": "llama-cpp", "store": false } }
          ]
        }"#,
    )
    .unwrap_err();
    assert_eq!(
        errors,
        vec![QuirksError::WireDirectiveOnCapabilityHost {
            host: "caps".to_owned(),
            directive: "store".to_owned(),
        }]
    );
}

#[test]
fn a_host_of_scope_capabilities_may_set_prompt_progress() {
    let book = Rulebook::from_json(
        r#"{
          "families": [],
          "hosts": [{ "id": "caps", "providers": ["prov"], "scope": "capabilities" }],
          "rules": [
            { "layer": "host", "target": "caps", "set": { "tokenize": "llama-cpp", "prompt_progress": true } }
          ]
        }"#,
    )
    .unwrap();
    let lan = model("openai-completions", "prov", "m", "http://10.0.0.2:8080/v1");
    let query = book.query(&lan, Lookup::Capabilities).unwrap();
    assert_eq!(
        book.lookup(&query, Directive::PromptProgress),
        Answer::Known(&Value::Bool(true))
    );
    let errors = Rulebook::from_json(
        r#"{
          "families": [],
          "hosts": [{ "id": "caps", "providers": ["prov"], "scope": "capabilities" }],
          "rules": [
            { "layer": "host", "target": "caps", "set": { "prompt_progress": true, "store": false } }
          ]
        }"#,
    )
    .unwrap_err();
    assert_eq!(
        errors,
        vec![QuirksError::WireDirectiveOnCapabilityHost {
            host: "caps".to_owned(),
            directive: "store".to_owned(),
        }]
    );
}

/// The capability hosts of the shipped rulebook change no wire setting:
/// provider `openai` behind a loopback URL keeps the loopback settings, and
/// a llama.cpp provider on a LAN address gets no host settings, as before
/// the capability rules; both keep their capability endpoints where they
/// had them.
#[test]
fn the_shipped_capability_hosts_keep_the_wire_settings() {
    let openai_local = model(
        "openai-completions",
        "openai",
        "gpt-4o",
        "http://localhost:8080/v1",
    );
    let llama_lan = model(
        "openai-completions",
        "llama-cpp",
        "gemma-3-4b",
        "http://192.168.1.20:8080/v1",
    );
    let llama_local = model(
        "openai-completions",
        "llama.cpp",
        "gemma-3-4b",
        "http://127.0.0.1:8080/v1",
    );
    let wire = |model: &Model| {
        let quirks = Quirks::of(model);
        (
            quirks.query().host.map(str::to_owned),
            quirks.store(),
            quirks.developer_role(),
        )
    };
    let loopback = Some("loopback".to_owned());
    assert_eq!(
        [wire(&openai_local), wire(&llama_lan), wire(&llama_local)],
        [
            (loopback.clone(), Some(false), Some(false)),
            (None, None, None),
            (loopback, Some(false), Some(false)),
        ]
    );
    let tokenize = |model: &Model| {
        Quirks::for_lookup(model, Lookup::Capabilities).endpoint(Capability::Tokenize)
    };
    assert_eq!(
        [
            tokenize(&openai_local),
            tokenize(&llama_lan),
            tokenize(&llama_local)
        ],
        [None, Some(Dialect::LlamaCpp), Some(Dialect::LlamaCpp)]
    );
}

#[test]
fn the_shipped_rules_give_the_former_host_and_family_checks() {
    let zai = model(
        "openai-completions",
        "custom",
        "glm-4.6",
        "https://api.z.ai/api/paas/v4",
    );
    let quirks = Quirks::of(&zai);
    assert_eq!(
        (
            quirks.store(),
            quirks.developer_role(),
            quirks.reasoning_effort(),
            quirks.max_tokens_field(),
            quirks.thinking_format(),
        ),
        (
            Some(false),
            Some(false),
            Some(false),
            Some(MaxTokensField::MaxTokens),
            Some(ThinkingFormat::Zai),
        )
    );
    let openrouter = model(
        "anthropic-messages",
        "openrouter",
        "anthropic/claude-sonnet-4.5",
        "https://openrouter.ai/api",
    );
    let quirks = Quirks::of(&openrouter);
    assert_eq!(
        (
            quirks.session_affinity_headers(),
            quirks.session_affinity_format(),
            quirks.anthropic_cache_control_prefixes(),
        ),
        (
            Some(true),
            Some(SessionAffinityFormat::OpenRouter),
            Some(["anthropic/".to_owned()].as_slice()),
        )
    );
}

#[test]
fn the_shipped_family_and_api_rules_give_the_former_checks() {
    let checks = [
        (
            Directive::QwenChatTemplate,
            model(
                "openai-completions",
                "local",
                "org/Qwen3-32B",
                "http://localhost:8000/v1",
            ),
        ),
        (
            Directive::GoogleValidatedTools,
            model(
                "google-generative-ai",
                "google",
                "gemini-3.1-pro-preview",
                "",
            ),
        ),
        (
            Directive::AdaptiveThinking,
            model(
                "bedrock-converse-stream",
                "amazon-bedrock",
                "global.anthropic.claude-opus-4-6-v1",
                "",
            ),
        ),
        (
            Directive::StrictTools,
            model(
                "azure-openai-responses",
                "my-azure",
                "gpt-5",
                "http://127.0.0.1:1",
            ),
        ),
    ];
    for (directive, model) in checks {
        assert_eq!(
            Rulebook::shipped().lookup(&Quirks::of(&model).query(), directive),
            Answer::Known(&Value::Bool(true)),
            "{directive:?} for {}",
            model.id
        );
    }
    let gemini_2 = model("google-generative-ai", "google", "gemini-2.5-pro", "");
    assert_eq!(Quirks::of(&gemini_2).google_validated_tools(), None);
    let anthropic = model(
        "anthropic-messages",
        "anthropic",
        "claude-opus-4-7",
        "https://api.anthropic.com",
    );
    assert_eq!(
        (
            Quirks::of(&anthropic).strict_cap(),
            Quirks::of(&anthropic).tool_choice_free()
        ),
        (Some(20), Some(false))
    );
}
