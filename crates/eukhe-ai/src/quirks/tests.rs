use serde_json::json;

use super::{
    compile, Answer, Directive, FamilyOverlap, Layer, Lookup, Query, Quirks, QuirksError, RawRule,
    RevisionRangeError, Rulebook, Value, ValueKind,
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
            { "id": "opus", "on": "names", "match": [{ "contains": ["opus-4-6"] }] },
            { "id": "claude", "on": "id", "match": [{ "is": ["claude-opus-4-6"] }] }
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

/// The compiled core's verdicts come back as the errors of their rules:
/// an unknown directive, and a clash that names the rule and the first
/// later rule of its layer, target and directive with another value (a
/// value parsed here: `20` and `20` are one value).
#[test]
fn the_core_names_an_unknown_directive_and_a_clash() {
    let errors = compile(&[
        rule(Layer::Model, "m", "strict_cap", json!(20)),
        rule(Layer::Host, "a", "stor", json!(false)),
        rule(Layer::Model, "m", "strict_cap", json!(20)),
        rule(Layer::Model, "m", "strict_cap", json!(8)),
    ])
    .unwrap_err();
    let clash = QuirksError::Clash {
        layer: Layer::Model,
        target: "m".to_owned(),
        directive: "strict_cap".to_owned(),
        first: json!(20),
        second: json!(8),
    };
    assert_eq!(
        errors,
        vec![
            clash.clone(),
            QuirksError::UnknownDirective {
                layer: Layer::Host,
                target: "a".to_owned(),
                directive: "stor".to_owned(),
            },
            clash,
        ]
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
            { "id": "b-family", "on": "id", "match": [{ "starts": ["gemini-2"] }] },
            { "id": "a-family", "on": "id", "match": [{ "starts": ["gemini-3"] }] },
            { "id": "c-family", "on": "names", "match": [{ "contains": ["opus-4-6"] }] }
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

/// `stops_output_at_window` holds for Claude 4.5 and later on the Claude
/// API only: not for older Claude there, not for the same model on
/// Bedrock, and not on a gateway that shares the Claude API's model ids.
#[test]
fn claude_4_5_and_later_stop_at_the_window_on_the_claude_api_only() {
    let stops = |api: &str, provider: &str, id: &str, url: &str| {
        Quirks::of(&model(api, provider, id, url)).stops_output_at_window()
    };
    assert_eq!(
        [
            stops(
                "anthropic-messages",
                "anthropic",
                "claude-sonnet-4-5",
                "https://api.anthropic.com"
            ),
            stops(
                "anthropic-messages",
                "anthropic",
                "claude-opus-4-1",
                "https://api.anthropic.com"
            ),
            stops(
                "bedrock-converse-stream",
                "amazon-bedrock",
                "global.anthropic.claude-sonnet-4-5-20250929-v1:0",
                "",
            ),
            stops(
                "anthropic-messages",
                "opencode",
                "claude-sonnet-4-5",
                "https://opencode.ai/zen"
            ),
        ],
        [Some(true), None, None, Some(false)]
    );
}

/// The shipped Qwen families split at the revision 3.8 (omp's class
/// `qwen`, `revision ">=3.8"`): the revision follows `qwen` in the bare
/// name; a size (`8b`) is not a revision, and an id with no revision is
/// below 3.8.
#[test]
fn the_shipped_qwen_families_split_at_the_revision_3_8() {
    let book = Rulebook::shipped();
    let ids = [
        "qwen3.8-27b",
        "Qwen/Qwen3.8-2.4T-A95B",
        "workers-ai/@cf/qwen/qwen3.8-27b",
        "qwen3-8b",
        "qwen3.5-122b-a10b",
        "qwq-32b",
        "qwen-max",
        "gpt-5.5",
    ];
    assert_eq!(
        ids.map(|id| book.family(id, "")),
        [
            Ok(Some("qwen-3.8")),
            Ok(Some("qwen-3.8")),
            Ok(Some("qwen-3.8")),
            Ok(Some("qwen")),
            Ok(Some("qwen")),
            Ok(Some("qwen")),
            Ok(Some("qwen")),
            Ok(Some("gpt-priority")),
        ]
    );
}

#[test]
fn a_bad_revision_range_an_undefined_tier_family_and_a_bad_ladder_do_not_compile() {
    let errors = Rulebook::from_json(
        r#"{
          "families": [
            { "id": "a", "on": "id", "match": [{ "starts": ["a"] }], "revision": { "prefix": "a", "range": "3.8" } }
          ],
          "hosts": [],
          "rules": [
            { "layer": "model", "target": "m", "set": { "thinking_ladder": { "turbo": "x" } } }
          ],
          "service_tiers": [
            { "provider": "p", "api": "q", "family": "b", "tiers": ["flex"] }
          ]
        }"#,
    )
    .unwrap_err();
    assert_eq!(
        errors,
        vec![
            QuirksError::BadRevision {
                family: "a".to_owned(),
                source: RevisionRangeError::NoComparison {
                    term: "3.8".to_owned(),
                },
            },
            QuirksError::BadValue {
                layer: Layer::Model,
                target: "m".to_owned(),
                directive: "thinking_ladder".to_owned(),
                value: json!({ "turbo": "x" }),
                kind: ValueKind::ThinkingLadder,
            },
            QuirksError::UndefinedTierFamily {
                family: "b".to_owned(),
            },
        ]
    );
}

/// The provider-id checks the host rules replaced, kept here only as their
/// oracle: every model of the compiled catalog gets the old answer (the
/// compound tool-call ids over the three Responses APIs, the lists of
/// which depended on the API).
#[test]
fn the_shipped_host_rules_give_the_former_provider_checks() {
    let flag = eukhe_bend::rules::model_facts::flag;
    let differences: Vec<(String, String, &str)> = crate::models_generated::MODELS
        .values()
        .flat_map(|models| models.values())
        .flat_map(|model| {
            let quirks = Quirks::of(model);
            let provider = model.provider.as_str();
            let compound = match model.api.as_str() {
                "openai-responses" | "openai-codex-responses" => {
                    Some(matches!(provider, "openai" | "openai-codex" | "opencode"))
                }
                "azure-openai-responses" => Some(matches!(
                    provider,
                    "openai" | "openai-codex" | "opencode" | "azure"
                )),
                _ => None,
            };
            [
                (
                    "compound_tool_call_ids",
                    compound.is_none_or(|old| old == flag(quirks.compound_tool_call_ids(), false)),
                ),
                (
                    "tool_call_id_limit",
                    (provider == "openai").then_some(40) == quirks.tool_call_id_limit(),
                ),
                (
                    "service_tier_field",
                    (provider != "github-copilot") == flag(quirks.service_tier_field(), true),
                ),
                (
                    "reasoning_off_field",
                    (provider != "github-copilot") == flag(quirks.reasoning_off_field(), true),
                ),
                (
                    "encrypted_reasoning",
                    (provider == "xai") == flag(quirks.encrypted_reasoning(), false),
                ),
                (
                    "reasoning_content_signature",
                    (provider == "opencode-go")
                        == flag(quirks.reasoning_content_signature(), false),
                ),
            ]
            .into_iter()
            .filter(|(_, same)| !same)
            .map(|(directive, _)| (model.provider.clone(), model.id.clone(), directive))
        })
        .collect();
    assert_eq!(differences, Vec::new());
}

/// A family takes what the families it is outside leave: a model one of
/// them matches is theirs alone; an `outside` naming no family, or a
/// family that is itself outside others, does not compile.
#[test]
fn a_family_outside_others_takes_only_what_they_leave() {
    let book = Rulebook::from_json(
        r#"{
          "families": [
            { "id": "gpt", "on": "names", "match": [{ "contains": ["gpt-"] }], "outside": ["gpt-5", "gpt-oss"] },
            { "id": "gpt-5", "on": "id", "match": [{ "starts": ["gpt-5"] }] },
            { "id": "gpt-oss", "on": "names", "match": [{ "contains": ["gpt-oss"] }] }
          ],
          "hosts": [],
          "rules": []
        }"#,
    )
    .unwrap();
    assert_eq!(
        [
            "openai.gpt-5.4",
            "gpt-5.4",
            "openai.gpt-oss-20b",
            "gpt-4o",
            "o3"
        ]
        .map(|id| book.family(id, "").unwrap()),
        [
            Some("gpt"),
            Some("gpt-5"),
            Some("gpt-oss"),
            Some("gpt"),
            None
        ]
    );
    let errors = Rulebook::from_json(
        r#"{
          "families": [
            { "id": "a", "on": "id", "match": [{ "starts": ["a"] }], "outside": ["b", "z"] },
            { "id": "b", "on": "id", "match": [{ "starts": ["b"] }], "outside": ["c"] },
            { "id": "c", "on": "id", "match": [{ "starts": ["c"] }] }
          ],
          "hosts": [],
          "rules": []
        }"#,
    )
    .unwrap_err();
    assert_eq!(
        errors,
        vec![
            QuirksError::NestedOutside {
                family: "a".to_owned(),
                outside: "b".to_owned(),
            },
            QuirksError::UndefinedOutside {
                family: "a".to_owned(),
                outside: "z".to_owned(),
            },
        ]
    );
}
