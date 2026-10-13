//! The ai wire-type unit battery: the service tier eligibility, the
//! round trips, and the serde shapes.
use super::*;

/// A minimal model for the tier-eligibility predicate (TS #2144's
/// gating tests run the same provider/api combinations), offered at the
/// tiers its row prices, with `compat` as its effective compat (the
/// provider defaults of `providers/data/provider_compat.json`).
fn tier_model(api: &str, compat: Value, offered: &[ServiceTier]) -> Model {
    let price = |tier| offered.contains(&tier).then_some(2.0);
    let service_tier_multipliers =
        (!offered.is_empty()).then(|| crate::pi_ai::ServiceTierMultipliers {
            flex: price(ServiceTier::Flex),
            priority: price(ServiceTier::Priority),
        });
    let Value::Object(raw) = compat else {
        panic!("compat is an object");
    };
    Model {
        id: "model".to_string(),
        name: "model".to_string(),
        api: api.to_string(),
        provider: "provider".to_string(),
        base_url: "https://example.invalid/v1".to_string(),
        reasoning: false,
        thinking_level_map: None,
        input: Vec::new(),
        cost: ModelCost {
            input: JsNumber(0.0),
            output: JsNumber(0.0),
            cache_read: JsNumber(0.0),
            cache_write: JsNumber(0.0),
            service_tier_multipliers,
        },
        context_window: 0,
        max_tokens: 0,
        max_tokens_explicit: false,
        featured: None,
        headers: None,
        compat: (!raw.is_empty()).then_some(ModelCompat { raw }),
    }
}

/// The tiers of `[Auto, Flex, Scale, Priority]` `model` is eligible for.
fn eligible_tiers(model: &Model) -> Vec<ServiceTier> {
    [
        ServiceTier::Auto,
        ServiceTier::Flex,
        ServiceTier::Scale,
        ServiceTier::Priority,
    ]
    .into_iter()
    .filter(|tier| supports_service_tier(model, *tier))
    .collect()
}

#[test]
fn service_tier_eligibility_follows_the_host_compat_facts() {
    use ServiceTier::*;
    let openrouter_completions =
        serde_json::json!({ "supportsServiceTier": true, "serviceTiers": ["flex", "priority"] });
    let openai_responses = serde_json::json!({ "serviceTiers": ["auto", "scale"] });
    let openai_completions = serde_json::json!({ "supportsServiceTier": true });
    let copilot_responses = serde_json::json!({ "supportsServiceTier": false });

    // `default` is always accepted (it means no tier request at all), even
    // where the compat block does not fit the API.
    for (api, compat) in [
        ("anthropic-messages", serde_json::json!({})),
        ("openai-completions", openrouter_completions.clone()),
        ("openai-responses", openai_responses.clone()),
        (
            "openai-completions",
            serde_json::json!({ "serviceTiers": 1 }),
        ),
    ] {
        assert!(supports_service_tier(
            &tier_model(api, compat, &[]),
            Default
        ));
    }
    // A host that offers flex/priority for every model (OpenRouter
    // completions) takes those and nothing else.
    let openrouter = tier_model("openai-completions", openrouter_completions, &[]);
    assert_eq!(eligible_tiers(&openrouter), [Flex, Priority]);
    // A Responses host offering auto/scale everywhere (OpenAI, Codex) takes
    // flex or priority where the row prices the tier.
    let codex = tier_model(
        "openai-codex-responses",
        openai_responses.clone(),
        &[Priority],
    );
    assert_eq!(eligible_tiers(&codex), [Auto, Scale, Priority]);
    let openai = tier_model(
        "openai-responses",
        openai_responses.clone(),
        &[Flex, Priority],
    );
    assert_eq!(eligible_tiers(&openai), [Auto, Flex, Scale, Priority]);
    let codex_unpriced = tier_model("openai-codex-responses", openai_responses, &[]);
    assert_eq!(eligible_tiers(&codex_unpriced), [Auto, Scale]);
    // A completions host that takes the field but offers no tier and an
    // unpriced row (OpenAI completions) stays at `default`.
    let direct = tier_model("openai-completions", openai_completions, &[]);
    assert!(eligible_tiers(&direct).is_empty());
    // A host that does not take the field (Copilot Responses) ignores the
    // row's prices; completions hosts do not take it by default.
    let copilot = tier_model("openai-responses", copilot_responses, &[Flex, Priority]);
    assert!(eligible_tiers(&copilot).is_empty());
    let completions = tier_model("openai-completions", serde_json::json!({}), &[Priority]);
    assert!(eligible_tiers(&completions).is_empty());
    // supportsFastMode is the priority question — and #2144 makes the
    // OpenRouter completions models fast-mode-eligible too (their
    // priority tier is accepted).
    assert!(supports_fast_mode(&codex));
    assert!(supports_fast_mode(&openrouter));
    assert!(!supports_fast_mode(&codex_unpriced));
}

fn rt<T: serde::Serialize + for<'de> Deserialize<'de>>(json: &str) -> String {
    let parsed: T = serde_json::from_str(json).expect("deserialize");
    serde_json::to_string(&parsed).expect("serialize")
}

fn assert_roundtrip<T: serde::Serialize + for<'de> Deserialize<'de>>(json: &str) {
    let original: Value = serde_json::from_str(json).unwrap();
    let out = rt::<T>(json);
    let reparsed: Value = serde_json::from_str(&out).unwrap();
    assert_eq!(original, reparsed, "round trip changed the value: {out}");
}

#[test]
fn user_message_content_string_or_blocks() {
    assert_roundtrip::<UserMessage>(r#"{"content":"hello","timestamp":1}"#);
    assert_roundtrip::<UserMessage>(
        r#"{"content":[{"type":"text","text":"a"},{"type":"image","data":"QQ==","mimeType":"image/png"}],"timestamp":2}"#,
    );
}

#[test]
fn assistant_message_roundtrip_and_unknown_fields() {
    assert_roundtrip::<AssistantMessage>(
        r#"{"content":[{"type":"thinking","thinking":"t","thinkingSignature":"r","redacted":false},{"type":"toolCall","id":"1","name":"bash","arguments":{"code":"ls"},"thoughtSignature":"g"},{"type":"text","text":"done","textSignature":"{\"v\":1,\"id\":\"x\"}"}],"api":"openai-completions","provider":"p","model":"m","responseModel":"m2","responseId":"rid","usage":{"input":1,"output":2,"cacheRead":3,"cacheWrite":4,"totalTokens":10,"cost":{"input":0.5,"output":0.25,"cacheRead":0,"cacheWrite":0,"total":0.75}},"stopReason":"toolUse","stopReasonRaw":"stop_sequence","timestamp":9,"future":"kept"}"#,
    );
}

#[test]
fn tool_result_message_roundtrip() {
    assert_roundtrip::<ToolResultMessage>(
        r#"{"toolCallId":"c1","toolName":"ipython","content":[{"type":"text","text":"out"}],"details":{"durationMs":3},"isError":false,"timestamp":4}"#,
    );
}

#[test]
fn model_with_compat_roundtrip() {
    // Anthropic-flavored compat is recognized by its distinctive key.
    assert_roundtrip::<Model>(
        r#"{"id":"m","name":"M","api":"anthropic-messages","provider":"anthropic","baseUrl":"https://x","reasoning":true,"input":["text","image"],"cost":{"input":3,"output":15,"cacheRead":0.3,"cacheWrite":3.75},"contextWindow":200000,"maxTokens":8192,"thinkingLevelMap":{"minimal":null,"low":"low"},"compat":{"supportsEagerToolInputStreaming":false},"headers":{"x":"y"},"featured":true}"#,
    );
    // OpenAI-completions-flavored compat.
    assert_roundtrip::<Model>(
        r#"{"id":"m2","name":"M2","api":"openai-completions","provider":"p","baseUrl":"https://y","reasoning":false,"input":["text"],"cost":{"input":1,"output":1,"cacheRead":0,"cacheWrite":0},"contextWindow":1000,"maxTokens":100,"compat":{"thinkingFormat":"openrouter","openRouterRouting":{"only":["a"],"sort":{"by":"price","partition":"model"},"max_price":{"prompt":"0.5","completion":2}}}}"#,
    );
}

#[test]
fn user_content_untagged_text_block_roundtrips_losslessly() {
    // Live session files carry user text blocks without a `type` tag
    // (persisted by earlier daemon builds, e.g. session
    // 01a0abe1-ab24-73c0-b363-0cc4e4d6cc5f.jsonl line 4). The block must
    // deserialize and re-serialize verbatim, without injecting a tag.
    assert_roundtrip::<UserMessage>(r#"{"content":[{"text":"hi"}],"timestamp":3}"#);
}

#[test]
fn user_content_unknown_block_kind_is_preserved() {
    // A block kind this version does not model (written by a newer
    // build) must never fail the load; it round-trips verbatim.
    assert_roundtrip::<UserMessage>(
        r#"{"content":[{"type":"video","url":"x","meta":{"a":1}}],"timestamp":4}"#,
    );
}

#[test]
fn bare_block_payload_views() {
    let content: UserContent = serde_json::from_str(
        r#"[{"text":"hi"},{"type":"image","data":"QQ==","mimeType":"image/png"},{"type":"file","id":"f"}]"#,
    )
    .unwrap();
    // Tag-strict display text ignores un-modeled blocks, matching the TS
    // text extraction (`block.type === "text"`).
    assert_eq!(content.text(), "");
    let UserContent::Blocks(blocks) = content else {
        panic!("expected blocks");
    };
    // Provider payload views recover the bare text/image structurally.
    assert_eq!(blocks[0].text(), Some("hi"));
    assert_eq!(blocks[1].image(), Some(("QQ==", "image/png")));
    assert_eq!(blocks[2].text(), None);
    assert_eq!(blocks[2].image(), None);
}

#[test]
fn user_content_text_helper() {
    let content: UserContent = serde_json::from_str(
        r#"[{"type":"text","text":"a b"},{"type":"image","data":"x","mimeType":"i"},{"type":"text","text":"c"}]"#,
    )
    .unwrap();
    assert_eq!(content.text(), "a b c");
}

/// Token sums saturate at `u64::MAX` (JS `Infinity`): an overflowing
/// record must never panic the whole-file readers that fold totals.
#[test]
fn add_usage_saturates_token_totals() {
    let mut total = Usage {
        input: u64::MAX,
        output: 1,
        ..Default::default()
    };
    total.add_usage(&Usage {
        input: 10,
        ..Default::default()
    });
    assert_eq!(total.input, u64::MAX);
    assert_eq!(total.output, 1);
}
