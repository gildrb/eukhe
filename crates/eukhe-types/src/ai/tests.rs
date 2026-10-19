//! The ai wire-type unit battery: the round trips and the serde shapes.
use super::*;

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
fn thinking_level_parse_reads_the_wire_vocabulary() {
    let parsed: Vec<Option<ModelThinkingLevel>> = [
        "off", "minimal", "low", "medium", "high", "xhigh", "max", "nope", "High",
    ]
    .into_iter()
    .map(ModelThinkingLevel::parse)
    .collect();
    assert_eq!(
        parsed,
        vec![
            Some(ModelThinkingLevel::Off),
            Some(ModelThinkingLevel::Minimal),
            Some(ModelThinkingLevel::Low),
            Some(ModelThinkingLevel::Medium),
            Some(ModelThinkingLevel::High),
            Some(ModelThinkingLevel::Xhigh),
            Some(ModelThinkingLevel::Max),
            None,
            None,
        ]
    );
    for level in parsed.into_iter().flatten() {
        assert_eq!(ModelThinkingLevel::parse(level.wire_name()), Some(level));
    }
}

#[test]
fn catalog_model_carries_the_served_lists_beside_the_model_keys() {
    let json = r#"{"id":"m","name":"M","api":"openai-responses","provider":"openai","baseUrl":"https://api.openai.com/v1","reasoning":true,"thinkingLevelMap":{"xhigh":"xhigh"},"input":["text"],"cost":{"input":1.5,"output":2,"cacheRead":0,"cacheWrite":0},"contextWindow":128000,"maxTokens":8192,"thinkingLevels":["minimal","high","xhigh"],"serviceTiers":["default","priority"]}"#;
    assert_roundtrip::<CatalogModel>(json);
    let entry: CatalogModel = serde_json::from_str(json).unwrap();
    assert_eq!(
        (
            entry.model.id.as_str(),
            entry.thinking_levels,
            entry.service_tiers
        ),
        (
            "m",
            vec![
                ModelThinkingLevel::Minimal,
                ModelThinkingLevel::High,
                ModelThinkingLevel::Xhigh,
            ],
            vec![ServiceTier::Default, ServiceTier::Priority],
        )
    );
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
