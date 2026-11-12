use std::borrow::Cow;

use serde_json::json;

use super::{AssistantTurn, MessageParts, Part, TokenBudgetCheck, Tokenizer};
use crate::{Encoding, ModelRef};

const HAIKU: ModelRef<'static> = ModelRef {
    id: "claude-haiku-5-5",
    provider: "anthropic",
    api: "anthropic-messages",
};

const GPT: ModelRef<'static> = ModelRef {
    id: "gpt-5.5",
    provider: "openai",
    api: "openai-responses",
};

fn turn<'a>(model: ModelRef<'a>, output: u64, parts: Vec<Part<'a>>) -> AssistantTurn<'a> {
    AssistantTurn {
        api: model.api,
        provider: model.provider,
        model: model.id,
        dropped: false,
        output,
        reasoning: None,
        parts,
    }
}

/// The reader's catalog tokenizer counts; a model the catalog names no
/// tokenizer for counts in `o200k_base`.
#[test]
fn counts_in_the_readers_tokenizer() {
    let text = "Tokenizers disagree: 東京タワー and naïve café.";
    assert_eq!(
        [
            Tokenizer::for_model(HAIKU).encoding(),
            Tokenizer::for_model(GPT).encoding(),
            Tokenizer::for_model(ModelRef {
                id: "some-local-model",
                provider: "llama-cpp",
                api: "openai-completions",
            })
            .encoding(),
        ],
        [
            Encoding::ClaudeV5Sonnet,
            Encoding::O200kBase,
            Encoding::O200kBase
        ]
    );
    let haiku = Tokenizer::for_model(HAIKU);
    assert_eq!(
        haiku.count_text(text),
        u64::from(Encoding::ClaudeV5Sonnet.count(text))
    );
    // Cached and uncached counts agree.
    assert_eq!(haiku.count_text(text), haiku.count_text(text));
}

/// A batch is the sum of its fragments' counts, below and above the
/// parallel threshold.
#[test]
fn fragments_sum_independent_counts() {
    let tokenizer = Tokenizer::for_model(GPT);
    for len in [3, 40] {
        let fragments: Vec<String> = (0..len)
            .map(|index| format!("fragment {index} ✓"))
            .collect();
        let expected: u64 = fragments
            .iter()
            .map(|fragment| u64::from(Encoding::O200kBase.count(fragment)))
            .sum();
        assert_eq!(tokenizer.count_fragments(&fragments), expected);
    }
}

/// Bytes bound tokens from above: text whose bytes fit is answered without
/// tokenizing; only text past the bound gets the exact count.
#[test]
fn budget_checks_bytes_first() {
    let tokenizer = Tokenizer::for_model(GPT);
    assert_eq!(
        tokenizer.check_token_budget(&["hello world"], 11),
        TokenBudgetCheck {
            fits: true,
            tokens: 11,
            exact: false
        }
    );
    let long = "word ".repeat(100);
    let exact = u64::from(Encoding::O200kBase.count(&long));
    assert_eq!(
        tokenizer.check_token_budget(&[long.as_str()], exact),
        TokenBudgetCheck {
            fits: true,
            tokens: exact,
            exact: true
        }
    );
    assert!(
        !tokenizer
            .check_token_budget(&[long.as_str()], exact - 1)
            .fits
    );
}

/// The M5 repro's text: CJK characters cost Claude about two tokens each
/// (1.2M of them: the provider counted 2,526,991 with the system prompt),
/// not the 2/7 of a token that 3.5 characters per token made of them.
#[test]
fn cjk_counts_at_the_providers_scale() {
    let chars = 120_000u32;
    let text: String = (0..chars)
        .map(|index| char::from_u32(0x4E00 + index % 0x5200 * 7919 % 0x5200).unwrap_or('字'))
        .collect();
    let tokens =
        Tokenizer::for_model(HAIKU).count_message(&MessageParts::Plain(vec![Part::Text(&text)]));
    assert!(
        (u64::from(chars) * 2..u64::from(chars) * 22 / 10).contains(&tokens),
        "{chars} CJK characters counted {tokens} Claude tokens"
    );
}

/// The reader's own signed thinking bills at the turn's output (Claude);
/// another model's thinking replays as plain text and its redacted
/// thinking is dropped; an aborted turn is not replayed.
#[test]
fn thinking_replays_as_the_reader_bills_it() {
    let haiku = Tokenizer::for_model(HAIKU);
    let thinking = Part::Thinking {
        text: "Let me think about it.",
        signature: Some("EsYBCkYIBhgCKkCsignature"),
        redacted: false,
    };
    let answer = Part::Text("The answer.");
    let visible = haiku.count_text("Let me think about it.") + haiku.count_text("The answer.");
    let own = turn(HAIKU, 500, vec![thinking.clone(), answer.clone()]);
    assert_eq!(haiku.count_message(&MessageParts::Assistant(own)), 500);
    let small = turn(HAIKU, 1, vec![thinking.clone(), answer.clone()]);
    assert_eq!(
        haiku.count_message(&MessageParts::Assistant(small)),
        visible
    );
    let foreign = turn(
        GPT,
        500,
        vec![
            thinking,
            Part::Thinking {
                text: "[Reasoning redacted]",
                signature: Some("opaque"),
                redacted: true,
            },
            answer.clone(),
        ],
    );
    assert_eq!(
        haiku.count_message(&MessageParts::Assistant(foreign)),
        visible
    );
    let mut aborted = turn(HAIKU, 500, vec![answer]);
    aborted.dropped = true;
    assert_eq!(haiku.count_message(&MessageParts::Assistant(aborted)), 0);
}

/// A signature-priced reader pays its own signatures' tokens, and a
/// replayed Responses reasoning item at the turn's reasoning tokens.
#[test]
fn signatures_bill_their_tokens_or_the_reasoning_item() {
    let gpt = Tokenizer::for_model(GPT);
    let item =
        json!({ "type": "reasoning", "id": "rs_1", "encrypted_content": "gAAAAB".repeat(200) })
            .to_string();
    let parts = |signature| {
        vec![
            Part::Thinking {
                text: "",
                signature: Some(signature),
                redacted: false,
            },
            Part::Text("done"),
        ]
    };
    let mut replayed = turn(GPT, 900, parts(item.as_str()));
    replayed.reasoning = Some(321);
    assert_eq!(
        gpt.count_message(&MessageParts::Assistant(replayed)),
        321 + gpt.count_text("done")
    );
    let signed = turn(GPT, 900, parts("opaque-signature"));
    assert_eq!(
        gpt.count_message(&MessageParts::Assistant(signed)),
        gpt.count_text("opaque-signature") + gpt.count_text("done")
    );
}

/// Tool calls count their name and JSON arguments; wire rows and typed
/// messages count alike.
#[test]
fn wire_rows_count_like_typed_messages() {
    let gpt = Tokenizer::for_model(GPT);
    let row = json!({
        "role": "assistant",
        "api": "openai-responses",
        "provider": "openai",
        "model": "gpt-5.5",
        "stopReason": "toolUse",
        "usage": { "output": 12 },
        "content": [
            { "type": "text", "text": "Reading it." },
            { "type": "toolCall", "id": "c1", "name": "read", "arguments": { "path": "src/lib.rs" } }
        ]
    });
    let expected = turn(
        GPT,
        12,
        vec![
            Part::Text("Reading it."),
            Part::ToolCall {
                name: "read",
                arguments: Cow::Borrowed(r#"{"path":"src/lib.rs"}"#),
            },
        ],
    );
    assert_eq!(
        MessageParts::from_wire(&row),
        MessageParts::Assistant(expected)
    );
    let user = json!({ "role": "user", "content": [{ "type": "text", "text": "hi" }, { "text": "untagged" }] });
    assert_eq!(
        gpt.count_message(&MessageParts::from_wire(&user)),
        gpt.count_text("hi") + gpt.count_text("untagged")
    );
}
