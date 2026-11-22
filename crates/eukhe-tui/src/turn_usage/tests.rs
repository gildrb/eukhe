use super::*;
use serde_json::json;

/// A settled assistant message with this usage, `tools` tool calls, its
/// request start at `timestamp` and its last token `last_token_ms` later.
fn message(
    (input, output, cache_read, cache_write): (u64, u64, u64, u64),
    cost: f64,
    tools: usize,
    timestamp: u64,
    last_token_ms: u64,
) -> AssistantMessage {
    let content: Vec<_> = (0..tools)
        .map(|index| json!({ "type": "toolCall", "id": format!("c{index}"), "name": "read", "arguments": {} }))
        .collect();
    serde_json::from_value(json!({
        "content": content,
        "api": "faux",
        "provider": "faux",
        "model": "faux-1",
        "usage": {
            "input": input, "output": output, "cacheRead": cache_read, "cacheWrite": cache_write,
            "totalTokens": input + output + cache_read + cache_write,
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": cost },
        },
        "stopReason": if tools > 0 { "toolUse" } else { "stop" },
        "timestamp": timestamp,
        "timing": { "firstTokenMs": 1, "lastTokenMs": last_token_ms },
    }))
    .expect("fixture decodes")
}

/// The audit's mock turn: a tool round and the answer.
fn mock_turn() -> TurnUsage {
    let mut usage = TurnUsage::default();
    usage.add_message(&message((1840, 212, 38912, 2048), 0.028, 3, 1_000, 1_500));
    usage.tool_failed();
    usage.add_message(&message((96, 140, 41200, 0), 0.0, 0, 3_000, 2_200));
    usage
}

#[test]
fn the_mock_turn_reads_its_tokens_cache_and_hit_share() {
    let usage = mock_turn();
    assert_eq!(usage.cache_hit_percent(), Some(95));
    assert_eq!(
        usage.row_text(),
        "-- 4.2s - 3 tools, 1 failed - in 1.9k - out 352 - cache r 80.1k w 2.0k (95% hit) - $0.03"
    );
}

#[test]
fn zero_cost_and_an_unused_cache_drop_out() {
    let mut usage = TurnUsage::default();
    usage.add_message(&message((12, 3, 0, 0), 0.0, 0, 0, 0));
    assert_eq!(usage.cache_hit_percent(), None);
    assert_eq!(usage.row_text(), "-- in 12 - out 3");
}

#[test]
fn a_turn_without_tokens_has_no_footer() {
    let mut usage = TurnUsage::default();
    assert!(usage.is_empty());
    usage.add_message(&message((0, 0, 0, 0), 0.0, 1, 5, 9));
    assert!(usage.is_empty());
    usage.add_message(&message((0, 1, 0, 0), 0.0, 0, 5, 9));
    assert!(!usage.is_empty());
}

#[test]
fn counts_times_and_costs_keep_their_scale() {
    assert_eq!(format_tokens(999), "999");
    assert_eq!(format_tokens(1_000), "1.0k");
    assert_eq!(format_tokens(999_949), "999.9k");
    assert_eq!(format_tokens(999_950), "1.0M");
    assert_eq!(format_tokens(2_500_000_000), "2.5B");
    assert_eq!(format_elapsed(Duration::from_millis(4_200)), "4.2s");
    assert_eq!(format_elapsed(Duration::from_secs(80)), "1m20s");
    assert_eq!(format_elapsed(Duration::from_mins(125)), "2h5m");
    assert_eq!(format_cost(0.056), "$0.06");
    assert_eq!(format_cost(0.004), "$0.004");
    assert_eq!(format_cost(0.0001), "<$0.001");
}

#[test]
fn the_footer_row_is_one_dim_ascii_row_at_the_turn_column() {
    let theme = Theme::builtin("eukhe", crate::theme::ColorMode::TrueColor);
    let rows = render_turn_footer(&mock_turn(), &theme, 60);
    assert_eq!(rows.len(), 1);
    let text: String = rows[0].iter().map(|span| span.content.as_str()).collect();
    assert!(text.starts_with("   -- 4.2s - 3 tools"), "{text}");
    assert!(crate::width::line_width(&rows[0]) <= 60);
    assert!(text.is_ascii());
    assert!(rows[0]
        .iter()
        .filter(|span| !span.content.trim().is_empty())
        .all(|span| span.style == theme.fg_style(ThemeColor::Dim)));
}
