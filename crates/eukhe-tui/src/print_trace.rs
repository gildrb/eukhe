//! The `eukhe -p` progress trace: a print run's session events as the
//! transcript's own rows at the `overview` level, one plain line each (no
//! colour, no cursor movement), for the CLI to write to a terminal's
//! stderr. The rows come from the producers the TUI draws with, so the
//! two read the same.

use std::time::Instant;

use eukhe_types::ai::AssistantContentBlock;
use eukhe_types::daemon::SessionEvent;
use eukhe_types::session::AgentMessage;

use crate::chat::{ChatEntry, Detail};
use crate::custom_message::injected_prompt::render_injected_prompt;
use crate::snapshot::{event_to_update, TurnUpdate};
use crate::theme::{ColorMode, Theme};
use crate::tool_card::{marks_failed, render_tool_card, ToolCallCard, ToolResultView};
use crate::turn_usage::{render_turn_footer, TurnUsage};
use crate::Line;

/// The width a trace takes when the terminal reports none.
const FALLBACK_WIDTH: usize = 100;

/// One print run's progress: the tool calls still running and the
/// current turn's usage.
pub struct PrintTrace {
    theme: Theme,
    width: usize,
    running: Vec<ToolCallCard>,
    usage: TurnUsage,
}

impl PrintTrace {
    /// A trace whose rows fit the controlling terminal's width.
    #[must_use]
    pub fn for_terminal() -> Self {
        let width = crossterm::terminal::size()
            .map_or(FALLBACK_WIDTH, |(columns, _)| usize::from(columns).max(1));
        Self::new(width)
    }

    /// A trace whose rows fit `width` columns.
    #[must_use]
    pub fn new(width: usize) -> Self {
        Self {
            theme: Theme::builtin(eukhe_theme::DEFAULT_THEME_NAME, ColorMode::TrueColor),
            width,
            running: Vec::new(),
            usage: TurnUsage::default(),
        }
    }

    /// The footer of the turn so far, when it reported usage, then one
    /// blank row before what follows (the answer, the next turn); the
    /// next turn sums from zero.
    pub fn finish(&mut self) -> Vec<String> {
        let usage = std::mem::take(&mut self.usage);
        if usage.is_empty() {
            return Vec::new();
        }
        let mut lines = plain_rows(&render_turn_footer(&usage, &self.theme, self.width));
        lines.push(String::new());
        lines
    }

    /// The lines one session event settles: a thinking summary per
    /// thinking block when its message settles, a tool call's summary row
    /// when it ends, an injected prompt's row when it arrives, the
    /// turn's footer when its run ends. Streamed updates settle nothing
    /// and are not decoded.
    pub fn push(&mut self, event: &SessionEvent) -> Vec<String> {
        match event {
            SessionEvent::MessageEnd {
                message: AgentMessage::Assistant(message),
            } => {
                self.usage.add_message(message);
                message
                    .content
                    .iter()
                    .filter_map(|block| match block {
                        AssistantContentBlock::Thinking(block)
                            if !block.thinking.trim().is_empty() =>
                        {
                            Some(crate::rows::thinking_summary(&block.thinking, self.width))
                        }
                        _ => None,
                    })
                    .collect()
            }
            SessionEvent::AgentEnd { .. } => self.finish(),
            SessionEvent::ToolExecutionStart {
                tool_call_id,
                tool_name,
                args,
            } => {
                self.running.push(ToolCallCard {
                    id: tool_call_id.clone(),
                    name: crate::tool_card::ToolName::from(tool_name.as_str()),
                    args: args.clone(),
                    started: true,
                    started_at: Some(Instant::now()),
                    ..ToolCallCard::default()
                });
                Vec::new()
            }
            SessionEvent::ToolExecutionEnd {
                tool_call_id,
                result,
                is_error,
                ..
            } => {
                let Some(index) = self
                    .running
                    .iter()
                    .position(|card| card.id == *tool_call_id)
                else {
                    if *is_error {
                        self.usage.tool_failed();
                    }
                    return Vec::new();
                };
                let mut card = self.running.swap_remove(index);
                card.ended_at = Some(Instant::now());
                card.result = Some(ToolResultView::new(card.name.as_str(), result, *is_error));
                // The footer counts the calls their cards mark failed.
                if marks_failed(&card) {
                    self.usage.tool_failed();
                }
                let rows =
                    render_tool_card(&card, 0, Detail::Overview, &self.theme, self.width, false);
                plain_rows(&rows).into_iter().take(1).collect()
            }
            SessionEvent::MessageStart {
                message: AgentMessage::Custom(_),
                ..
            } => match event_to_update(event.clone()) {
                // A trace line has no blank lead row: plain_rows drops it.
                TurnUpdate::CustomRow(ChatEntry::InjectedPrompt(row)) => plain_rows(
                    &render_injected_prompt(&row, Detail::Overview, &self.theme, self.width, false),
                ),
                _ => Vec::new(),
            },
            _ => Vec::new(),
        }
    }
}

/// The non-blank rows' text, trailing padding cut.
fn plain_rows(rows: &[Line]) -> Vec<String> {
    rows.iter()
        .map(|row| {
            row.iter()
                .map(|span| span.content.as_str())
                .collect::<String>()
                .trim_end()
                .to_string()
        })
        .filter(|row| !row.is_empty())
        .collect()
}

#[cfg(test)]
mod tests {
    use serde_json::{json, Value};

    use super::*;

    fn usage(input: u64, output: u64, cache_read: u64, cache_write: u64) -> Value {
        json!({
            "input": input, "output": output, "cacheRead": cache_read, "cacheWrite": cache_write,
            "totalTokens": input + output + cache_read + cache_write,
            "cost": { "input": 0.0, "output": 0.0, "cacheRead": 0.0, "cacheWrite": 0.0, "total": 0.0 },
        })
    }

    fn assistant(content: &Value, usage: &Value, stop: &str) -> Value {
        json!({
            "role": "assistant", "content": content, "api": "anthropic-messages",
            "provider": "anthropic", "model": "claude-sonnet-4-5", "usage": usage,
            "stopReason": stop, "timestamp": 1,
        })
    }

    fn tool(id: &str, name: &str, args: &Value, output: &str, is_error: bool) -> [Value; 2] {
        [
            json!({ "type": "tool_execution_start", "toolCallId": id, "toolName": name, "args": args }),
            json!({ "type": "tool_execution_end", "toolCallId": id, "toolName": name,
                "result": { "content": [{ "type": "text", "text": output }] }, "isError": is_error }),
        ]
    }

    /// The audit's mock turn (section 2a): a reminder, thinking, three
    /// tool calls (the last one failing), then thinking and the answer.
    fn mock_turn() -> Vec<SessionEvent> {
        let reminder = json!({ "role": "custom", "customType": "director_continuation",
            "display": false, "timestamp": 1,
            "content": "<system-reminder>Run the tests before you answer.</system-reminder>" });
        let first = json!([
            { "type": "thinking", "thinking": "The user wants the greeting fixed. First read `src/hello.rs` to see what it prints.\n\nThen patch the string and run the tests." },
            { "type": "text", "text": "Reading the file, then patching it." },
            { "type": "toolCall", "id": "tc-read", "name": "read", "arguments": { "path": "src/hello.rs" } },
            { "type": "toolCall", "id": "tc-edit", "name": "edit", "arguments": { "input": "[src/hello.rs#AB12]\nPUT 2.=2:\n+    println!(\"Hello, world!\");" } },
            { "type": "toolCall", "id": "tc-test", "name": "bash", "arguments": { "script": "cargo test -q" } },
        ]);
        let last = json!([
            { "type": "thinking", "thinking": "The compile error is in a different file, unrelated to my patch. Report it." },
            { "type": "text", "text": "Fixed the greeting in `src/hello.rs`." },
        ]);
        let mut events = vec![
            json!({ "type": "agent_start" }),
            json!({ "type": "turn_start" }),
            json!({ "type": "message_start", "message": { "role": "user", "content": "fix the greeting in hello.rs", "timestamp": 1 } }),
            json!({ "type": "message_start", "message": reminder }),
            json!({ "type": "message_end", "message": reminder }),
            json!({ "type": "message_start", "message": assistant(&json!([]), &usage(1840, 212, 38912, 2048), "toolUse"), "assistantMessageEvent": { "type": "start" } }),
            json!({ "type": "message_update", "message": assistant(&first, &usage(1840, 212, 38912, 2048), "toolUse"), "assistantMessageEvent": { "type": "text_delta", "delta": "Reading" } }),
            json!({ "type": "message_end", "message": assistant(&first, &usage(1840, 212, 38912, 2048), "toolUse") }),
        ];
        events.extend(tool("tc-read", "read", &json!({ "path": "src/hello.rs" }),
            "[src/hello.rs#AB12]\n1:fn greet() {\n2:    println!(\"Helo world\");\n3:}\n4:\n5:fn main() { greet(); }", false));
        events.extend(tool("tc-edit", "edit", &json!({ "input": "[src/hello.rs#AB12]\nPUT 2.=2:\n+    println!(\"Hello, world!\");" }),
            "[src/hello.rs#CD34]\n1:fn greet() {\n2:    println!(\"Hello, world!\");\n3:}", false));
        events.extend(tool("tc-test", "bash", &json!({ "script": "cargo test -q" }),
            "error[E0425]: cannot find function `greet2` in this scope\n --> src/main.rs:9:5\nerror: could not compile `demo` (bin \"demo\") due to 1 previous error", true));
        events.extend([
            json!({ "type": "message_start", "message": assistant(&json!([]), &usage(96, 140, 41200, 0), "stop"), "assistantMessageEvent": { "type": "start" } }),
            json!({ "type": "message_end", "message": assistant(&last, &usage(96, 140, 41200, 0), "stop") }),
            json!({ "type": "turn_end" }),
            json!({ "type": "agent_end", "messages": [] }),
        ]);
        events
            .into_iter()
            .map(|event| serde_json::from_value(event).expect("a session event"))
            .collect()
    }

    /// The trace's lines.
    fn trace(width: usize) -> Vec<String> {
        let mut trace = PrintTrace::new(width);
        let mut lines: Vec<String> = mock_turn()
            .iter()
            .flat_map(|event| trace.push(event))
            .collect();
        lines.extend(trace.finish());
        lines
    }

    #[test]
    fn the_mock_turn_traces_its_steps_then_its_footer() {
        let lines = trace(100);
        let position = |prefix: &str| {
            lines
                .iter()
                .position(|line| line.trim_start().starts_with(prefix))
                .unwrap_or_else(|| panic!("no {prefix:?} line in {lines:#?}"))
        };
        let order = [
            position("+ thinking: The user"),
            position("ok read "),
            position("ok edit "),
            position("x  bash "),
            position("+ thinking: The compile"),
            position("-- "),
        ];
        assert!(order.is_sorted(), "{order:?} in {lines:#?}");
        assert_eq!(
            lines[order[0]],
            "   + thinking: The user wants the greeting fixed. First read src/hello.rs to see what it prints."
        );
        assert_eq!(
            lines[order[4]],
            "   + thinking: The compile error is in a different file, unrelated to my patch. Report it."
        );
        assert_eq!(
            lines[order[5]..],
            [
                "   -- 3 tools, 1 failed - in 1.9k - out 352 - cache r 80.1k w 2.0k (95% hit)",
                "",
            ]
        );
        assert!(
            lines
                .iter()
                .all(|line| line.is_ascii() && line.len() <= 100),
            "{lines:#?}"
        );
    }

    #[test]
    fn a_streamed_update_settles_no_line() {
        let mut trace = PrintTrace::new(100);
        let lines: Vec<String> = mock_turn()
            .iter()
            .filter(|event| matches!(event, SessionEvent::MessageUpdate { .. }))
            .flat_map(|event| trace.push(event))
            .collect();
        assert!(lines.is_empty(), "{lines:#?}");
        assert!(trace.finish().is_empty());
    }
}
