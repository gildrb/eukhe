//! The turn's usage footer: what one turn (a prompt and every model
//! request that answers it) cost, summed over its settled assistant
//! messages -- the time from its first request to its last token, its
//! tool calls and how many failed, the input and
//! output tokens, the prompt cache's reads and writes with the share of
//! the prompt the cache served, and the provider's cost. The live event
//! pump, the transcript rebuild and `eukhe -p` fold the same messages
//! through [`TurnUsage`] and print the same [`TurnUsage::row_text`].

use std::time::Duration;

use eukhe_types::ai::{AssistantContentBlock, AssistantMessage, StopReason};

use crate::glyphs::{ELLIPSIS, MARK_FOOTER, SEP};
use crate::rows::Gutter;
use crate::theme::{Theme, ThemeColor};
use crate::{Line, Span};

/// The usage of one turn so far.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct TurnUsage {
    input: u64,
    output: u64,
    cache_read: u64,
    cache_write: u64,
    cost: f64,
    tools: u32,
    failed: u32,
    started_ms: u64,
    ended_ms: u64,
    continues: bool,
}

impl TurnUsage {
    /// Add one settled assistant message: its usage, its tool calls, and
    /// its span (the request start to the last token).
    pub fn add_message(&mut self, message: &AssistantMessage) {
        let usage = &message.usage;
        self.input = self.input.saturating_add(usage.input);
        self.output = self.output.saturating_add(usage.output);
        self.cache_read = self.cache_read.saturating_add(usage.cache_read);
        self.cache_write = self.cache_write.saturating_add(usage.cache_write);
        self.cost += usage.cost.total.as_f64();
        let calls = message
            .content
            .iter()
            .filter(|block| matches!(block, AssistantContentBlock::ToolCall(_)))
            .count();
        self.tools = self
            .tools
            .saturating_add(u32::try_from(calls).unwrap_or(u32::MAX));
        self.continues = message.stop_reason == StopReason::ToolUse;
        let streamed = message
            .timing
            .and_then(|timing| timing.last_token_ms.or(timing.first_token_ms))
            .unwrap_or(0);
        if message.timestamp > 0 {
            self.started_ms = match self.started_ms {
                0 => message.timestamp,
                started => started.min(message.timestamp),
            };
            self.ended_ms = self
                .ended_ms
                .max(message.timestamp.saturating_add(streamed));
        }
    }

    /// One of the turn's tool calls returned an error.
    pub fn tool_failed(&mut self) {
        self.failed = self.failed.saturating_add(1);
    }

    /// No settled message reported a token yet: the turn has no footer.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.input == 0 && self.output == 0 && self.cache_read == 0 && self.cache_write == 0
    }

    /// The newest message called tools: the turn goes on with the next
    /// request, even past a prompt that lands meanwhile.
    pub(crate) fn continues(&self) -> bool {
        self.continues
    }

    /// From the first request's start to the last token.
    #[must_use]
    pub fn elapsed(&self) -> Option<Duration> {
        (self.ended_ms > self.started_ms)
            .then(|| Duration::from_millis(self.ended_ms - self.started_ms))
    }

    /// The share of the prompt the cache served, in whole percent (cut,
    /// never rounded up to a full hit): cache reads over the input, the
    /// reads and the writes. `None` while the cache neither read nor
    /// wrote.
    #[must_use]
    pub fn cache_hit_percent(&self) -> Option<u64> {
        if self.cache_read == 0 && self.cache_write == 0 {
            return None;
        }
        let prompt = self
            .input
            .saturating_add(self.cache_read)
            .saturating_add(self.cache_write);
        Some(u64::try_from(u128::from(self.cache_read) * 100 / u128::from(prompt)).unwrap_or(100))
    }

    /// The footer's text: `-- 4.2s - 3 tools, 1 failed - in 1.9k - out
    /// 352 - cache r 80.1k w 2.0k (95% hit) - $0.06`. The time, the tools,
    /// the cache and the cost drop out while they are unknown or zero.
    #[must_use]
    pub fn row_text(&self) -> String {
        format!("{MARK_FOOTER} {}", self.figures())
    }

    /// The footer's figures after its mark.
    fn figures(&self) -> String {
        let mut parts: Vec<String> = Vec::with_capacity(5);
        if let Some(elapsed) = self.elapsed() {
            parts.push(format_elapsed(elapsed));
        }
        if self.tools > 0 {
            let noun = if self.tools == 1 { "tool" } else { "tools" };
            parts.push(match self.failed {
                0 => format!("{} {noun}", self.tools),
                failed => format!("{} {noun}, {failed} failed", self.tools),
            });
        }
        parts.push(format!("in {}", format_tokens(self.input)));
        parts.push(format!("out {}", format_tokens(self.output)));
        if let Some(hit) = self.cache_hit_percent() {
            parts.push(format!(
                "cache r {} w {} ({hit}% hit)",
                format_tokens(self.cache_read),
                format_tokens(self.cache_write)
            ));
        }
        if self.cost > 0.0 {
            parts.push(format_cost(self.cost));
        }
        parts.join(SEP)
    }
}

/// The footer row: the `--` mark in the step gutter and the turn's
/// figures, all in the chrome tier, cut at `width`.
#[must_use]
pub fn render_turn_footer(usage: &TurnUsage, theme: &Theme, width: usize) -> Vec<Line> {
    let dim = theme.fg_style(ThemeColor::Dim);
    let lead = Gutter::Step.mark_col() + crate::width::str_width(MARK_FOOTER) + 1;
    let figures =
        crate::width::truncate_to_width(&usage.figures(), width.saturating_sub(lead + 1), ELLIPSIS);
    Gutter::Step.place(
        Some(Span::styled(MARK_FOOTER, dim)),
        vec![vec![Span::styled(figures, dim)]],
        theme,
        width,
    )
}

/// Tokens: the count under 1000, then one decimal of thousands (`1.9k`,
/// `80.1k`), millions (`1.2M`) or billions.
fn format_tokens(count: u64) -> String {
    let count_f = count as f64;
    match count {
        0..1_000 => count.to_string(),
        1_000..999_950 => format!("{:.1}k", count_f / 1e3),
        999_950..999_950_000 => format!("{:.1}M", count_f / 1e6),
        _ => format!("{:.1}B", count_f / 1e9),
    }
}

/// `4.2s` under a minute, `1m20s` under an hour, `2h5m` above.
fn format_elapsed(elapsed: Duration) -> String {
    let seconds = elapsed.as_secs();
    if seconds < 60 {
        format!("{:.1}s", elapsed.as_secs_f64())
    } else if seconds < 3600 {
        format!("{}m{}s", seconds / 60, seconds % 60)
    } else {
        format!("{}h{}m", seconds / 3600, seconds % 3600 / 60)
    }
}

/// Cents from one cent up (`$0.06`), a tenth of a cent below it (`$0.004`).
fn format_cost(cost: f64) -> String {
    if cost >= 0.01 {
        format!("${cost:.2}")
    } else if cost >= 0.001 {
        format!("${cost:.3}")
    } else {
        "<$0.001".to_string()
    }
}

#[cfg(test)]
mod tests;
