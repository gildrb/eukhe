//! Reasoning a model leaked into its visible text: a server that does not
//! split reasoning into its own field streams the chat template's reasoning
//! section (`<think>...</think>`, ...) as `delta.content`. The scanner
//! splits that content into visible text and reasoning, live (the Gemini
//! ` ```thinking ` fence is not recognized).

/// One piece of scanned content, in stream order.
pub(crate) enum Scanned {
    /// Visible text.
    Text(String),
    /// Reasoning inside a reasoning section.
    Thinking(String),
    /// A bare `</think>`: the chat template prefilled the opener, so the
    /// text before it was reasoning (when it is all the reply so far).
    ImpliedClose,
}

/// A reasoning section's delimiters.
struct Tag {
    open: &'static str,
    close: &'static str,
}

/// Every in-band reasoning section, in the order the scanner tries them.
static TAGS: [Tag; 6] = [
    // deepseek, glm, hermes, kimi, qwen3.
    Tag {
        open: "<think>",
        close: IMPLIED_CLOSE,
    },
    // anthropic, minimax, xml.
    Tag {
        open: "<thinking>",
        close: "</thinking>",
    },
    Tag {
        open: "<scratchpad>",
        close: "</scratchpad>",
    },
    // The gemma reasoning channel.
    Tag {
        open: "<|channel>thought\n",
        close: "<channel|>",
    },
    // The harmony analysis channel, rendered and as a bare leak.
    Tag {
        open: "<|start|>assistant<|channel|>analysis<|message|>",
        close: "<|end|>",
    },
    Tag {
        open: "<|channel|>analysis<|message|>",
        close: "<|end|>",
    },
];

/// The close of the section whose opener chat templates prefill
/// (DeepSeek-R1, Qwen3-Thinking): the model streams only this.
const IMPLIED_CLOSE: &str = "</think>";

/// A held tail is a proper prefix of a delimiter, so it is shorter than
/// the longest one (the rendered harmony opener).
const MAX_DELIMITER_LEN: usize = 48;

/// The next boundary in idle visible text.
enum Hit {
    Open(usize, &'static Tag),
    ImpliedClose(usize),
    /// A Markdown code span or fence opener: a run of this many backticks.
    Code(usize, usize),
    /// The tail may still grow into a delimiter or a longer backtick run.
    Hold(usize),
}

/// Splits streamed content into visible text and leaked reasoning. A
/// reasoning tag inside a Markdown code span or fenced block stays text.
pub(crate) struct LeakedThinkingScanner {
    buffer: String,
    /// The close tag of the open reasoning section.
    close: Option<&'static str>,
    /// Backticks that opened the code span or fence the text is inside.
    code_ticks: usize,
    /// The open code region is a fenced block (it closes on a fence line).
    code_fenced: bool,
    /// Leading spaces of the current output line; `None` once the line has
    /// another character. A fence may open the stream or sit at most three
    /// spaces in.
    line_indent: Option<usize>,
}

impl LeakedThinkingScanner {
    pub(crate) const fn new() -> Self {
        Self {
            buffer: String::new(),
            close: None,
            code_ticks: 0,
            code_fenced: false,
            line_indent: Some(0),
        }
    }

    /// Scan the next content delta.
    pub(crate) fn feed(&mut self, text: &str) -> Vec<Scanned> {
        self.buffer.push_str(text);
        self.consume(/*at_end*/ false)
    }

    /// The stream ended: release what was held back. An unterminated
    /// reasoning section is reasoning.
    pub(crate) fn flush(&mut self) -> Vec<Scanned> {
        let mut out = self.consume(/*at_end*/ true);
        let rest = std::mem::take(&mut self.buffer);
        if !rest.is_empty() {
            out.push(if self.close.is_some() {
                Scanned::Thinking(rest)
            } else {
                Scanned::Text(rest)
            });
        }
        self.close = None;
        out
    }

    fn consume(&mut self, at_end: bool) -> Vec<Scanned> {
        let mut out = Vec::new();
        while !self.buffer.is_empty() {
            if let Some(close) = self.close {
                let Some(at) = self.buffer.find(close) else {
                    // Hold a tail that may grow into the close tag.
                    let kept = if at_end {
                        0
                    } else {
                        (1..close.len().min(self.buffer.len() + 1))
                            .rev()
                            .find(|&len| self.buffer.ends_with(&close[..len]))
                            .unwrap_or(0)
                    };
                    let tail = self.buffer.split_off(self.buffer.len() - kept);
                    push_thinking(&mut out, std::mem::replace(&mut self.buffer, tail));
                    break;
                };
                let rest = self.buffer.split_off(at + close.len());
                self.buffer.truncate(at);
                push_thinking(&mut out, std::mem::replace(&mut self.buffer, rest));
                self.close = None;
                continue;
            }
            if self.code_ticks > 0 {
                if self.emit_code(at_end, &mut out) {
                    continue;
                }
                break;
            }
            let Some(hit) = scan_visible(&self.buffer, at_end) else {
                let text = std::mem::take(&mut self.buffer);
                self.push_text(&mut out, text);
                break;
            };
            let (Hit::Open(index, _)
            | Hit::ImpliedClose(index)
            | Hit::Code(index, _)
            | Hit::Hold(index)) = hit;
            let rest = self.buffer.split_off(index);
            let before = std::mem::replace(&mut self.buffer, rest);
            self.push_text(&mut out, before);
            match hit {
                Hit::Hold(_) => break,
                Hit::ImpliedClose(_) => {
                    self.buffer.drain(..IMPLIED_CLOSE.len());
                    out.push(Scanned::ImpliedClose);
                }
                Hit::Code(_, ticks) => {
                    let fenced = ticks >= 3 && self.line_indent.is_some_and(|indent| indent <= 3);
                    let rest = self.buffer.split_off(ticks);
                    let run = std::mem::replace(&mut self.buffer, rest);
                    self.push_text(&mut out, run);
                    self.code_ticks = ticks;
                    self.code_fenced = fenced;
                }
                Hit::Open(_, tag) => {
                    self.buffer.drain(..tag.open.len());
                    self.close = Some(tag.close);
                }
            }
        }
        out
    }

    /// Emit buffered content inside a Markdown code region, where no
    /// reasoning tag is recognized. A fenced block closes on a fence line
    /// (only backticks, at least as many as its opener); an inline span on
    /// the first backtick run of exactly the opener's length. `true` when
    /// the region closed and scanning goes on, `false` when it held back.
    fn emit_code(&mut self, at_end: bool, out: &mut Vec<Scanned>) -> bool {
        if self.code_fenced {
            if let Some(end) = fence_close_end(&self.buffer, self.code_ticks, at_end) {
                let rest = self.buffer.split_off(end);
                let block = std::mem::replace(&mut self.buffer, rest);
                self.push_text(out, block);
                self.code_ticks = 0;
                self.code_fenced = false;
                return true;
            }
            if at_end {
                let block = std::mem::take(&mut self.buffer);
                self.push_text(out, block);
                self.code_ticks = 0;
                self.code_fenced = false;
            } else if let Some(newline) = self.buffer.rfind('\n') {
                // Stream whole lines; hold the last (possibly partial) one.
                let rest = self.buffer.split_off(newline + 1);
                let lines = std::mem::replace(&mut self.buffer, rest);
                self.push_text(out, lines);
            }
            return false;
        }
        let ticks = self.code_ticks;
        let close = backtick_run_of(&self.buffer, ticks)
            .filter(|close| at_end || close + ticks < self.buffer.len());
        if let Some(close) = close {
            let rest = self.buffer.split_off(close + ticks);
            let span = std::mem::replace(&mut self.buffer, rest);
            self.push_text(out, span);
            self.code_ticks = 0;
            return true;
        }
        // No settled close yet: hold a trailing backtick run that may still
        // grow into, or past, the closing delimiter.
        let kept = if at_end {
            0
        } else {
            self.buffer.len() - self.buffer.trim_end_matches('`').len()
        };
        let tail = self.buffer.split_off(self.buffer.len() - kept);
        let text = std::mem::replace(&mut self.buffer, tail);
        self.push_text(out, text);
        if at_end {
            self.code_ticks = 0;
        }
        false
    }

    fn push_text(&mut self, out: &mut Vec<Scanned>, text: String) {
        if text.is_empty() {
            return;
        }
        let line_start = text.rfind('\n').map(|newline| newline + 1);
        let mut indent = if line_start.is_some() {
            Some(0)
        } else {
            self.line_indent
        };
        for character in text[line_start.unwrap_or(0)..].chars() {
            indent = indent.filter(|_| character == ' ').map(|indent| indent + 1);
        }
        self.line_indent = indent;
        match out.last_mut() {
            Some(Scanned::Text(last)) => last.push_str(&text),
            Some(Scanned::Thinking(_) | Scanned::ImpliedClose) | None => {
                out.push(Scanned::Text(text));
            }
        }
    }
}

fn push_thinking(out: &mut Vec<Scanned>, thinking: String) {
    if !thinking.is_empty() {
        out.push(Scanned::Thinking(thinking));
    }
}

/// The earliest boundary in idle visible text: a reasoning section's
/// opener, a bare implied close, a Markdown code opener, or (while more
/// content may follow) a tail that is a proper prefix of a delimiter.
fn scan_visible(buffer: &str, at_end: bool) -> Option<Hit> {
    // Only the tail can be a proper prefix of a delimiter.
    let hold_from = if at_end {
        buffer.len()
    } else {
        (buffer.len() + 1).saturating_sub(MAX_DELIMITER_LEN)
    };
    for (index, byte) in buffer.bytes().enumerate() {
        // Every delimiter starts with `<`; code starts with a backtick.
        if byte != b'<' && byte != b'`' {
            continue;
        }
        let rest = &buffer[index..];
        if let Some(tag) = TAGS.iter().find(|tag| rest.starts_with(tag.open)) {
            return Some(Hit::Open(index, tag));
        }
        if rest.starts_with(IMPLIED_CLOSE) {
            return Some(Hit::ImpliedClose(index));
        }
        if index >= hold_from
            && TAGS
                .iter()
                .map(|tag| tag.open)
                .chain([IMPLIED_CLOSE])
                .any(|delimiter| delimiter.len() > rest.len() && delimiter.starts_with(rest))
        {
            return Some(Hit::Hold(index));
        }
        if byte == b'`' {
            let ticks = rest.len() - rest.trim_start_matches('`').len();
            if !at_end && ticks == rest.len() {
                return Some(Hit::Hold(index));
            }
            return Some(Hit::Code(index, ticks));
        }
    }
    None
}

/// The index of the first maximal backtick run of exactly `ticks`.
fn backtick_run_of(buffer: &str, ticks: usize) -> Option<usize> {
    let mut from = 0;
    while let Some(offset) = buffer[from..].find('`') {
        let start = from + offset;
        let run = buffer.len() - start - buffer[start..].trim_start_matches('`').len();
        if run == ticks {
            return Some(start);
        }
        from = start + run;
    }
    None
}

/// The index just past the first closing fence line of a block opened with
/// `ticks` backticks: a line of only backticks, at least `ticks` of them. A
/// line without its newline counts only when no more content follows.
fn fence_close_end(buffer: &str, ticks: usize, at_end: bool) -> Option<usize> {
    let mut start = 0;
    loop {
        let newline = buffer[start..].find('\n').map(|offset| start + offset);
        let line = buffer[start..newline.unwrap_or(buffer.len())].trim();
        if line.len() >= ticks
            && line.bytes().all(|byte| byte == b'`')
            && (newline.is_some() || at_end)
        {
            return Some(newline.map_or(buffer.len(), |newline| newline + 1));
        }
        start = newline? + 1;
    }
}
