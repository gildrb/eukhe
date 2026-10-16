//! The live partial message shared by every event of one response.

use std::fmt;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use serde::{Deserialize, Deserializer, Serialize, Serializer};

use super::content::AssistantContentBlock;
use super::event::AssistantMessageEvent;
use super::message::AssistantMessage;

/// The response so far, shared by every event of one stream (TS passes one
/// live accumulator object in every event).
///
/// Cloning shares the message. The producer publishes each change before it
/// pushes the event that describes it, so [`Partial::read`] observes at least
/// the state of the event being handled, possibly later. A delta costs the
/// delta, not a copy of the message: readers copy only what they read.
#[derive(Clone)]
pub struct Partial(Arc<Mutex<AssistantMessage>>);

impl Partial {
    /// A partial holding `message`.
    #[must_use]
    pub fn new(message: AssistantMessage) -> Self {
        Self(Arc::new(Mutex::new(message)))
    }

    fn lock(&self) -> MutexGuard<'_, AssistantMessage> {
        self.0.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Run `read` on the current message.
    pub fn read<R>(&self, read: impl FnOnce(&AssistantMessage) -> R) -> R {
        read(&self.lock())
    }

    /// A copy of the current message.
    #[must_use]
    pub fn snapshot(&self) -> AssistantMessage {
        self.read(AssistantMessage::clone)
    }

    /// Make the shared message a copy of `output` (a change no event
    /// describes).
    pub fn replace(&self, output: &AssistantMessage) {
        self.lock().clone_from(output);
    }

    /// Make the shared message equal `output` after the change `event`
    /// describes. A delta appends to (or, for tool calls, replaces) its block
    /// and refreshes the message fields; any other event copies the message.
    /// Text and thinking grow by appending between their `*_start` and
    /// `*_end` (the event protocol); a delta that rewrote its block copies
    /// the block whole.
    pub fn publish(&self, output: &AssistantMessage, event: &AssistantMessageEvent) {
        let mut shared = self.lock();
        let grown = match event {
            AssistantMessageEvent::TextDelta { content_index, .. }
            | AssistantMessageEvent::ThinkingDelta { content_index, .. }
            | AssistantMessageEvent::ToolCallDelta { content_index, .. } => {
                grow(&mut shared, output, *content_index)
            }
            AssistantMessageEvent::Start { .. }
            | AssistantMessageEvent::TextStart { .. }
            | AssistantMessageEvent::TextEnd { .. }
            | AssistantMessageEvent::ThinkingStart { .. }
            | AssistantMessageEvent::ThinkingEnd { .. }
            | AssistantMessageEvent::ToolCallStart { .. }
            | AssistantMessageEvent::ToolCallEnd { .. }
            | AssistantMessageEvent::Done { .. }
            | AssistantMessageEvent::Error { .. } => false,
        };
        if !grown {
            shared.clone_from(output);
        }
        debug_assert!(
            *shared == *output,
            "a {} event changed the partial outside its block",
            event.type_name()
        );
    }
}

/// Grow `shared` to `output` through block `index`; `false` when the block
/// is missing or changed kind, which needs a full copy.
fn grow(shared: &mut AssistantMessage, output: &AssistantMessage, index: usize) -> bool {
    if shared.content.len() != output.content.len() {
        return false;
    }
    let (Some(target), Some(source)) = (shared.content.get_mut(index), output.content.get(index))
    else {
        return false;
    };
    match (target, source) {
        (AssistantContentBlock::Text(target), AssistantContentBlock::Text(source)) => {
            append(&mut target.text, &source.text);
            assign(&mut target.text_signature, &source.text_signature);
            assign(&mut target.cache_breakpoint, &source.cache_breakpoint);
        }
        (AssistantContentBlock::Thinking(target), AssistantContentBlock::Thinking(source)) => {
            append(&mut target.thinking, &source.thinking);
            assign(&mut target.thinking_signature, &source.thinking_signature);
            assign(&mut target.redacted, &source.redacted);
        }
        (AssistantContentBlock::ToolCall(target), AssistantContentBlock::ToolCall(source)) => {
            assign(target, source);
        }
        (
            AssistantContentBlock::Text(_)
            | AssistantContentBlock::Thinking(_)
            | AssistantContentBlock::ToolCall(_),
            AssistantContentBlock::Text(_)
            | AssistantContentBlock::Thinking(_)
            | AssistantContentBlock::ToolCall(_),
        ) => return false,
    }
    let AssistantMessage {
        content: _,
        api,
        provider,
        model,
        response_model,
        response_id,
        provider_thinking_level,
        thinking_level,
        diagnostics,
        usage,
        stop_reason,
        deferred,
        error_message,
        raw_stop_reason,
        end_turn,
        timestamp,
        duration_ms,
    } = output;
    assign(&mut shared.api, api);
    assign(&mut shared.provider, provider);
    assign(&mut shared.model, model);
    assign(&mut shared.response_model, response_model);
    assign(&mut shared.response_id, response_id);
    assign(&mut shared.provider_thinking_level, provider_thinking_level);
    assign(&mut shared.thinking_level, thinking_level);
    assign(&mut shared.diagnostics, diagnostics);
    assign(&mut shared.usage, usage);
    assign(&mut shared.stop_reason, stop_reason);
    assign(&mut shared.deferred, deferred);
    assign(&mut shared.error_message, error_message);
    assign(&mut shared.raw_stop_reason, raw_stop_reason);
    assign(&mut shared.end_turn, end_turn);
    assign(&mut shared.timestamp, timestamp);
    assign(&mut shared.duration_ms, duration_ms);
    true
}

/// Append the part of `source` past `target`; copy it whole when `target`
/// is not a prefix of it (a provider that rewrote the block).
fn append(target: &mut String, source: &str) {
    match source.strip_prefix(target.as_str()) {
        Some(suffix) => target.push_str(suffix),
        None => source.clone_into(target),
    }
}

fn assign<T: PartialEq + Clone>(target: &mut T, source: &T) {
    if target != source {
        target.clone_from(source);
    }
}

impl From<AssistantMessage> for Partial {
    fn from(message: AssistantMessage) -> Self {
        Self::new(message)
    }
}

impl PartialEq for Partial {
    fn eq(&self, other: &Self) -> bool {
        if Arc::ptr_eq(&self.0, &other.0) {
            return true;
        }
        let other = other.snapshot();
        self.read(|this| *this == other)
    }
}

impl fmt::Debug for Partial {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.read(|message| message.fmt(formatter))
    }
}

impl Serialize for Partial {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.read(|message| message.serialize(serializer))
    }
}

impl<'de> Deserialize<'de> for Partial {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        AssistantMessage::deserialize(deserializer).map(Self::new)
    }
}

#[cfg(test)]
mod tests {
    use super::append;

    #[test]
    fn a_delta_that_is_not_an_append_replaces_the_text() {
        let mut target = "hello".to_owned();
        append(&mut target, "hello world");
        assert_eq!(target, "hello world");
        // Same length prefix, other content: release builds must not keep
        // the stale head.
        append(&mut target, "HELLO world!");
        assert_eq!(target, "HELLO world!");
        append(&mut target, "short");
        assert_eq!(target, "short");
    }
}
