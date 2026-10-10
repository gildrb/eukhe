//! Static system-prompt layers: human-editable markdown files assembled into
//! the cache-stable prefix of the prompt. The layers are, in order:
//!
//! 1. `core.md` — the harness description and the full programmatic-tool API
//!    surface (one tool: `ipython`; everything else lives in the REPL).
//! 2. `usage.md` — mandatory usage rules.
//! 3. `opinionated.md` — style and engineering guidelines users may override.
//!
//! Per-model additions follow them as one more cached segment, resolved from
//! the TOML rule map in [`super::model_prompts`].
//!
//! Layer files must never contain session-specific values: the cached
//! prefix ends where the dynamic tail (`system_prompt.rs`) begins, and the
//! cache-safety guard test pins that boundary.
//!
//! A layer may hold memory-specific blocks, each delimited by whole marker
//! lines: `<!-- eukhe:harness-memory -->` ... `<!-- /eukhe:harness-memory -->`
//! for sessions whose memory is the continual harness (memories, prompt
//! notes, proactive delegation), and `<!-- eukhe:chat-memory -->` ...
//! `<!-- /eukhe:chat-memory -->` for chat-memory sessions, whose only memory
//! is the chat. [`render_layer`] keeps the session's blocks and drops the
//! marker lines, so a harness-memory render is the file minus its
//! chat-memory blocks.

use crate::refinement::HarnessMemory;

/// The core harness layer (file `layers/core.md`).
pub const CORE_LAYER: &str = include_str!("layers/core.md");
/// The mandatory usage layer (file `layers/usage.md`).
pub const USAGE_LAYER: &str = include_str!("layers/usage.md");
/// The opinionated guidelines layer (file `layers/opinionated.md`).
pub const OPINIONATED_LAYER: &str = include_str!("layers/opinionated.md");

const HARNESS_MEMORY_OPEN: &str = "<!-- eukhe:harness-memory -->";
const HARNESS_MEMORY_CLOSE: &str = "<!-- /eukhe:harness-memory -->";
const CHAT_MEMORY_OPEN: &str = "<!-- eukhe:chat-memory -->";
const CHAT_MEMORY_CLOSE: &str = "<!-- /eukhe:chat-memory -->";

/// Render a layer file for a session's memory: keep the unmarked lines and
/// the blocks for `memory`, drop the other memory's blocks and every marker
/// line (see the module docs).
#[must_use]
pub fn render_layer(layer: &str, memory: HarnessMemory) -> String {
    let mut rendered = String::with_capacity(layer.len());
    let mut block: Option<HarnessMemory> = None;
    for line in layer.split_inclusive('\n') {
        match line.trim_end() {
            HARNESS_MEMORY_OPEN => block = Some(HarnessMemory::Harness),
            CHAT_MEMORY_OPEN => block = Some(HarnessMemory::Chat),
            HARNESS_MEMORY_CLOSE | CHAT_MEMORY_CLOSE => block = None,
            _text_line => {
                if block.is_none_or(|only| only == memory) {
                    rendered.push_str(line);
                }
            }
        }
    }
    rendered
}

/// The three constant layers (core, usage, opinionated) rendered for
/// `memory` and trimmed, with their names, in assembly order.
#[must_use]
pub fn constant_layers(memory: HarnessMemory) -> [(&'static str, String); 3] {
    [
        ("core", CORE_LAYER),
        ("usage", USAGE_LAYER),
        ("opinionated", OPINIONATED_LAYER),
    ]
    .map(|(name, layer)| (name, render_layer(layer, memory).trim().to_string()))
}

/// Source file of one layer (breakdown provenance).
#[must_use]
pub fn layer_source(name: &str) -> Option<&'static str> {
    match name {
        "core" => Some("prompts/layers/core.md"),
        "usage" => Some("prompts/layers/usage.md"),
        "opinionated" => Some("prompts/layers/opinionated.md"),
        "model-prompts" => Some("prompts/layers/model_prompts.toml"),
        _ => None,
    }
}

/// The cache-stable layered prefix for `memory` without per-model
/// additions: the three constant layers rendered for `memory`, joined with
/// blank lines. A chat-memory session's prompt puts its memory layer in
/// front of it; everything after is session-specific.
#[must_use]
pub fn static_prefix(memory: HarnessMemory) -> String {
    constant_layers(memory)
        .into_iter()
        .map(|(_name, text)| text)
        .collect::<Vec<_>>()
        .join("\n\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn static_prefix_is_layer_composition() {
        let prefix = static_prefix(HarnessMemory::Harness);
        assert!(prefix.starts_with("# eukhe harness"));
        assert!(prefix.contains("The following are mandatory rules"));
        assert!(prefix.contains("guidelines to agents have been shown"));
        // Exact composition: the three constant layers.
        assert_eq!(
            prefix,
            format!(
                "{}\n\n{}\n\n{}",
                render_layer(CORE_LAYER, HarnessMemory::Harness).trim(),
                render_layer(USAGE_LAYER, HarnessMemory::Harness).trim(),
                render_layer(OPINIONATED_LAYER, HarnessMemory::Harness).trim()
            )
        );
    }

    #[test]
    fn render_keeps_the_session_memory_blocks_only() {
        let layer = "a\n<!-- eukhe:harness-memory -->\nh1\nh2\n<!-- /eukhe:harness-memory -->\nb\n<!-- eukhe:chat-memory -->\nc1\n<!-- /eukhe:chat-memory -->\nz\n";
        assert_eq!(
            render_layer(layer, HarnessMemory::Harness),
            "a\nh1\nh2\nb\nz\n"
        );
        assert_eq!(render_layer(layer, HarnessMemory::Chat), "a\nb\nc1\nz\n");
    }

    /// The chat-memory session's layers carry no continual-harness memory
    /// surface and no push toward proactive delegation (the chat is the
    /// only memory; subagents run when the user asks).
    #[test]
    fn chat_memory_layers_drop_harness_memory_and_delegation() {
        let chat = static_prefix(HarnessMemory::Chat);
        let harness = static_prefix(HarnessMemory::Harness);
        for rendered in [&chat, &harness] {
            assert!(!rendered.contains("<!-- eukhe:"), "a marker line leaked");
            assert!(!rendered.contains("<!-- /eukhe:"), "a marker line leaked");
        }
        for harness_only in [
            "rlm.harness.create_memory",
            "rlm.harness.update_memory",
            "rlm.harness.delete_memory",
            "_prompt_note",
            "rlm.get_harness_state",
            "persistent memories",
            "Memories must be kept lean",
            "into memories",
            "assigns independent substantive tasks to separate workers",
            "Delegate parallel context-heavy research",
            "Write wrappers around `rlm.spawn`",
        ] {
            assert!(harness.contains(harness_only), "{harness_only:?}");
            assert!(!chat.contains(harness_only), "{harness_only:?}");
        }
        // The tools stay: subagents, skills, and subagent specs.
        for tool in [
            "rlm.spawn(",
            "rlm.harness.create_skill(",
            "rlm.harness.create_subagent(",
            "refine.run(",
        ] {
            assert!(chat.contains(tool), "{tool:?}");
        }
    }
}
