//! Static system-prompt layers: human-editable markdown files assembled into
//! the cache-stable prefix of the prompt. The layers are, in order:
//!
//! 1. `core.md` — the harness description, the core tools (`bash`, `jobs`,
//!    the file functions, `rlm.harness`), the one-loop subagent policy, and
//!    how skills load; every other programmatic tool's API lives in the
//!    skill that owns it (`skills/*/`), never here.
//! 2. `usage.md` — mandatory usage rules.
//! 3. `opinionated.md` — style and engineering guidelines users may override.
//!
//! Per-model additions follow them as one more cached segment, resolved from
//! the TOML rule map in [`super::model_prompts`].
//!
//! `critical.md` is no prefix layer: its `<critical>` block closes the
//! install-stable tail, after every extension's section; only the project's
//! instructions and the environment follow (`durable::prompt::extensions`).
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
/// The closing `<critical>` block (file `layers/critical.md`).
pub const CRITICAL_LAYER: &str = include_str!("layers/critical.md");

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
        "critical" => Some("prompts/layers/critical.md"),
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

    /// No marker line reaches a rendered layer, whatever the memory.
    #[test]
    fn rendered_layers_carry_no_marker_lines() {
        for memory in [HarnessMemory::Chat, HarnessMemory::Harness] {
            let rendered = static_prefix(memory);
            assert!(!rendered.contains("<!-- eukhe:"), "a marker line leaked");
            assert!(!rendered.contains("<!-- /eukhe:"), "a marker line leaked");
        }
    }

    /// Main in the `main-worker` shape (the user's approved design) routes
    /// each message to its worker by tool choice instead of doing the work;
    /// every other root does the user's tasks itself.
    #[test]
    fn main_routes_each_message_to_its_worker() {
        let root = crate::memory::memory_system_layer();
        let main = crate::memory::main_system_layer();
        assert!(root.contains("Do the user's tasks yourself"));
        assert!(!main.contains("Do the user's tasks yourself"));
        for route in [
            "worker_status",
            "worker_forward with\n  kind \"context\"",
            "worker_forward with kind \"redirect\"",
            "new work: worker_assign",
            "never run long work yourself",
        ] {
            assert!(main.contains(route), "{route:?}");
            assert!(!root.contains(route), "{route:?}");
        }
    }

    /// Main's worker runs on a chat of its own, as a top-level session
    /// does: its layer opens as a session's own chat, never as a subagent
    /// handed main's view, and carries the worker doctrine.
    #[test]
    fn the_worker_layer_is_its_own_chat_with_the_doctrine() {
        let root = crate::memory::memory_system_layer();
        let worker = crate::memory::worker_system_layer();
        let opening = root.split("\n\n").next().expect("an opening");
        assert!(worker.starts_with(opening));
        assert!(!worker.contains("You are a subagent"));
        assert!(!worker.contains("Your first message holds the view"));
        assert!(worker.contains("You are the worker: main talks with the user"));
        assert!(!root.contains("You are the worker"));
    }
}
