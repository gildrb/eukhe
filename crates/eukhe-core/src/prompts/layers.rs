//! Static system-prompt layers: human-editable markdown files assembled into
//! the cache-stable prefix of the prompt. The layers are, in order:
//!
//! 1. `core.md` — the harness description and the full programmatic-tool API
//!    surface (one tool: `ipython`; everything else lives in the REPL).
//! 2. `usage.md` — mandatory usage rules.
//! 3. `opinionated.md` — style and engineering guidelines users may override.
//! 4. `per_model.md` — the per-model instruction map (blocks keyed by model
//!    selector patterns; shipped empty, the mechanism is live).
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
/// The per-model instruction map (file `layers/per_model.md`).
pub const PER_MODEL_MAP: &str = include_str!("layers/per_model.md");

/// Layer names, in assembly order, for breakdown rendering.
pub const LAYER_NAMES: [&str; 4] = ["core", "usage", "opinionated", "per-model"];

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
        "per-model" => Some("prompts/layers/per_model.md"),
        _ => None,
    }
}

/// One per-model instruction block from the map file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PerModelBlock {
    /// Comma-separated selector patterns from the block header.
    pub patterns: Vec<String>,
    /// The instruction text between the markers.
    pub text: String,
}

/// Parse the per-model map. Blocks are delimited by
/// `<!-- eukhe:model: <patterns> -->` ... `<!-- /eukhe:model -->`; whitespace-only
/// blocks are ignored. Everything outside blocks (the format documentation)
/// is not prompt content.
pub fn parse_per_model_blocks(map: &str) -> Vec<PerModelBlock> {
    const OPEN: &str = "<!-- eukhe:model:";
    const CLOSE: &str = "<!-- /eukhe:model -->";
    // Documentation comments (anything that is not a eukhe:model block) are
    // not prompt content; drop them before scanning for blocks so prose
    // examples cannot smuggle in markers.
    let map = strip_documentation_comments(map);
    let mut blocks = Vec::new();
    let mut rest = map.as_str();
    while let Some(start) = rest.find(OPEN) {
        let after_open = &rest[start + OPEN.len()..];
        let Some(header_end) = after_open.find("-->") else {
            break;
        };
        let patterns = after_open[..header_end]
            .split(',')
            .map(str::trim)
            .filter(|pattern| !pattern.is_empty())
            .map(str::to_string)
            .collect::<Vec<_>>();
        let body = &after_open[header_end + 3..];
        let Some(end) = body.find(CLOSE) else { break };
        let text = body[..end].trim().to_string();
        if !text.is_empty() {
            blocks.push(PerModelBlock { patterns, text });
        }
        rest = &body[end + CLOSE.len()..];
    }
    blocks
}

/// Remove `<!-- ... -->` spans that are neither `eukhe:model` markers nor their
/// terminators.
fn strip_documentation_comments(map: &str) -> String {
    let mut out = String::with_capacity(map.len());
    let mut rest = map;
    while let Some(start) = rest.find("<!--") {
        out.push_str(&rest[..start]);
        let Some(end) = rest[start..].find("-->") else {
            // Unterminated comment: drop the remainder.
            return out;
        };
        let inner = &rest[start + 4..start + end];
        if inner.trim_start().starts_with("eukhe:model:") || inner.trim() == "/eukhe:model" {
            out.push_str(&rest[start..start + end + 3]);
        }
        rest = &rest[start + end + 3..];
    }
    out.push_str(rest);
    out
}

/// Wildcard match: `*` matches any run of characters, the rest matches
/// literally.
#[must_use]
pub fn selector_matches(pattern: &str, selector: &str) -> bool {
    let mut parts = pattern.split('*');
    let mut rest = selector;
    let Some(first) = parts.next() else {
        return selector.is_empty();
    };
    if !rest.starts_with(first) {
        return false;
    }
    rest = &rest[first.len()..];
    for part in parts {
        if part.is_empty() {
            continue;
        }
        let Some(at) = rest.find(part) else {
            return false;
        };
        rest = &rest[at + part.len()..];
    }
    // A pattern ending in `*` matches the remainder; otherwise the pattern
    // must end exactly at the selector's end.
    pattern.ends_with('*') || rest.is_empty()
}

/// The per-model instructions that apply to `model` (a resolved
/// `provider/id` selector), in map order. `None` model selects blocks whose
/// patterns include `*`.
#[must_use]
pub fn per_model_text(model: Option<&str>) -> Vec<String> {
    parse_per_model_blocks(PER_MODEL_MAP)
        .into_iter()
        .filter(|block| {
            model.is_some_and(|selector| {
                block
                    .patterns
                    .iter()
                    .any(|pattern| selector_matches(pattern, selector))
            })
        })
        .map(|block| block.text)
        .collect()
}

/// The cache-stable layered prefix for `model` and `memory`: the three
/// constant layers rendered for `memory` plus any matching per-model
/// blocks, joined with blank lines. A chat-memory session's prompt puts its
/// memory layer in front of it; everything after is session-specific.
#[must_use]
pub fn static_prefix(model: Option<&str>, memory: HarnessMemory) -> String {
    let mut parts: Vec<String> = constant_layers(memory)
        .into_iter()
        .map(|(_name, text)| text)
        .collect();
    parts.extend(per_model_text(model));
    parts.join("\n\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn per_model_map_ships_empty() {
        // The shipped map is the blockless format reference: nothing parses
        // as a block, so no model selects any per-model text.
        assert!(parse_per_model_blocks(PER_MODEL_MAP).is_empty());
        assert!(per_model_text(None).is_empty());
        assert!(per_model_text(Some("mock/mock-1")).is_empty());
    }

    #[test]
    fn parses_blocks_and_matches_selectors() {
        let map = "<!-- eukhe:model: openai/gpt-5, anthropic/claude-* -->\nUse thinking mode.\n<!-- /eukhe:model -->\n<!-- eukhe:model: * -->\nFallback.\n<!-- /eukhe:model -->\n";
        let blocks = parse_per_model_blocks(map);
        assert_eq!(blocks.len(), 2);
        assert_eq!(
            blocks[0].patterns,
            vec!["openai/gpt-5", "anthropic/claude-*"]
        );
        assert_eq!(blocks[0].text, "Use thinking mode.");
        assert_eq!(blocks[1].patterns, vec!["*"]);
        assert!(selector_matches(
            "anthropic/claude-*",
            "anthropic/claude-4-sonnet"
        ));
        assert!(!selector_matches("anthropic/claude-*", "openai/gpt-5"));
        assert!(selector_matches("*", "anything"));
    }

    #[test]
    fn empty_blocks_are_ignored() {
        let map = "<!-- eukhe:model: * -->\n   \n<!-- /eukhe:model -->\n";
        assert!(parse_per_model_blocks(map).is_empty());
    }

    #[test]
    fn static_prefix_is_layer_composition() {
        let prefix = static_prefix(None, HarnessMemory::Harness);
        assert!(prefix.starts_with("# eukhe harness"));
        assert!(prefix.contains("The following are mandatory rules"));
        assert!(prefix.contains("guidelines to agents have been shown"));
        // Exact composition: the three constant layers, no per-model text.
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
        let chat = static_prefix(None, HarnessMemory::Chat);
        let harness = static_prefix(None, HarnessMemory::Harness);
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
