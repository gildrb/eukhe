//! The refreshed-models overlay: the models a provider's own listing
//! offers that the built-in catalog lacks, kept locally beside it
//! (`models-refresh.json` in the agent dir; the read and the atomic write
//! live with the registry in eukhe-core).
//!
//! Pure: a listing maps to catalog models here, and the overlay joins the
//! built-in catalog here. The overlay only adds: a model the built-in
//! catalog has (same provider and id) keeps its built-in entry, and the
//! overlay's copy is dropped. A listed model the catalog lacks is built from
//! its nearest sibling in the catalog (the provider's model whose id shares
//! the longest prefix with it): api, base URL, headers, compat, cost and
//! thinking map from the sibling; context window, output cap, reasoning
//! and input from the listing when it gives them, else the sibling's.

use std::collections::{BTreeMap, HashSet};

use eukhe_ai::capabilities::ListedModel;
use eukhe_types::ai::ModelInput;
use eukhe_types::pi_ai::Modality;
use serde::{Deserialize, Serialize};

use crate::Model;

/// The overlay document: when it was last refreshed (UTC ISO 8601) and,
/// per provider, the models its listing added.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RefreshOverlay {
    pub refreshed_at: String,
    pub providers: BTreeMap<String, Vec<Model>>,
}

/// What one provider's listing gives against the built-in catalog.
#[derive(Debug, Clone, PartialEq)]
pub struct ProviderListing {
    /// The chat models the catalog lacks, in listing order.
    pub added: Vec<Model>,
    /// How many listed chat models the catalog already has.
    pub known: usize,
}

/// Parts of an id that mark a model other than a chat model (embedding,
/// speech, image, moderation, search, realtime).
const NON_CHAT_MARKERS: [&str; 14] = [
    "embed",
    "whisper",
    "tts",
    "moderation",
    "transcribe",
    "speech",
    "image",
    "realtime",
    "audio",
    "dall-e",
    "rerank",
    "veo",
    "aqa",
    "search",
];

/// The id prefixes of the `openai` provider's chat models: its listing
/// also names fine-tunes, legacy completions and other kinds.
const OPENAI_CHAT_PREFIXES: [&str; 5] = ["gpt-", "o1", "o3", "o4", "chatgpt"];

/// Whether `listed` is a chat model of `provider`: not one the provider
/// marks as another kind, no non-chat marker in its id, and for `openai`
/// one of its chat prefixes.
fn is_chat_listing(provider: &str, listed: &ListedModel) -> bool {
    let id = listed.id.to_lowercase();
    listed.chat != Some(false)
        && !NON_CHAT_MARKERS.iter().any(|marker| id.contains(marker))
        && (provider != "openai"
            || OPENAI_CHAT_PREFIXES
                .iter()
                .any(|prefix| id.starts_with(prefix)))
}

/// The length of the common prefix of `left` and `right`, in chars.
fn common_prefix(left: &str, right: &str) -> usize {
    left.chars()
        .zip(right.chars())
        .take_while(|(a, b)| a == b)
        .count()
}

/// The sibling whose id shares the longest prefix with `id`; the first in
/// catalog order on a tie. `None` without siblings.
fn nearest_sibling<'a>(siblings: &[&'a Model], id: &str) -> Option<&'a Model> {
    siblings
        .iter()
        .copied()
        .rev()
        .max_by_key(|sibling| common_prefix(&sibling.id, id))
}

/// The catalog form of a listed modality.
fn model_input(modality: Modality) -> ModelInput {
    match modality {
        Modality::Text => ModelInput::Text,
        Modality::Image => ModelInput::Image,
    }
}

/// `listed` as a catalog model built from `template` (see the module docs).
#[must_use]
pub fn model_from_listing(template: &Model, listed: &ListedModel) -> Model {
    let reasoning = listed.reasoning.unwrap_or(template.reasoning);
    let context_window = listed.context_window.unwrap_or(template.context_window);
    Model {
        id: listed.id.clone(),
        name: listed.name.clone().unwrap_or_else(|| listed.id.clone()),
        reasoning,
        thinking_level_map: template
            .thinking_level_map
            .clone()
            .filter(|_| reasoning && template.reasoning),
        input: listed.input.as_ref().map_or_else(
            || template.input.clone(),
            |input| input.iter().copied().map(model_input).collect(),
        ),
        context_window,
        max_tokens: listed
            .max_output_tokens
            .unwrap_or(template.max_tokens)
            .min(context_window),
        max_tokens_explicit: false,
        featured: None,
        ..template.clone()
    }
}

/// `provider`'s `listed` models against the built-in catalog `pinned`:
/// the chat models it lacks, built from their nearest siblings, and the
/// count of those it has. `None` when the catalog has no model of
/// `provider` to build from.
#[must_use]
pub fn provider_listing(
    pinned: &[Model],
    provider: &str,
    listed: &[ListedModel],
) -> Option<ProviderListing> {
    let siblings: Vec<&Model> = pinned
        .iter()
        .filter(|model| model.provider == provider)
        .collect();
    if siblings.is_empty() {
        return None;
    }
    let known_ids: HashSet<&str> = siblings.iter().map(|model| model.id.as_str()).collect();
    let mut seen: HashSet<&str> = HashSet::new();
    let chat = listed
        .iter()
        .filter(|entry| is_chat_listing(provider, entry))
        .filter(|entry| seen.insert(entry.id.as_str()));
    let (known, new): (Vec<&ListedModel>, Vec<&ListedModel>) =
        chat.partition(|entry| known_ids.contains(entry.id.as_str()));
    let added = new
        .into_iter()
        .filter_map(|entry| {
            nearest_sibling(&siblings, &entry.id)
                .map(|template| model_from_listing(template, entry))
        })
        .collect();
    Some(ProviderListing {
        added,
        known: known.len(),
    })
}

/// `overlay` with `provider`'s added models replaced by `added` (an empty
/// list removes the provider) and the refresh date set.
#[must_use]
pub fn with_provider_listing(
    mut overlay: RefreshOverlay,
    provider: &str,
    added: Vec<Model>,
    refreshed_at: &str,
) -> RefreshOverlay {
    if added.is_empty() {
        overlay.providers.remove(provider);
    } else {
        overlay.providers.insert(provider.to_owned(), added);
    }
    refreshed_at.clone_into(&mut overlay.refreshed_at);
    overlay
}

/// The overlay's models the built-in catalog `pinned` lacks, each
/// provider and id once, in provider order then listing order.
#[must_use]
pub fn overlay_models(pinned: &[Model], overlay: &RefreshOverlay) -> Vec<Model> {
    let mut taken: HashSet<(&str, &str)> = pinned
        .iter()
        .map(|model| (model.provider.as_str(), model.id.as_str()))
        .collect();
    overlay
        .providers
        .values()
        .flatten()
        .filter(|model| taken.insert((model.provider.as_str(), model.id.as_str())))
        .cloned()
        .collect()
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    fn model(provider: &str, id: &str, extra: &serde_json::Value) -> Model {
        let mut value = json!({
            "id": id,
            "name": id,
            "api": "openai-codex-responses",
            "provider": provider,
            "baseUrl": "https://chatgpt.com/backend-api",
            "reasoning": true,
            "input": ["text", "image"],
            "cost": {"input": 5, "output": 30, "cacheRead": 0.5, "cacheWrite": 0},
            "contextWindow": 272_000,
            "maxTokens": 128_000,
            "thinkingLevelMap": {"minimal": "low"},
            "compat": {"supportsOpenAIGrammarTools": true},
        });
        if let (Some(target), Some(extra)) = (value.as_object_mut(), extra.as_object()) {
            target.extend(extra.clone());
        }
        serde_json::from_value(value).expect("a model")
    }

    fn listed(id: &str) -> ListedModel {
        ListedModel {
            id: id.to_owned(),
            ..ListedModel::default()
        }
    }

    #[test]
    fn a_new_id_is_built_from_its_nearest_sibling_with_the_listing_values() {
        let pinned = vec![
            model("openai-codex", "gpt-5.5", &json!({})),
            model(
                "openai-codex",
                "gpt-6-sol",
                &json!({"contextWindow": 400_000, "name": "GPT-6 Sol"}),
            ),
            model("anthropic", "gpt-6-sol-x", &json!({})),
        ];
        let listing = ListedModel {
            id: "gpt-6-sol-pro".to_owned(),
            name: Some("GPT-6 Sol Pro".to_owned()),
            context_window: Some(100_000),
            max_output_tokens: None,
            reasoning: Some(false),
            input: Some(vec![Modality::Text]),
            chat: Some(true),
        };
        let expected = model(
            "openai-codex",
            "gpt-6-sol-pro",
            &json!({
                "name": "GPT-6 Sol Pro",
                "reasoning": false,
                "input": ["text"],
                "contextWindow": 100_000,
                "maxTokens": 100_000,
            }),
        );
        let expected = Model {
            thinking_level_map: None,
            ..expected
        };
        assert_eq!(
            provider_listing(
                &pinned,
                "openai-codex",
                &[listed("gpt-5.5"), listing, listed("gpt-5.5")]
            ),
            Some(ProviderListing {
                added: vec![expected],
                known: 1,
            })
        );
    }

    #[test]
    fn a_listing_without_values_takes_the_siblings() {
        let template = model("openai-codex", "gpt-5.5", &json!({}));
        assert_eq!(
            model_from_listing(&template, &listed("gpt-5.5-mini")),
            model("openai-codex", "gpt-5.5-mini", &json!({}),)
        );
    }

    #[test]
    fn non_chat_listings_are_neither_added_nor_known() {
        let pinned = vec![model("openai", "gpt-5", &json!({}))];
        let entries = [
            listed("gpt-5"),
            listed("text-embedding-3-small"),
            listed("gpt-image-1"),
            listed("davinci-002"),
            listed("gpt-6"),
            ListedModel {
                chat: Some(false),
                ..listed("gpt-7")
            },
        ];
        let listing = provider_listing(&pinned, "openai", &entries).expect("a listing");
        assert_eq!(
            (
                listing
                    .added
                    .iter()
                    .map(|model| model.id.as_str())
                    .collect::<Vec<_>>(),
                listing.known
            ),
            (vec!["gpt-6"], 1)
        );
    }

    #[test]
    fn a_provider_without_catalog_models_has_no_listing() {
        assert_eq!(
            provider_listing(&[], "openai-codex", &[listed("gpt-6")]),
            None
        );
    }

    #[test]
    fn the_pinned_catalog_wins_and_the_overlay_adds() {
        let pinned = vec![model("openai-codex", "gpt-5.5", &json!({"name": "Pinned"}))];
        let overlay = RefreshOverlay {
            refreshed_at: "2026-11-14T10:00:00.000Z".to_owned(),
            providers: BTreeMap::from([
                (
                    "openai-codex".to_owned(),
                    vec![
                        model("openai-codex", "gpt-5.5", &json!({"name": "Overlay"})),
                        model("openai-codex", "gpt-6.2", &json!({})),
                        model("openai-codex", "gpt-6.2", &json!({"name": "Twice"})),
                    ],
                ),
                (
                    "anthropic".to_owned(),
                    vec![model("anthropic", "claude-x", &json!({}))],
                ),
            ]),
        };
        assert_eq!(
            overlay_models(&pinned, &overlay),
            vec![
                model("anthropic", "claude-x", &json!({})),
                model("openai-codex", "gpt-6.2", &json!({})),
            ]
        );
    }

    #[test]
    fn a_provider_listing_replaces_its_models_and_an_empty_one_removes_them() {
        let overlay = RefreshOverlay {
            refreshed_at: "old".to_owned(),
            providers: BTreeMap::from([
                (
                    "openai-codex".to_owned(),
                    vec![model("openai-codex", "gpt-6.1", &json!({}))],
                ),
                (
                    "anthropic".to_owned(),
                    vec![model("anthropic", "claude-x", &json!({}))],
                ),
            ]),
        };
        let replaced = with_provider_listing(
            overlay,
            "openai-codex",
            vec![model("openai-codex", "gpt-6.2", &json!({}))],
            "new",
        );
        let removed = with_provider_listing(replaced.clone(), "anthropic", Vec::new(), "newer");
        assert_eq!(
            (replaced, removed),
            (
                RefreshOverlay {
                    refreshed_at: "new".to_owned(),
                    providers: BTreeMap::from([
                        (
                            "openai-codex".to_owned(),
                            vec![model("openai-codex", "gpt-6.2", &json!({}))],
                        ),
                        (
                            "anthropic".to_owned(),
                            vec![model("anthropic", "claude-x", &json!({}))],
                        ),
                    ]),
                },
                RefreshOverlay {
                    refreshed_at: "newer".to_owned(),
                    providers: BTreeMap::from([(
                        "openai-codex".to_owned(),
                        vec![model("openai-codex", "gpt-6.2", &json!({}))],
                    )]),
                },
            )
        );
    }
}
