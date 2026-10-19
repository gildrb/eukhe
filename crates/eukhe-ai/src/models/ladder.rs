//! The thinking ladder of a model (docs/inference.md S10; model
//! `bend/infer.bend` section 6): the levels a model offers and their wire
//! values. Every ladder is data:
//!
//! 1. The chosen ladder is the model's explicit `thinkingLevelMap`; else,
//!    for a reasoning model of a custom provider (not a built-in one), the
//!    ladder that the quirks rulebook gives it (`thinking_ladder`, S6.1);
//!    else none. Built-in providers keep the ladders of their catalog.
//! 2. A reasoning model offers each level whose entry in the chosen ladder
//!    is a wire string, and each level that the chosen ladder does not name
//!    and the rulebook's default ladder (`thinking_defaults.reasoning`)
//!    lists. A `null` entry removes the level. A model without reasoning
//!    offers the levels of `thinking_defaults.plain`.
//! 3. A request sends a level's wire string from the chosen ladder; a level
//!    with no string goes out in the wire API's own form.
//!
//! The code holds no ladder and no wire value of a model.

use eukhe_types::daemon::CycleDirection;
use eukhe_types::pi_ai::{KnownProvider, Model, ModelThinkingLevel, ThinkingLevelMap};

use crate::quirks::{Quirks, Rulebook};

/// The levels in ladder order: the vocabulary, weakest first.
const LEVELS: [ModelThinkingLevel; 7] = [
    ModelThinkingLevel::Off,
    ModelThinkingLevel::Minimal,
    ModelThinkingLevel::Low,
    ModelThinkingLevel::Medium,
    ModelThinkingLevel::High,
    ModelThinkingLevel::Xhigh,
    ModelThinkingLevel::Max,
];

/// [`LEVELS`] in the registry's level type.
const REGISTRY_LEVELS: [eukhe_types::ai::ModelThinkingLevel; 7] = [
    eukhe_types::ai::ModelThinkingLevel::Off,
    eukhe_types::ai::ModelThinkingLevel::Minimal,
    eukhe_types::ai::ModelThinkingLevel::Low,
    eukhe_types::ai::ModelThinkingLevel::Medium,
    eukhe_types::ai::ModelThinkingLevel::High,
    eukhe_types::ai::ModelThinkingLevel::Xhigh,
    eukhe_types::ai::ModelThinkingLevel::Max,
];

/// The rungs (indexes into [`LEVELS`]) that a model offers (the module
/// docs, rule 2). `entry` gives the chosen ladder's entry of a rung:
/// `Some(true)` a wire string, `Some(false)` `null`, `None` no entry.
fn offered_rungs(reasoning: bool, entry: impl Fn(usize) -> Option<bool>) -> Vec<usize> {
    let defaults = Rulebook::shipped().thinking_defaults();
    (0..LEVELS.len())
        .filter(|&rung| {
            if reasoning {
                entry(rung).unwrap_or_else(|| defaults.reasoning.contains(&LEVELS[rung]))
            } else {
                defaults.plain.contains(&LEVELS[rung])
            }
        })
        .collect()
}

/// The offered rung closest to `rung`: `rung` itself, else the next
/// offered rung up the ladder, else the next one down; rung 0 (`off`)
/// when the model offers none.
fn clamp_rung(offered: &[usize], rung: usize) -> usize {
    (rung..LEVELS.len())
        .chain((0..rung).rev())
        .find(|candidate| offered.contains(candidate))
        .unwrap_or(0)
}

/// The rung of `level` in [`LEVELS`].
fn rung_of(level: ModelThinkingLevel) -> usize {
    LEVELS
        .iter()
        .position(|candidate| *candidate == level)
        .unwrap_or_default()
}

/// The rule ladder of a model (the module docs, rule 1): the rulebook's
/// ladder for a reasoning model of a custom provider.
fn rule_ladder<'a>(
    model: impl Into<crate::quirks::ModelKey<'a>>,
    provider: &str,
    reasoning: bool,
) -> Option<&'static ThinkingLevelMap> {
    if reasoning && KnownProvider::parse(provider).is_none() {
        Quirks::of(model).thinking_ladder()
    } else {
        None
    }
}

/// The chosen ladder that the requests of `model` use (the module docs,
/// rule 1): the explicit `thinkingLevelMap`, else the rulebook's ladder
/// for a reasoning model of a custom provider. `None`: every level goes
/// out in the wire API's own form.
#[must_use]
pub fn thinking_level_map(model: &Model) -> Option<&ThinkingLevelMap> {
    model
        .thinking_level_map
        .as_ref()
        .or_else(|| rule_ladder(model, &model.provider, model.reasoning))
}

/// The thinking levels `model` offers, in ladder order (the module docs,
/// rule 2).
#[must_use]
pub fn get_supported_thinking_levels(model: &Model) -> Vec<ModelThinkingLevel> {
    let ladder = thinking_level_map(model);
    offered_rungs(model.reasoning, |rung| {
        ladder
            .and_then(|ladder| ladder.get(&LEVELS[rung]))
            .map(Option::is_some)
    })
    .into_iter()
    .map(|rung| LEVELS[rung])
    .collect()
}

/// The offered level closest to `level`: the requested one, else the next
/// higher offered level, else the next lower one; `off` when the model
/// offers none.
#[must_use]
pub fn clamp_thinking_level(model: &Model, level: ModelThinkingLevel) -> ModelThinkingLevel {
    let offered: Vec<usize> = get_supported_thinking_levels(model)
        .into_iter()
        .map(rung_of)
        .collect();
    LEVELS[clamp_rung(&offered, rung_of(level))]
}

/// The level one cycle step moves to (TS `cycleThinkingLevel`): from the
/// level the model runs `current` at (its clamp), the next level of the
/// offered ladder `Forward` or the previous one `Backward`, wrapping at
/// the ends. `None` when the ladder offers fewer than two levels: no step
/// changes anything.
#[must_use]
pub fn cycle_thinking_level(
    model: &Model,
    current: ModelThinkingLevel,
    direction: CycleDirection,
) -> Option<ModelThinkingLevel> {
    let ladder = get_supported_thinking_levels(model);
    if ladder.len() < 2 {
        return None;
    }
    let shown = clamp_thinking_level(model, current);
    let index = ladder.iter().position(|level| *level == shown)?;
    let step = match direction {
        CycleDirection::Forward => 1,
        CycleDirection::Backward => ladder.len() - 1,
    };
    Some(ladder[(index + step) % ladder.len()])
}

/// The offered rungs of a registry model: [`get_supported_thinking_levels`]
/// over the registry's model type. The registry model reasons when its
/// flag is set or its map addresses a level (#2858, the flag that the
/// session's providers set: `eukhe-core` `compose`).
fn registry_rungs(model: &eukhe_types::ai::Model) -> Vec<usize> {
    let reasoning = model.reasoning
        || model
            .thinking_level_map
            .as_ref()
            .is_some_and(|map| map.values().any(Option::is_some));
    if let Some(map) = &model.thinking_level_map {
        return offered_rungs(reasoning, |rung| {
            map.get(&REGISTRY_LEVELS[rung]).map(Option::is_some)
        });
    }
    let ladder = rule_ladder(model, &model.provider, reasoning);
    offered_rungs(reasoning, |rung| {
        ladder
            .and_then(|ladder| ladder.get(&LEVELS[rung]))
            .map(Option::is_some)
    })
}

/// The thinking levels a registry model (`eukhe_types::ai::Model`)
/// offers, in ladder order: the rule of [`get_supported_thinking_levels`].
#[must_use]
pub fn registry_thinking_levels(
    model: &eukhe_types::ai::Model,
) -> Vec<eukhe_types::ai::ModelThinkingLevel> {
    registry_rungs(model)
        .into_iter()
        .map(|rung| REGISTRY_LEVELS[rung])
        .collect()
}

/// [`clamp_thinking_level`] over a registry model.
#[must_use]
pub fn registry_clamp_thinking_level(
    model: &eukhe_types::ai::Model,
    level: eukhe_types::ai::ModelThinkingLevel,
) -> eukhe_types::ai::ModelThinkingLevel {
    let rung = REGISTRY_LEVELS
        .iter()
        .position(|candidate| *candidate == level)
        .unwrap_or_default();
    REGISTRY_LEVELS[clamp_rung(&registry_rungs(model), rung)]
}

#[cfg(test)]
mod tests {
    use eukhe_types::pi_ai::{Model, ModelThinkingLevel};
    use serde_json::{json, Value};

    use super::{
        clamp_thinking_level, get_supported_thinking_levels, registry_clamp_thinking_level,
        registry_thinking_levels,
    };

    fn json_model(provider: &str, id: &str, reasoning: bool, map: Option<Value>) -> Value {
        let mut value = json!({
            "id": id, "name": id, "api": "openai-completions", "provider": provider,
            "baseUrl": "http://10.0.0.7:18020/v1", "reasoning": reasoning, "input": ["text"],
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
            "contextWindow": 128_000, "maxTokens": 4096,
        });
        if let Some(map) = map {
            value["thinkingLevelMap"] = map;
        }
        value
    }

    fn model(provider: &str, id: &str, reasoning: bool, map: Option<Value>) -> Model {
        serde_json::from_value(json_model(provider, id, reasoning, map)).unwrap()
    }

    /// The ladder of each source: the family rule of a custom provider
    /// (Qwen 3.8 and before 3.8), the default ladder (a built-in provider,
    /// no family), the plain default (no reasoning).
    #[test]
    fn a_model_offers_the_ladder_of_its_highest_source() {
        use ModelThinkingLevel::{High, Low, Medium, Minimal, Off, Xhigh};
        let models = [
            model("elpis-fast", "qwen3.8-27b", true, None),
            model("elpis-fast", "qwen3-32b", true, None),
            model("prime-inference", "qwen3.8-27b", true, None),
            model("elpis-fast", "llama-4", true, None),
            model("elpis-fast", "qwen3.8-27b", false, None),
            model(
                "elpis-fast",
                "qwen3.8-27b",
                true,
                Some(json!({ "high": null, "max": "max" })),
            ),
        ];
        assert_eq!(
            models.each_ref().map(get_supported_thinking_levels),
            [
                vec![Off, Low, Medium, Xhigh],
                vec![Off, High],
                vec![Off, Minimal, Low, Medium, High],
                vec![Off, Minimal, Low, Medium, High],
                vec![Off],
                vec![Off, Minimal, Low, Medium, ModelThinkingLevel::Max],
            ]
        );
        let elpis = &models[0];
        assert_eq!(
            [Minimal, High, ModelThinkingLevel::Max]
                .map(|level| clamp_thinking_level(elpis, level)),
            [Low, Xhigh, Xhigh]
        );
    }

    /// The registry model type reads the same sources; its map makes it
    /// reason even with the flag off (#2858).
    #[test]
    fn a_registry_model_offers_the_same_ladder() {
        use eukhe_types::ai::ModelThinkingLevel::{High, Low, Medium, Minimal, Off, Xhigh};
        let registry = |provider: &str, id: &str, reasoning: bool, map: Option<Value>| {
            serde_json::from_value::<eukhe_types::ai::Model>(json_model(
                provider, id, reasoning, map,
            ))
            .unwrap()
        };
        let elpis = registry("elpis-fast", "qwen3.8-27b", true, None);
        let addressed = registry(
            "openai",
            "gpt-5.3-chat-latest",
            false,
            Some(json!({ "xhigh": "xhigh" })),
        );
        assert_eq!(
            (
                registry_thinking_levels(&elpis),
                registry_thinking_levels(&addressed),
                registry_clamp_thinking_level(&elpis, High),
            ),
            (
                vec![Off, Low, Medium, Xhigh],
                vec![Off, Minimal, Low, Medium, High, Xhigh],
                Xhigh,
            )
        );
    }
}
