//! The thinking ladder of a model (docs/inference.md S10; model
//! `bend/infer.bend` section 6 and `bend/effort.bend`): the levels a model
//! offers and their wire values. Every ladder is data:
//!
//! 1. The chosen ladder is the model's explicit `thinkingLevelMap`; else,
//!    for a reasoning model of a custom provider (not a built-in one), the
//!    ladder that the quirks rulebook gives it (`thinking_ladder`, S6.1);
//!    else none. Built-in providers keep the ladders of their catalog.
//! 2. A reasoning model offers each level whose entry in the chosen ladder
//!    is a wire string, and each level that the chosen ladder does not name
//!    and the rulebook's default ladder (`thinking_defaults.reasoning`)
//!    lists. A `null` entry removes the level. A model without reasoning
//!    offers the levels of `thinking_defaults.plain`. A registry model also
//!    reasons when its explicit map gives a level a wire string (#2858).
//! 3. A request sends a level's wire string from the chosen ladder; a level
//!    with no string goes out in the wire API's own form.
//!
//! The rule of 2 and the S10 clamp and cycle over the offered levels are
//! one pure function of [`LadderFacts`] ([`offered`], [`clamp`],
//! [`cycle`]); this module only projects a model onto those facts. The
//! code holds no ladder and no wire value of a model.

use eukhe_types::daemon::CycleDirection;
use eukhe_types::pi_ai::{KnownProvider, Model, ModelThinkingLevel, ThinkingLevelMap};

use eukhe_bend::wire::{Reader, WireError, Writer};
use eukhe_bend::Entry;

use crate::quirks::{Quirks, Rulebook};

/// The levels in ladder order: the vocabulary, weakest first. A level's
/// index here is its rung.
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

/// The rung of `level` in [`LEVELS`].
const fn rung(level: ModelThinkingLevel) -> usize {
    match level {
        ModelThinkingLevel::Off => 0,
        ModelThinkingLevel::Minimal => 1,
        ModelThinkingLevel::Low => 2,
        ModelThinkingLevel::Medium => 3,
        ModelThinkingLevel::High => 4,
        ModelThinkingLevel::Xhigh => 5,
        ModelThinkingLevel::Max => 6,
    }
}

/// The rung of a registry `level` in [`REGISTRY_LEVELS`].
const fn registry_rung(level: eukhe_types::ai::ModelThinkingLevel) -> usize {
    match level {
        eukhe_types::ai::ModelThinkingLevel::Off => 0,
        eukhe_types::ai::ModelThinkingLevel::Minimal => 1,
        eukhe_types::ai::ModelThinkingLevel::Low => 2,
        eukhe_types::ai::ModelThinkingLevel::Medium => 3,
        eukhe_types::ai::ModelThinkingLevel::High => 4,
        eukhe_types::ai::ModelThinkingLevel::Xhigh => 5,
        eukhe_types::ai::ModelThinkingLevel::Max => 6,
    }
}

/// The entry of one level in a ladder map (model `Ef.Ent`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MapEntry {
    /// The map names no entry for the level.
    Missing,
    /// The entry is `null`: the model does not take the level.
    Null,
    /// The entry is a wire string.
    Wire,
}

impl MapEntry {
    /// The entry of a map lookup: `None` no entry, `Some(None)` `null`.
    const fn of<T>(entry: Option<&Option<T>>) -> Self {
        match entry {
            None => Self::Missing,
            Some(None) => Self::Null,
            Some(Some(_)) => Self::Wire,
        }
    }

    /// The entry's tag on the wire (`bend/ffi_effort.bend`).
    const fn tag(self) -> u32 {
        match self {
            Self::Missing => 0,
            Self::Null => 1,
            Self::Wire => 2,
        }
    }
}

/// Whether a model reasons (model `If.lad.reasons`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Reasons {
    /// The model's reasoning flag alone.
    ByFlag(bool),
    /// The flag, or an explicit map that gives a level a wire string
    /// (registry models, #2858).
    ByFlagOrMap(bool),
}

/// Everything the ladder rule reads of a model (model `If.lad.model`):
/// whether it reasons, its explicit map and the rulebook's ladder for it
/// (each entry projected to [`MapEntry`]), and the rulebook's default
/// ladders as rungs.
#[derive(Debug, Clone, PartialEq, Eq)]
struct LadderFacts {
    reasons: Reasons,
    explicit: Option<[MapEntry; 7]>,
    rule: Option<[MapEntry; 7]>,
    defaults_reasoning: Vec<usize>,
    defaults_plain: Vec<usize>,
}

impl LadderFacts {
    fn new(reasons: Reasons, explicit: Option<[MapEntry; 7]>, rule: Option<[MapEntry; 7]>) -> Self {
        let defaults = Rulebook::shipped().thinking_defaults();
        let rungs = |levels: &[ModelThinkingLevel]| levels.iter().copied().map(rung).collect();
        Self {
            reasons,
            explicit,
            rule,
            defaults_reasoning: rungs(&defaults.reasoning),
            defaults_plain: rungs(&defaults.plain),
        }
    }

    /// The facts on the wire (`bend/ffi_effort.bend` `Facts`).
    fn write(&self, writer: &mut Writer) {
        let (flag, by_map) = match self.reasons {
            Reasons::ByFlag(flag) => (flag, false),
            Reasons::ByFlagOrMap(flag) => (flag, true),
        };
        writer.bool(flag).bool(by_map);
        for map in [&self.explicit, &self.rule] {
            match map {
                None => {
                    writer.none();
                }
                Some(entries) => {
                    writer.some();
                    for entry in entries {
                        writer.tag(entry.tag());
                    }
                }
            }
        }
        for rungs in [&self.defaults_reasoning, &self.defaults_plain] {
            writer.count(rungs.len());
            for rung in rungs {
                writer.count(*rung);
            }
        }
    }
}

/// One call of the compiled ladder rule (`bend/ffi_effort.bend`): the
/// request `tag` with the facts and `write`'s fields, the reply by `read`.
fn ladder_call<T>(
    tag: u32,
    facts: &LadderFacts,
    write: impl FnOnce(&mut Writer),
    read: impl FnOnce(&mut Reader<'_>) -> Result<T, WireError>,
) -> T {
    let answer = || -> Result<T, eukhe_bend::Error> {
        let mut writer = Writer::new();
        writer.tag(tag);
        facts.write(&mut writer);
        write(&mut writer);
        let reply = eukhe_bend::call(Entry::Effort, &writer.finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let value = read(&mut reader)?;
        reader.end()?;
        Ok(value)
    };
    eukhe_bend::expect_core(Entry::Effort, answer())
}

/// A rung on the wire.
fn read_rung(reader: &mut Reader<'_>) -> Result<usize, WireError> {
    reader.tag_of(7, "a ladder level").map(|tag| tag as usize)
}

/// The rungs a model offers, in ladder order (the module docs, rule 2;
/// LAWS.bend `quirk_ladder_offered_exact`, `quirk_ladder_plain_exact`,
/// `quirk_ladder_reasons`).
fn offered(facts: &LadderFacts) -> Vec<usize> {
    ladder_call(
        0,
        facts,
        |_| {},
        |reader| (0..reader.count()?).map(|_| read_rung(reader)).collect(),
    )
}

/// The offered rung closest to `rung`: `rung` itself, else the next
/// offered rung up the ladder, else the next one down; rung 0 (`off`)
/// when the model offers none (LAWS.bend S10 `effort_clamp_*`).
fn clamp(facts: &LadderFacts, rung: usize) -> usize {
    ladder_call(
        1,
        facts,
        |writer| {
            writer.count(rung);
        },
        read_rung,
    )
}

/// The rung one cycle step moves to (TS `cycleThinkingLevel`): from the
/// clamp of `rung`, the next offered rung `Forward` or the previous one
/// `Backward`, wrapping at the ends; `None` when fewer than two rungs are
/// offered (LAWS.bend S10 `effort_cycle_*`).
fn cycle(facts: &LadderFacts, rung: usize, direction: CycleDirection) -> Option<usize> {
    ladder_call(
        2,
        facts,
        |writer| {
            writer.count(rung).tag(match direction {
                CycleDirection::Forward => 0,
                CycleDirection::Backward => 1,
            });
        },
        |reader| {
            if reader.maybe()? {
                read_rung(reader).map(Some)
            } else {
                Ok(None)
            }
        },
    )
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

/// The entries of a pi-ai ladder map, by rung.
fn entries(map: &ThinkingLevelMap) -> [MapEntry; 7] {
    LEVELS.map(|level| MapEntry::of(map.get(&level)))
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

/// The ladder facts of a pi-ai model.
fn facts(model: &Model) -> LadderFacts {
    LadderFacts::new(
        Reasons::ByFlag(model.reasoning),
        model.thinking_level_map.as_ref().map(entries),
        rule_ladder(model, &model.provider, model.reasoning).map(entries),
    )
}

/// The ladder facts of a registry model. Its rule ladder is read with the
/// flag alone: an explicit map, the only other source of reasoning, wins
/// over the rule ladder anyway.
fn registry_facts(model: &eukhe_types::ai::Model) -> LadderFacts {
    LadderFacts::new(
        Reasons::ByFlagOrMap(model.reasoning),
        model
            .thinking_level_map
            .as_ref()
            .map(|map| REGISTRY_LEVELS.map(|level| MapEntry::of(map.get(&level)))),
        rule_ladder(model, &model.provider, model.reasoning).map(entries),
    )
}

/// The thinking levels `model` offers, in ladder order (the module docs,
/// rule 2).
#[must_use]
pub fn get_supported_thinking_levels(model: &Model) -> Vec<ModelThinkingLevel> {
    offered(&facts(model))
        .into_iter()
        .map(|rung| LEVELS[rung])
        .collect()
}

/// The offered level closest to `level`: the requested one, else the next
/// higher offered level, else the next lower one; `off` when the model
/// offers none.
#[must_use]
pub fn clamp_thinking_level(model: &Model, level: ModelThinkingLevel) -> ModelThinkingLevel {
    LEVELS[clamp(&facts(model), rung(level))]
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
    cycle(&facts(model), rung(current), direction).map(|rung| LEVELS[rung])
}

/// The thinking levels a registry model (`eukhe_types::ai::Model`)
/// offers, in ladder order: the rule of [`get_supported_thinking_levels`].
#[must_use]
pub fn registry_thinking_levels(
    model: &eukhe_types::ai::Model,
) -> Vec<eukhe_types::ai::ModelThinkingLevel> {
    offered(&registry_facts(model))
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
    REGISTRY_LEVELS[clamp(&registry_facts(model), registry_rung(level))]
}

/// The quirks rulebook's thinking ladder of a registry model (the rule of
/// its host, model id or family), in the registry's level type. Unlike
/// the chosen ladder (the module docs, rule 1), it does not look at the
/// provider or the reasoning flag: the caller decides where it applies.
/// `None`: no rule gives a ladder.
#[must_use]
pub fn registry_rule_ladder(
    model: &eukhe_types::ai::Model,
) -> Option<eukhe_types::ai::ThinkingLevelMap> {
    Quirks::of(model).thinking_ladder().map(|ladder| {
        ladder
            .iter()
            .map(|(level, value)| (REGISTRY_LEVELS[rung(*level)], value.clone()))
            .collect()
    })
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
