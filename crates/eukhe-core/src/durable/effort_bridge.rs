//! The bridge between the reasoning-depth rules of `eukhe-ai`
//! ([`get_supported_thinking_levels`], [`clamp_thinking_level`],
//! [`cycle_thinking_level`]) and their Bend models (`bend/infer.bend`
//! section 6, the ladder data; `bend/effort.bend`, the clamp and the
//! cycle; their laws `PROOF.bend` proves, sections S6 and S10 of
//! `docs/inference.md`): both run the same scenarios and must print the
//! same transcript, byte for byte.
//!
//! A scenario starts with the rulebook's default ladders and then lists
//! models, one a line (`bend/bridge_effort.bend` documents the format):
//! reasoning or not, no thinking-level map or a map whose entry for each
//! ladder level is missing, `null` or a wire string, and the rulebook's
//! ladder for the model when one applies (a Qwen family on a custom
//! provider; a built-in provider keeps its catalog ladder). The scenarios
//! hold the edge models (no reasoning, no map, an off-only ladder, an
//! empty ladder, one level, explicit xhigh and max, each rule ladder alone
//! and under an explicit map, a Qwen on a built-in provider) and random
//! ones. For each model the transcript prints the offered levels, the
//! clamp of each ladder level, and a forward and a backward cycle step
//! from each ladder level.
//!
//! [`compare`] runs them (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::collections::BTreeSet;
use std::fmt::Write as _;

use eukhe_ai::models::{clamp_thinking_level, cycle_thinking_level, get_supported_thinking_levels};
use eukhe_ai::quirks::{Quirks, Rulebook};
use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use eukhe_types::daemon::CycleDirection;
use eukhe_types::pi_ai::{Model, ModelThinkingLevel, ThinkingLevelMap};
use serde_json::Value;

/// The ladder, in order.
const LADDER: [ModelThinkingLevel; 7] = [
    ModelThinkingLevel::Off,
    ModelThinkingLevel::Minimal,
    ModelThinkingLevel::Low,
    ModelThinkingLevel::Medium,
    ModelThinkingLevel::High,
    ModelThinkingLevel::Xhigh,
    ModelThinkingLevel::Max,
];

/// A rule of the model the scenarios reach.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Case {
    /// A model without reasoning offers off only.
    NotReasoning,
    /// A reasoning model with no map.
    NoMap,
    /// A null entry drops its level.
    NullDropped,
    /// A wire entry below xhigh keeps its level.
    WireKept,
    /// A missing entry takes the default ladder, which lists the level.
    MissingKept,
    /// A missing entry takes the default ladder, which does not list the
    /// level.
    MissingDropped,
    /// A wire xhigh or max entry keeps its level.
    ExtWireKept,
    /// A reasoning model with no map takes the rulebook's ladder.
    RuleLadder,
    /// An explicit map wins over the rulebook's ladder.
    ExplicitOverRule,
    /// A Qwen on a built-in provider keeps the default ladder.
    BuiltInDefault,
    /// A reasoning model offers off only.
    OffOnly,
    /// A reasoning model offers no level.
    EmptyLadder,
    /// The clamp keeps an offered level.
    ClampKeeps,
    /// The clamp goes up the ladder.
    ClampUp,
    /// The clamp goes down the ladder.
    ClampDown,
    /// The clamp to no offered level is off.
    ClampEmpty,
    /// With fewer than two offered levels a step changes nothing.
    CycleStill,
    /// A step to the neighbouring offered level.
    CycleStep,
    /// A forward step from the last offered level to the first.
    CycleWrapForward,
    /// A backward step from the first offered level to the last.
    CycleWrapBackward,
    /// A step from a level the model does not offer (from its clamp).
    CycleFromClamp,
}

/// The rules the scenarios reached.
type Reached = BTreeSet<Case>;

/// An entry of a thinking-level map.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Entry {
    Missing,
    Null,
    Wire,
}

impl Entry {
    fn token(self) -> char {
        match self {
            Self::Missing => '-',
            Self::Null => 'n',
            Self::Wire => 'w',
        }
    }
}

/// The family of a scenario model: none (`bridge`), a Qwen before 3.8
/// (`qwen3-32b`), a Qwen 3.8 (`qwen3.8-27b`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Family {
    None,
    Qwen,
    Qwen38,
}

/// The provider of a scenario model: a custom one, or a built-in one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Host {
    Custom,
    BuiltIn,
}

/// A model of the scenarios.
#[derive(Clone, Copy, Debug)]
struct Spec {
    reasoning: bool,
    /// The entry of each ladder level; `None`: the model has no map.
    map: Option<[Entry; 7]>,
    family: Family,
    host: Host,
}

/// The entries of a ladder, in ladder order.
fn entries(ladder: &ThinkingLevelMap) -> [Entry; 7] {
    LADDER.map(|level| match ladder.get(&level) {
        None => Entry::Missing,
        Some(None) => Entry::Null,
        Some(Some(_)) => Entry::Wire,
    })
}

/// The scenario line of the rulebook's default ladders: `d`, then for each
/// ladder level `1` when the reasoning default lists it, else `0`, then
/// the same for the plain default.
fn defaults_line() -> String {
    let defaults = Rulebook::shipped().thinking_defaults();
    let mut line = "d".to_owned();
    for list in [&defaults.reasoning, &defaults.plain] {
        for level in LADDER {
            write!(line, " {}", u8::from(list.contains(&level))).unwrap();
        }
    }
    line
}

impl Spec {
    /// A model of no family on a built-in provider.
    const fn plain(reasoning: bool, map: Option<[Entry; 7]>) -> Self {
        Self {
            reasoning,
            map,
            family: Family::None,
            host: Host::BuiltIn,
        }
    }

    /// The edge models: no reasoning, no map, an off-only ladder, an
    /// empty ladder, one level, explicit xhigh and max; each rule ladder
    /// alone and under an explicit map; a Qwen on a built-in provider.
    fn edges() -> Vec<Self> {
        use Entry::{Missing, Null, Wire};
        let rule = |family, map| Self {
            reasoning: true,
            map,
            family,
            host: Host::Custom,
        };
        vec![
            Self::plain(false, None),
            Self::plain(false, Some([Null; 7])),
            Self::plain(true, None),
            Self::plain(true, Some([Wire, Null, Null, Null, Null, Null, Null])),
            Self::plain(true, Some([Null; 7])),
            Self::plain(
                true,
                Some([Missing, Missing, Missing, Missing, Missing, Wire, Wire]),
            ),
            Self::plain(true, Some([Null, Null, Null, Null, Wire, Null, Null])),
            Self::plain(true, Some([Null, Null, Wire, Wire, Wire, Wire, Wire])),
            rule(Family::Qwen, None),
            rule(Family::Qwen38, None),
            rule(
                Family::Qwen38,
                Some([Missing, Missing, Null, Missing, Wire, Missing, Missing]),
            ),
            Self {
                reasoning: true,
                map: None,
                family: Family::Qwen38,
                host: Host::BuiltIn,
            },
        ]
    }

    /// A random model: mostly reasoning; no map, an all-null map, an
    /// off-only map, a one-level map, or random entries; any family on
    /// any provider.
    fn random(rng: &mut Rng) -> Self {
        let any = [Entry::Missing, Entry::Null, Entry::Wire];
        let map = match rng.below(10) {
            0 | 1 => None,
            2 => Some([Entry::Null; 7]),
            3 => {
                let mut entries = [Entry::Null; 7];
                entries[0] = rng.pick(&[Entry::Missing, Entry::Wire]).unwrap();
                Some(entries)
            }
            4 => {
                let mut entries = [Entry::Null; 7];
                entries[usize::try_from(rng.below(7)).unwrap()] = Entry::Wire;
                Some(entries)
            }
            _ => Some(std::array::from_fn(|_| rng.pick(&any).unwrap())),
        };
        Self {
            reasoning: rng.chance(85),
            map,
            family: rng
                .pick(&[Family::None, Family::Qwen, Family::Qwen38])
                .unwrap(),
            host: rng.pick(&[Host::Custom, Host::BuiltIn]).unwrap(),
        }
    }

    /// The rulebook's ladder for the model: a Qwen family on a custom
    /// provider; a built-in provider keeps its catalog ladder.
    fn rule(self) -> Option<[Entry; 7]> {
        match (self.family, self.host) {
            (Family::None | Family::Qwen | Family::Qwen38, Host::BuiltIn)
            | (Family::None, Host::Custom) => None,
            (Family::Qwen | Family::Qwen38, Host::Custom) => Some(entries(
                Quirks::of(&self.model())
                    .thinking_ladder()
                    .expect("the rulebook has a ladder for the Qwen families"),
            )),
        }
    }

    /// The model's scenario line.
    fn line(self) -> String {
        let mut line = format!(
            "{} {}",
            u8::from(self.reasoning),
            u8::from(self.map.is_some())
        );
        for entry in self.map.unwrap_or([Entry::Missing; 7]) {
            write!(line, " {}", entry.token()).unwrap();
        }
        let rule = self.rule();
        write!(line, " {}", u8::from(rule.is_some())).unwrap();
        for entry in rule.unwrap_or([Entry::Missing; 7]) {
            write!(line, " {}", entry.token()).unwrap();
        }
        line
    }

    /// The model as the catalog holds it.
    fn model(self) -> Model {
        let id = match self.family {
            Family::None => "bridge",
            Family::Qwen => "qwen3-32b",
            Family::Qwen38 => "qwen3.8-27b",
        };
        let provider = match self.host {
            Host::Custom => "bridge-host",
            Host::BuiltIn => "prime-inference",
        };
        let mut json = serde_json::json!({
            "id": id, "name": "Bridge", "api": "openai-completions",
            "provider": provider, "baseUrl": "https://example.invalid/v1",
            "reasoning": self.reasoning, "input": ["text"],
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
            "contextWindow": 128_000, "maxTokens": 4096,
        });
        if let Some(entries) = self.map {
            let map: serde_json::Map<String, Value> = LADDER
                .iter()
                .zip(entries)
                .filter_map(|(level, entry)| match entry {
                    Entry::Missing => None,
                    Entry::Null => Some((level.as_str().to_string(), Value::Null)),
                    Entry::Wire => Some((
                        level.as_str().to_string(),
                        Value::String(format!("wire-{level}")),
                    )),
                })
                .collect();
            json["thinkingLevelMap"] = Value::Object(map);
        }
        serde_json::from_value(json).unwrap()
    }

    /// Note the rules of the offered levels that the model reaches.
    fn note(self, offered: &[ModelThinkingLevel], reached: &mut Reached) {
        if !self.reasoning {
            reached.insert(Case::NotReasoning);
            return;
        }
        if offered.is_empty() {
            reached.insert(Case::EmptyLadder);
        } else if offered == [ModelThinkingLevel::Off] {
            reached.insert(Case::OffOnly);
        }
        let rule = self.rule();
        match (self.map, rule) {
            (Some(_), Some(_)) => {
                reached.insert(Case::ExplicitOverRule);
            }
            (None, Some(_)) => {
                reached.insert(Case::RuleLadder);
            }
            (None, None) => {
                reached.insert(match self.family {
                    Family::None => Case::NoMap,
                    Family::Qwen | Family::Qwen38 => Case::BuiltInDefault,
                });
            }
            (Some(_), None) => {}
        }
        let defaults = &Rulebook::shipped().thinking_defaults().reasoning;
        let chosen = self.map.or(rule).unwrap_or([Entry::Missing; 7]);
        for (level, entry) in LADDER.iter().zip(chosen) {
            let ext = matches!(level, ModelThinkingLevel::Xhigh | ModelThinkingLevel::Max);
            reached.insert(match (entry, ext) {
                (Entry::Null, _) => Case::NullDropped,
                (Entry::Wire, false) => Case::WireKept,
                (Entry::Wire, true) => Case::ExtWireKept,
                (Entry::Missing, _) if defaults.contains(level) => Case::MissingKept,
                (Entry::Missing, _) => Case::MissingDropped,
            });
        }
    }
}

/// The index of `level` on the ladder.
fn rung(level: ModelThinkingLevel) -> usize {
    LADDER
        .iter()
        .position(|candidate| *candidate == level)
        .unwrap()
}

/// One scenario's models as they run on the Rust code: their lines, for
/// the model, and the transcript the Rust code printed.
fn run(name: String, specs: &[Spec], reached: &mut Reached) -> Scenario {
    let mut events = defaults_line();
    events.push('\n');
    let mut transcript = String::new();
    for spec in specs {
        events.push_str(&spec.line());
        events.push('\n');
        let model = spec.model();
        let offered = get_supported_thinking_levels(&model);
        spec.note(&offered, reached);
        transcript.push_str("offered");
        for level in &offered {
            write!(transcript, " {level}").unwrap();
        }
        transcript.push_str("\nclamp");
        for level in LADDER {
            let clamped = clamp_thinking_level(&model, level);
            reached.insert(if offered.is_empty() {
                Case::ClampEmpty
            } else if offered.contains(&level) {
                Case::ClampKeeps
            } else if rung(clamped) > rung(level) {
                Case::ClampUp
            } else {
                Case::ClampDown
            });
            write!(transcript, " {clamped}").unwrap();
        }
        for (row, direction) in [
            ("forward", CycleDirection::Forward),
            ("backward", CycleDirection::Backward),
        ] {
            write!(transcript, "\n{row}").unwrap();
            for level in LADDER {
                let Some(stepped) = cycle_thinking_level(&model, level, direction) else {
                    reached.insert(Case::CycleStill);
                    transcript.push_str(" -");
                    continue;
                };
                if !offered.contains(&level) {
                    reached.insert(Case::CycleFromClamp);
                }
                let from = rung(clamp_thinking_level(&model, level));
                reached.insert(match direction {
                    CycleDirection::Forward if rung(stepped) < from => Case::CycleWrapForward,
                    CycleDirection::Backward if rung(stepped) > from => Case::CycleWrapBackward,
                    CycleDirection::Forward | CycleDirection::Backward => Case::CycleStep,
                });
                write!(transcript, " {stepped}").unwrap();
            }
        }
        transcript.push('\n');
    }
    Scenario {
        name,
        events,
        transcript,
    }
}

#[test]
fn the_rust_reasoning_depth_equals_the_bend_model() {
    let mut reached = Reached::new();
    let mut rng = Rng(0x5eed_e4f0_47c1_ba5e);
    let mut plans = vec![Spec::edges()];
    plans.extend((0..60).map(|_| (0..8).map(|_| Spec::random(&mut rng)).collect()));
    let scenarios: Vec<Scenario> = plans
        .iter()
        .enumerate()
        .map(|(at, specs)| run(format!("models {at}"), specs, &mut reached))
        .collect();
    compare("bend/bridge_effort.bend", scenarios);
    // The scenarios reach every rule of the model.
    assert_eq!(
        reached,
        Reached::from([
            Case::NotReasoning,
            Case::NoMap,
            Case::NullDropped,
            Case::WireKept,
            Case::MissingKept,
            Case::MissingDropped,
            Case::ExtWireKept,
            Case::RuleLadder,
            Case::ExplicitOverRule,
            Case::BuiltInDefault,
            Case::OffOnly,
            Case::EmptyLadder,
            Case::ClampKeeps,
            Case::ClampUp,
            Case::ClampDown,
            Case::ClampEmpty,
            Case::CycleStill,
            Case::CycleStep,
            Case::CycleWrapForward,
            Case::CycleWrapBackward,
            Case::CycleFromClamp,
        ])
    );
}
