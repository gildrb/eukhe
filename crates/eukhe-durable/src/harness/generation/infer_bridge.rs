//! The bridge between the quirks rulebook of the inference layer
//! (docs/inference.md S6) and its Bend model (`bend/infer.bend`, whose
//! laws `PROOF.bend` proves): both run the same scenarios and must print
//! the same transcript, byte for byte. The forced call, the repetition
//! guard and early compaction run as the compiled core
//! (`eukhe_bend::rules::infer_force`, `infer_guard`, `infer_threshold`): no
//! bridge.
//!
//! - `bridge/bridge_quirks.bend` documents the rulebook format: generated
//!   rules (layer, target, directive, value) and queries. The Rust side
//!   compiles them with [`eukhe_ai::quirks::compile`] and looks them up
//!   with `Rules::lookup`. Model directive `d` is the Rust directive
//!   `Directive::ALL[d]`; an id past the list is an unknown name
//!   (`unknown_<d>`), so the model's known list is `0 .. ALL.len()`. Value
//!   `v` (0 or 1) is the `v`-th value of the directive's type (`false`,
//!   `true`; the count `v`; the prefix list `["p<v>"]`; the `v`-th member
//!   of an enum; the thinking ladder whose `high` level has the wire value
//!   `w<v>`; for a capability endpoint `false`, then the first dialect
//!   that implements it). Target `t` is the id `t<t>` at its layer. Rules name
//!   targets 0 to 2; a query's family or host target 3 is no target
//!   (`None`: a model that no family or no host matches), which the model
//!   reads as a target no rule names. Each rulebook also runs with two
//!   adjacent rules swapped.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;

use eukhe_ai::capabilities::Dialect;
use eukhe_ai::quirks::{compile, Answer, Directive, Layer, Query, RawRule, ValueKind};
use eukhe_types::pi_ai::{MaxTokensField, SessionAffinityFormat, ThinkingFormat};
use serde_json::{json, Value as JsonValue};

use crate::testing::bridge::{compare, Rng, Scenario};

// The quirks rulebook
// -------------------

/// The target id a query's family or host uses for no target (`None`).
const NO_TARGET: u64 = 3;

/// The raw value `v` of model directive `d`.
fn raw_value(d: usize, v: usize) -> JsonValue {
    let Some(directive) = Directive::ALL.get(d) else {
        return json!(v);
    };
    match directive.kind() {
        ValueKind::Bool => json!(v == 1),
        ValueKind::Count => json!(v),
        ValueKind::Prefixes => json!([format!("p{v}")]),
        ValueKind::MaxTokensField => json!(MaxTokensField::ALL[v].as_str()),
        ValueKind::ThinkingFormat => json!(ThinkingFormat::ALL[v].as_str()),
        ValueKind::SessionAffinityFormat => json!(SessionAffinityFormat::ALL[v].as_str()),
        ValueKind::ThinkingLadder => json!({ "high": format!("w{v}") }),
        ValueKind::ThinkingBudgets => json!({ "minimal": v, "low": v, "medium": v, "high": v }),
        // 0 is `false` (no endpoint), 1 the first dialect with one.
        ValueKind::Endpoint(capability) => match v {
            0 => json!(false),
            _ => json!(Dialect::ALL
                .into_iter()
                .find(|dialect| dialect.endpoint(capability).is_some())
                .map(Dialect::as_str)),
        },
    }
}

fn directive_name(d: usize) -> String {
    Directive::ALL.get(d).map_or_else(
        || format!("unknown_{d}"),
        |directive| directive.as_str().to_owned(),
    )
}

const fn layer_of(l: u64) -> Layer {
    match l {
        0 => Layer::Family,
        1 => Layer::Model,
        _ => Layer::Host,
    }
}

/// One model rule: layer, target, directive, value.
type ModelRule = (u64, u64, usize, usize);

fn quirks_scenario(name: String, rules: &[ModelRule], queries: &[[u64; 4]]) -> Scenario {
    let mut events = format!("k {}\n", Directive::ALL.len());
    for &(layer, target, d, v) in rules {
        writeln!(events, "r {layer} {target} {d} {v}").unwrap();
    }
    events.push_str("c\n");
    let raw: Vec<RawRule> = rules
        .iter()
        .map(|&(layer, target, d, v)| RawRule {
            layer: layer_of(layer),
            target: format!("t{target}"),
            directive: directive_name(d),
            value: raw_value(d, v),
        })
        .collect();
    let mut transcript = String::new();
    match compile(&raw) {
        Err(_) => transcript.push_str("c 0\n"),
        Ok(compiled) => {
            transcript.push_str("c 1\n");
            for &[f, m, h, d] in queries {
                writeln!(events, "q {f} {m} {h} {d}").unwrap();
                let (family, model, host) = (format!("t{f}"), format!("t{m}"), format!("t{h}"));
                let query = Query {
                    family: (f != NO_TARGET).then_some(family.as_str()),
                    model: &model,
                    host: (h != NO_TARGET).then_some(host.as_str()),
                };
                let index = usize::try_from(d).unwrap();
                match compiled.lookup(&query, Directive::ALL[index]) {
                    Answer::Unknown => transcript.push_str("q u\n"),
                    Answer::Known(value) => {
                        let kind = Directive::ALL[index].kind();
                        let v = (0..2)
                            .find(|&v| kind.parse(&raw_value(index, v)).as_ref() == Some(value))
                            .unwrap();
                        writeln!(transcript, "q k {v}").unwrap();
                    }
                }
            }
        }
    }
    Scenario {
        name,
        events,
        transcript,
    }
}

fn quirks_scenarios() -> Vec<Scenario> {
    let mut rng = Rng(0x5e6_0001);
    let known = Directive::ALL.len() as u64;
    // The directives the generated rules use: the first of each value
    // type in `Directive::ALL`, so every parse is exercised.
    let mut kinds: Vec<ValueKind> = Vec::new();
    let directives: Vec<u64> = (0..known)
        .filter(|&d| {
            let kind = Directive::ALL[usize::try_from(d).unwrap()].kind();
            let first = !kinds.contains(&kind);
            kinds.push(kind);
            first
        })
        .collect();
    let mut scenarios = Vec::new();
    for at in 0..300 {
        let rules: Vec<ModelRule> = (0..rng.range(0, 7))
            .map(|_| {
                let d = if rng.chance(8) {
                    known + rng.below(2)
                } else {
                    rng.pick(&directives).unwrap()
                };
                (
                    rng.below(3),
                    rng.below(3),
                    usize::try_from(d).unwrap(),
                    usize::try_from(rng.below(2)).unwrap(),
                )
            })
            .collect();
        let queries: Vec<[u64; 4]> = (0..4)
            .map(|_| {
                [
                    rng.below(NO_TARGET + 1),
                    rng.below(3),
                    rng.below(NO_TARGET + 1),
                    rng.pick(&directives).unwrap(),
                ]
            })
            .collect();
        scenarios.push(quirks_scenario(format!("rulebook {at}"), &rules, &queries));
        if rules.len() >= 2 {
            let mut swapped = rules.clone();
            let i = usize::try_from(rng.below(rules.len() as u64 - 1)).unwrap();
            swapped.swap(i, i + 1);
            scenarios.push(quirks_scenario(
                format!("rulebook {at} with rules {i} and {} swapped", i + 1),
                &swapped,
                &queries,
            ));
        }
    }
    scenarios
}

#[test]
fn the_rust_quirks_rulebook_equals_the_bend_model() {
    compare("bridge/bridge_quirks.bend", quirks_scenarios());
}
