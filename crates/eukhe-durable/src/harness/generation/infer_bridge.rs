//! The bridges between the inference layer (docs/inference.md S6) and its
//! Bend model (`bend/infer.bend`, whose laws `PROOF.bend` proves): both
//! run the same scenarios and must print the same transcript, byte for
//! byte.
//!
//! - `bend/bridge_quirks.bend` documents the rulebook format: generated
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
//! - `bend/bridge_infer.bend` documents the other problems: the forced
//!   call ([`ForceEscalation`], model `force`), the strict budget
//!   ([`strict_budget`], model `strict`), the repetition guard
//!   ([`RepetitionGuard`], model `guard`: chunk id `x` is the line `c<x>`,
//!   fed in deltas cut at random points; the chunks are random, a cycle of
//!   1 to 4 chunks, the same with one chunk changed, or the observed
//!   thinking loop of [`OBSERVED_CYCLE`]), and early compaction
//!   ([`threshold_for`], model `first_at`). For compaction the limit is
//!   the blocking threshold `L = window - reserve` and the margin `m` a
//!   whole number of tokens; the code compares strictly (`tokens > L - m`,
//!   `tokens > L`), so for whole token counts the model's thresholds are
//!   `T = L - m + 1` and `L + 1`.
//!
//! [`compare`] runs them (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;

use eukhe_ai::api::constrained_sampling::strict_budget;
use eukhe_ai::capabilities::Dialect;
use eukhe_ai::quirks::{compile, Answer, Directive, Layer, Query, RawRule, ValueKind};
use eukhe_ai::utils::stream_repeat::RepetitionGuard;
use eukhe_types::pi_ai::{MaxTokensField, SessionAffinityFormat, ThinkingFormat};
use serde_json::{json, Value as JsonValue};

use super::decide::{threshold_for, Threshold};
use super::force::{ForceEscalation, ForceReply, ForceStep};
use crate::harness::types::{BackgroundMargin, CompactionPolicy, ThresholdTokens};
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
    compare("bend/bridge_quirks.bend", quirks_scenarios());
}

// The forced call, the strict budget, the guard, early compaction
// ----------------------------------------------------------------

fn bit(flag: bool) -> u8 {
    u8::from(flag)
}

fn force_problem(rng: &mut Rng, events: &mut String, transcript: &mut String) {
    let retries = u32::try_from(rng.below(4)).unwrap();
    let (native, free) = (rng.chance(50), rng.chance(50));
    let replies: Vec<bool> = (0..=u64::from(retries) + rng.below(2))
        .map(|_| rng.chance(30))
        .collect();
    write!(events, "f {retries} {} {}", bit(native), bit(free)).unwrap();
    for called in &replies {
        write!(events, " {}", bit(*called)).unwrap();
    }
    events.push('\n');
    let escalation = ForceEscalation {
        retries,
        native,
        free,
    };
    transcript.push('f');
    let mut attempt = 1;
    loop {
        write!(transcript, " {}", bit(escalation.flag(attempt))).unwrap();
        let reply = if replies[usize::try_from(attempt - 1).unwrap()] {
            ForceReply::Called
        } else {
            ForceReply::Missed
        };
        match escalation.after(attempt, reply) {
            ForceStep::Called => break transcript.push_str(" called\n"),
            ForceStep::Retry => attempt += 1,
            ForceStep::Failed => break transcript.push_str(" missed\n"),
        }
    }
}

fn strict_problem(rng: &mut Rng, events: &mut String, transcript: &mut String) {
    let cap = u32::try_from(rng.below(5)).unwrap();
    let priorities: Vec<u32> = (0..rng.below(7))
        .map(|_| u32::try_from(rng.below(3)).unwrap())
        .collect();
    write!(events, "s {cap}").unwrap();
    for priority in &priorities {
        write!(events, " {priority}").unwrap();
    }
    events.push('\n');
    transcript.push('s');
    for keep in strict_budget(&priorities, Some(cap)) {
        transcript.push_str(if keep { " 10" } else { " 01" });
    }
    transcript.push('\n');
}

/// The observed thinking loop (docs/inference.md S6.5) as chunk ids: 14
/// lines, then this cycle of 7 lines, in which no line comes twice in a row.
const OBSERVED_CYCLE: [u64; 7] = [9, 11, 14, 10, 11, 15, 13];

fn guard_problem(rng: &mut Rng, events: &mut String, transcript: &mut String) {
    let (k, chunks): (u64, Vec<u64>) = match rng.below(4) {
        0 => (
            rng.below(10),
            (0..rng.below(16)).map(|_| rng.below(3)).collect(),
        ),
        kind @ (1 | 2) => {
            let block: Vec<u64> = (0..rng.range(1, 4)).map(|_| rng.below(3)).collect();
            let mut chunks: Vec<u64> = (0..rng.below(4)).map(|_| rng.below(3)).collect();
            let repeated = usize::try_from(rng.range(1, 24)).unwrap();
            chunks.extend(block.iter().copied().cycle().take(repeated));
            if kind == 2 {
                // A near miss: one chunk of the cycle changed.
                let at = usize::try_from(rng.below(u64::try_from(chunks.len()).unwrap())).unwrap();
                chunks[at] = 3;
            }
            (rng.range(2, 16), chunks)
        }
        _ => {
            let length = usize::try_from(rng.range(40, 98)).unwrap();
            let chunks = (0..14)
                .chain(OBSERVED_CYCLE.iter().copied().cycle())
                .take(length)
                .collect();
            (rng.pick(&[27, 28, 32, 64]).unwrap(), chunks)
        }
    };
    let k = u32::try_from(k).unwrap();
    write!(events, "g {k}").unwrap();
    for chunk in &chunks {
        write!(events, " {chunk}").unwrap();
    }
    events.push('\n');
    let mut text = String::new();
    for chunk in &chunks {
        writeln!(text, "c{chunk}").unwrap();
    }
    let mut guard = RepetitionGuard::new(k);
    let mut cut = None;
    let mut rest = text.as_str();
    while cut.is_none() && !rest.is_empty() {
        let mut at = usize::try_from(rng.range(1, 4)).unwrap().min(rest.len());
        while !rest.is_char_boundary(at) {
            at += 1;
        }
        let (delta, after) = rest.split_at(at);
        cut = guard.push(0, delta);
        rest = after;
    }
    match cut {
        Some(cut) => writeln!(transcript, "g cut {}", cut.chunks).unwrap(),
        None => transcript.push_str("g whole\n"),
    }
}

fn first_problem(rng: &mut Rng, events: &mut String, transcript: &mut String) {
    let window = 100 * rng.range(1, 20);
    let reserve = rng.range(0, window / 4);
    let percent = rng.below(30);
    let policy = CompactionPolicy {
        enabled: true,
        reserve_tokens: f64::from(u32::try_from(reserve).unwrap()),
        keep_recent_tokens: 0.0,
        background: BackgroundMargin::WindowPercent(f64::from(u32::try_from(percent).unwrap())),
        token_count: ThresholdTokens::Estimate,
    };
    let limit = window - reserve;
    let margin = window * percent / 100;
    let mut size = 0;
    let sizes: Vec<u64> = (0..rng.range(1, 10))
        .map(|_| {
            size += rng.below(window / 5 + 1);
            size
        })
        .collect();
    write!(events, "t {} {limit}", limit - margin + 1).unwrap();
    for size in &sizes {
        write!(events, " {size}").unwrap();
    }
    events.push('\n');
    let thresholds: Vec<Option<Threshold>> = sizes
        .iter()
        .map(|&size| threshold_for(f64::from(u32::try_from(size).unwrap()), window, &policy))
        .collect();
    let first = |wanted: fn(Option<Threshold>) -> bool| {
        thresholds
            .iter()
            .position(|threshold| wanted(*threshold))
            .map_or_else(|| "none".to_owned(), |at| at.to_string())
    };
    writeln!(
        transcript,
        "t {} {}",
        first(|threshold| threshold.is_some()),
        first(|threshold| threshold == Some(Threshold::Blocking))
    )
    .unwrap();
}

fn infer_scenarios() -> Vec<Scenario> {
    let mut rng = Rng(0x5e6_0002);
    (0..60)
        .map(|at| {
            let (mut events, mut transcript) = (String::new(), String::new());
            for _ in 0..10 {
                force_problem(&mut rng, &mut events, &mut transcript);
                strict_problem(&mut rng, &mut events, &mut transcript);
                guard_problem(&mut rng, &mut events, &mut transcript);
                first_problem(&mut rng, &mut events, &mut transcript);
            }
            Scenario {
                name: format!("problems {at}"),
                events,
                transcript,
            }
        })
        .collect()
}

#[test]
fn the_rust_inference_units_equal_the_bend_model() {
    compare("bend/bridge_infer.bend", infer_scenarios());
}
