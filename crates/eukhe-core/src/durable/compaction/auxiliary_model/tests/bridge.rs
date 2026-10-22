//! The bridge between the auxiliary-model decision and notices
//! ([`decide_auxiliary_route`], [`AuxiliaryNotices::take`]) and their Bend
//! model (`bend/aux_fallback.bend`, whose laws `PROOF.bend` proves): both
//! run the same sessions of summarizer passes and must print the same
//! events, byte for byte. `bend/bridge_aux_fallback.bend` documents the
//! scenario format.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;

use eukhe_durable::testing::bridge::{compare, Rng, Scenario};

use super::super::{
    decide_auxiliary_route, AuxiliaryNotices, AuxiliaryRoute, AuxiliarySelector, FallbackReason,
    Found,
};

/// The reasons the resolvers' own lookups give, with their model codes.
const LOOKUP_REASONS: [(FallbackReason, u64); 4] = [
    (FallbackReason::ModelListFailed, 1),
    (FallbackReason::NotFound, 2),
    (FallbackReason::NoKey, 3),
    (FallbackReason::NotInSession, 4),
];

/// One session: its passes, for the model, and what the Rust code printed.
fn scenario(seed: u64, passes: usize) -> (String, String) {
    let mut rng = Rng(seed);
    let mut events = String::new();
    let mut transcript = String::new();
    let notices = AuxiliaryNotices::default();
    for _ in 0..passes {
        let purpose = rng.below(2);
        let shape = rng.below(6);
        let selector = rng.below(3);
        let admitted = rng.chance(80);
        let hit = rng.chance(60);
        let reason = rng.pick(&LOOKUP_REASONS).unwrap();
        let window = rng.pick(&[0, 4, 8, 16]).unwrap();
        let need = rng.pick(&[0, 3, 8, 12, 20]).unwrap();
        // The setting: unset (or blank), the session model (any case), or
        // another model.
        let (sel, setting) = match shape {
            0 => (0, None),
            1 => (0, Some("  ".to_owned())),
            2 => (1, Some("Faux/Session".to_owned())),
            _ => (2, Some(format!("p/m{selector}"))),
        };
        let look = if hit { (1, window) } else { (0, reason.1) };
        writeln!(
            events,
            "{purpose} {sel} {selector} {} {} {} {need}",
            u8::from(admitted),
            look.0,
            look.1
        )
        .unwrap();
        let allowlist = if admitted {
            vec![format!("p/m{selector}"), "faux/session".to_owned()]
        } else {
            vec!["faux/session".to_owned()]
        };
        let route = decide_auxiliary_route(
            &AuxiliarySelector::of(setting.as_deref(), "faux", "session"),
            Some(&allowlist),
            (need > 0).then_some(need),
            |_| {
                if hit {
                    Ok(Found {
                        model: (),
                        context_window: window,
                    })
                } else {
                    Err(reason.0)
                }
            },
        );
        let purpose_name = ["compaction summary", "branch summary"][usize::from(purpose == 1)];
        let notice = notices.take(purpose_name, &route, "faux/session");
        match &route {
            AuxiliaryRoute::Session => transcript.push_str("S\n"),
            AuxiliaryRoute::Routed(()) => transcript.push_str("R\n"),
            AuxiliaryRoute::Fallback { selector, reason } => {
                let id = selector.trim_start_matches("p/m");
                let reason = match reason {
                    FallbackReason::NotAllowed => 0,
                    FallbackReason::ModelListFailed => 1,
                    FallbackReason::NotFound => 2,
                    FallbackReason::NoKey => 3,
                    FallbackReason::NotInSession => 4,
                    FallbackReason::WindowTooSmall => 5,
                };
                writeln!(transcript, "F {purpose} {id} {reason}").unwrap();
                if notice.is_some() {
                    writeln!(transcript, "N {purpose} {id} {reason}").unwrap();
                }
            }
        }
    }
    (events, transcript)
}

#[test]
fn the_rust_fallback_notices_equal_the_bend_model() {
    let scenarios = (1..=40).map(|seed| {
        let (events, transcript) = scenario(seed, 60);
        Scenario {
            name: seed.to_string(),
            events,
            transcript,
        }
    });
    compare("bend/bridge_aux_fallback.bend", scenarios);
}
