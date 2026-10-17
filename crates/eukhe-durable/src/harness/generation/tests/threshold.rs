//! `threshold_for`: which threshold compaction a context size is over
//! (spec §8.3; `bend/infer.bend` §5, law `compact_starts_early`).

use crate::harness::generation::decide::{threshold_for, Threshold};
use crate::harness::types::{BackgroundMargin, CompactionPolicy};

/// A 200k window less 16384 reserved: blocking above 183616; a tenth of
/// the window (20000) below it, background above 163616.
const WINDOW: u64 = 200_000;
const EARLY: CompactionPolicy = CompactionPolicy {
    enabled: true,
    reserve_tokens: 16384.0,
    keep_recent_tokens: 20000.0,
    background: BackgroundMargin::WindowPercent(10.0),
};

fn over(sizes: &[f64], window: u64, policy: &CompactionPolicy) -> Vec<Option<Threshold>> {
    sizes
        .iter()
        .map(|&tokens| threshold_for(tokens, window, policy))
        .collect()
}

#[test]
fn a_window_percent_margin_starts_background_strictly_above_its_threshold() {
    assert_eq!(
        over(
            &[0.0, 163_616.0, 163_617.0, 183_616.0, 183_617.0],
            WINDOW,
            &EARLY
        ),
        vec![
            None,
            None,
            Some(Threshold::Background),
            Some(Threshold::Background),
            Some(Threshold::Blocking),
        ]
    );
}

#[test]
fn a_token_margin_starts_background_that_many_tokens_below_blocking() {
    let policy = CompactionPolicy {
        background: BackgroundMargin::Tokens(32768.0),
        ..EARLY
    };
    assert_eq!(
        over(&[150_848.0, 150_849.0, 183_617.0], WINDOW, &policy),
        vec![None, Some(Threshold::Background), Some(Threshold::Blocking)]
    );
}

#[test]
fn a_zero_margin_only_blocks() {
    let sizes = [183_616.0, 183_617.0];
    let expected = vec![None, Some(Threshold::Blocking)];
    for background in [
        BackgroundMargin::Tokens(0.0),
        BackgroundMargin::WindowPercent(0.0),
    ] {
        let policy = CompactionPolicy {
            background,
            ..EARLY
        };
        assert_eq!(over(&sizes, WINDOW, &policy), expected);
    }
}

#[test]
fn a_disabled_policy_or_an_unknown_window_never_compacts() {
    let disabled = CompactionPolicy {
        enabled: false,
        ..EARLY
    };
    assert_eq!(over(&[183_617.0], WINDOW, &disabled), vec![None]);
    assert_eq!(over(&[183_617.0], 0, &EARLY), vec![None]);
}

/// Law `compact_starts_early`: when each turn grows the context by at most
/// the margin, the first turn over a threshold is over the background one,
/// before any turn over the blocking one.
#[test]
fn growth_within_the_margin_starts_background_before_blocking() {
    for step in [1_000.0, 7_919.0, 19_999.0, 20_000.0] {
        let first = (0_u32..)
            .map(|turn| f64::from(turn) * step)
            .find_map(|tokens| threshold_for(tokens, WINDOW, &EARLY));
        assert_eq!(first, Some(Threshold::Background), "step {step}");
    }
}

/// `keep_window`: the keep window is at most half the size where automatic
/// compaction starts, so a context just over that size always has history
/// before the kept tail; an unknown window leaves it as configured.
#[test]
fn the_keep_window_is_at_most_half_the_compaction_start() {
    let keeps = |policy: &CompactionPolicy, window: u64, expected: f64| {
        let keep = policy.keep_window(window);
        assert!((keep - expected).abs() < 1e-9, "window {window}: {keep}");
    };
    let huge = CompactionPolicy {
        keep_recent_tokens: 1_000_000.0,
        ..EARLY
    };
    // Background start 163616: half is 81808.
    keeps(&huge, WINDOW, 81_808.0);
    // A zero margin starts at blocking (183616).
    let blocking_only = CompactionPolicy {
        background: BackgroundMargin::Tokens(0.0),
        ..huge
    };
    keeps(&blocking_only, WINDOW, 91_808.0);
    // 32k window: 32768 - 16384 - 3276.8 = 13107.2 starts it.
    keeps(&huge, 32_768, 6_553.6);
    // A reserve larger than the window: nothing is kept.
    keeps(&huge, 8_000, 0.0);
    keeps(&EARLY, WINDOW, 20_000.0);
    keeps(&huge, 0, 1_000_000.0);
}
