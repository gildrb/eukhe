//! `threshold_for`: the policy as the compiled core reads it (the
//! decision itself is pinned by `laws/infer_threshold.bend`), and the keep
//! window.

use crate::harness::generation::decide::{threshold_for, Threshold};
use crate::harness::types::{BackgroundMargin, CompactionPolicy, ThresholdTokens};

/// A 200k window less 16384 reserved: blocking above 183616; a tenth of
/// the window (20000) below it, background above 163616.
const WINDOW: u64 = 200_000;
const EARLY: CompactionPolicy = CompactionPolicy {
    enabled: true,
    reserve_tokens: 16384.0,
    keep_recent_tokens: 20000.0,
    background: BackgroundMargin::WindowPercent(10.0),
    token_count: ThresholdTokens::Estimate,
};

fn over(sizes: &[u64], window: u64, policy: &CompactionPolicy) -> Vec<Option<Threshold>> {
    sizes
        .iter()
        .map(|&tokens| threshold_for(tokens, window, policy))
        .collect()
}

/// The margin is a tenth of the window, the reserve and the margin go to
/// the core in tokens: background strictly above 163616, blocking strictly
/// above 183616.
#[test]
fn a_window_percent_margin_starts_background_strictly_above_its_threshold() {
    assert_eq!(
        over(&[0, 163_616, 163_617, 183_616, 183_617], WINDOW, &EARLY),
        vec![
            None,
            None,
            Some(Threshold::Background),
            Some(Threshold::Background),
            Some(Threshold::Blocking),
        ]
    );
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
