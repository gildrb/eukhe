//! The cost of slash-command completion per keystroke: each line below
//! is typed into an editor one key at a time, its menu materialized after
//! every key as at a real keyboard, and the time of each key (the key
//! and its menu, rows and ghost hint) is recorded.
//!
//! `cargo run --release -p eukhe-tui --example slash_complete_bench`

use std::time::{Duration, Instant};

use eukhe_tui::editor::Editor;

const LINES: &[&str] = &[
    "/budget set cost=2 tokens=200k time=10m calls=50",
    "/loop 7 --until 'cargo test' fix the failing tests",
    "/accept cmd --timeout 60 --protect src make check",
    "/effects ran toolu_01AbC",
    "/heartbeat --every 10m --follow-up check the build",
    "/memory model",
    "/workflows size large",
    "/scoped",
    "/compact keep the decisions",
];

const ROUNDS: usize = 200;

/// The value at `percent` of the sorted times.
fn percentile(sorted: &[Duration], percent: usize) -> Duration {
    sorted[(sorted.len() - 1) * percent / 100]
}

fn main() {
    let mut keys: Vec<Duration> = Vec::new();
    for _ in 0..ROUNDS {
        for line in LINES {
            let mut editor = Editor::new();
            for (at, c) in line.char_indices() {
                let key = &line[at..at + c.len_utf8()];
                let start = Instant::now();
                editor.handle_input(key);
                editor.materialize_autocomplete();
                std::hint::black_box(editor.ghost_hint());
                keys.push(start.elapsed());
            }
        }
    }
    keys.sort_unstable();
    let total: Duration = keys.iter().sum();
    println!(
        "keys {} mean {:?} p50 {:?} p99 {:?} max {:?}",
        keys.len(),
        total / u32::try_from(keys.len()).unwrap_or(u32::MAX),
        percentile(&keys, 50),
        percentile(&keys, 99),
        keys[keys.len() - 1],
    );
}
