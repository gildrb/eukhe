//! Throughput and first-use latency of [`Encoding::count`]. Not a
//! correctness test: run it alone, in release, in a fresh process (the
//! first-use timings are only meaningful before any table is decoded):
//!
//! ```text
//! cargo test -p eukhe-tokens --release --lib -- --ignored --exact \
//!     utok::tests::throughput::count_throughput --nocapture
//! ```

use std::time::Instant;

use crate::utok::Encoding;

const TARGET_BYTES: usize = 2 << 20;

/// English prose and Rust code: this crate's own sources (doc comments and
/// code), repeated to 2 MiB.
fn english_code() -> String {
    let sources = [
        include_str!("../bpe.rs"),
        include_str!("../jev.rs"),
        include_str!("../pretoken.rs"),
        include_str!("../tables.rs"),
        include_str!("../utf.rs"),
        include_str!("../claude/constants.rs"),
        include_str!("../claude/engine.rs"),
        include_str!("../claude/mod.rs"),
        include_str!("../claude/normalize.rs"),
        include_str!("../scan/mod.rs"),
        include_str!("../scan/deepseek.rs"),
        include_str!("../scan/kimi.rs"),
        include_str!("../scan/qwen.rs"),
        include_str!("../../../data/README.md"),
    ];
    let mut text = String::with_capacity(TARGET_BYTES + 64 * 1024);
    while text.len() < TARGET_BYTES {
        for source in sources {
            text.push_str(source);
        }
    }
    text
}

/// Synthetic CJK: Han ideographs drawn from the first 2,500 of the URO block
/// (the low range holds many common characters) by a splitmix64 stream,
/// with a full-width comma or full stop every 8–23 characters.
fn cjk() -> String {
    let mut state = 0x00c0_ffee_u64;
    let mut next = || {
        state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    };
    let mut text = String::with_capacity(TARGET_BYTES + 64);
    let mut until_punct = 8;
    while text.len() < TARGET_BYTES {
        let offset = u32::try_from(next() % 2500).expect("below 2500");
        text.push(char::from_u32(0x4e00 + offset).expect("URO ideograph"));
        until_punct -= 1;
        if until_punct == 0 {
            text.push(if next() % 3 == 0 { '。' } else { '，' });
            until_punct = 8 + next() % 16;
        }
    }
    text
}

#[test]
#[ignore = "benchmark: run explicitly in release (see module doc)"]
fn count_throughput() {
    println!("first use (decode + first count of \"a\"):");
    for encoding in [
        Encoding::O200kBase,
        Encoding::Cl100kBase,
        Encoding::ClaudeV3,
        Encoding::ClaudeV47,
        Encoding::ClaudeV5,
        Encoding::ClaudeV5Sonnet,
        Encoding::Qwen3,
        Encoding::DeepSeekV3,
        Encoding::KimiK2,
        Encoding::Glm5,
        Encoding::Jev,
    ] {
        let start = Instant::now();
        let n = encoding.count("a");
        let first = start.elapsed();
        let start = Instant::now();
        let again = encoding.count("a");
        let warm = start.elapsed();
        assert_eq!(n, again);
        println!("  {encoding:?}: first {first:?}, warm {warm:?}");
    }

    let corpora = [("english+code", english_code()), ("cjk", cjk())];
    println!("throughput (count of one 2 MiB string; first pass, best of 5):");
    for encoding in [Encoding::O200kBase, Encoding::ClaudeV5Sonnet] {
        for (name, text) in &corpora {
            let mut first = None;
            let mut best = f64::INFINITY;
            let mut tokens = 0;
            for _ in 0..5 {
                let start = Instant::now();
                tokens = encoding.count(text);
                let secs = start.elapsed().as_secs_f64();
                first.get_or_insert(secs);
                best = best.min(secs);
            }
            let first = first.expect("five passes ran");
            #[allow(
                clippy::cast_precision_loss,
                reason = "a 2 MiB byte count is exact in f64"
            )]
            let mb = text.len() as f64 / 1e6;
            println!(
                "  {encoding:?} {name}: {mb:.2} MB, {tokens} tokens; first {:.1} ms = {:.1} \
                 MB/s; best {:.1} ms = {:.1} MB/s",
                first * 1e3,
                mb / first,
                best * 1e3,
                mb / best
            );
        }
    }
}
