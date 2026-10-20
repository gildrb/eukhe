//! The live decode rate of the dashboard estimates tokens from streamed
//! text with `CHARS_PER_TOKEN` in `ui/src/lib/turn.ts`. It must be the one
//! token estimate of `eukhe_types::token_estimate`, the ratio the TUI and
//! the worker use.

use eukhe_types::token_estimate::{CHARS_PER_TOKEN_DENOMINATOR, CHARS_PER_TOKEN_NUMERATOR};

#[test]
fn the_ui_chars_per_token_is_the_one_token_estimate() {
    let source = include_str!("../ui/src/lib/turn.ts");
    let definitions: Vec<&str> = source
        .lines()
        .filter_map(|line| line.strip_prefix("const CHARS_PER_TOKEN = "))
        .collect();
    #[expect(
        clippy::cast_precision_loss,
        reason = "the numerator and the denominator are small integers, exact in f64"
    )]
    let ratio = CHARS_PER_TOKEN_NUMERATOR as f64 / CHARS_PER_TOKEN_DENOMINATOR as f64;
    assert_eq!(definitions, [format!("{ratio};")]);
}
