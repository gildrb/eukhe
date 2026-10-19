//! The bridge from the terminal UI's color code to its Bend model
//! (`bend/tui_color.bend`, docs/interface.md T3): the effort ramp
//! ([`ramp_rung`], [`Theme::effort_ramp`]), the usage bands
//! ([`crate::status_line::context_band`]) and the color roles (the
//! tokens of [`ThemeColor`], [`ThemeBg`] and [`ThemeRgb`]) run generated
//! scenarios, and `bend/bridge_tui_color.bend` must print the same
//! transcript, byte for byte.
//!
//! A scenario file (no trailing newline) has one query a line:
//!
//! - `e LR LG LB HR HG HB N`: the N-rung ramp between two colors. Prints
//!   `e` and ` R,G,B` for each rung.
//! - `s I N`: the N-rung effort ramp of the builtin theme I (0 eukhe, 1
//!   dark, 2 light), as [`Theme::effort_ramp`] paints it in truecolor.
//!   Prints `s` and the rungs.
//! - `b T W`: the usage band of T tokens in a W-token window. Prints
//!   `b B`.
//! - `r`: every color role of the terminal UI. Prints `r` and ` I` for
//!   each role, its token index.

use super::{ramp_rung, Color, ColorMode, Paint, Theme, ThemeBg, ThemeColor, ThemeRgb};
use crate::testing::{compare, Rng, Scenario};
use eukhe_theme::Rgb;
use std::fmt::Write as _;

const MODEL: &str = "bend/bridge_tui_color.bend";

/// The builtin themes by their scenario number.
const SHIPPED: [&str; 3] = ["eukhe", "dark", "light"];

/// `tag` and ` R,G,B` for each rung.
fn rungs_line(tag: &str, rungs: impl Iterator<Item = Rgb>) -> String {
    let mut line = tag.to_string();
    for rgb in rungs {
        write!(line, " {},{},{}", rgb.r, rgb.g, rgb.b).unwrap();
    }
    line
}

/// One query: its scenario line and the line the Rust code prints.
fn ramp(low: Rgb, high: Rgb, rungs: usize) -> (String, String) {
    (
        format!(
            "e {} {} {} {} {} {} {rungs}",
            low.r, low.g, low.b, high.r, high.g, high.b
        ),
        rungs_line(
            "e",
            (1..=rungs).map(|rung| ramp_rung(low, high, rung, rungs)),
        ),
    )
}

fn shipped(index: usize, rungs: usize) -> (String, String) {
    let theme = Theme::builtin(SHIPPED[index], ColorMode::TrueColor);
    let rgb = |color: Option<Color>| match color {
        Some(Color(Paint::Rgb(r, g, b))) => Rgb::new(r, g, b),
        other => panic!("a truecolor rung paints #rrggbb, not {other:?}"),
    };
    (
        format!("s {index} {rungs}"),
        rungs_line("s", theme.effort_ramp(rungs).map(|style| rgb(style.fg))),
    )
}

fn band(tokens: u64, window: u64) -> (String, String) {
    (
        format!("b {tokens} {window}"),
        format!("b {}", crate::status_line::context_band(tokens, window)),
    )
}

fn roles() -> (String, String) {
    let tokens = ThemeColor::ALL
        .map(ThemeColor::token)
        .into_iter()
        .chain(ThemeBg::ALL.map(ThemeBg::token))
        .chain(ThemeRgb::ALL.map(ThemeRgb::token));
    let mut line = String::from("r");
    for token in tokens {
        write!(line, " {}", token as usize).unwrap();
    }
    ("r".to_string(), line)
}

fn rgb(rng: &mut Rng) -> Rgb {
    // Mostly any channel; one in four at an end of the range.
    let mut channel = || match rng.below(8) {
        0 => 0,
        1 => 255,
        _ => rng.below(256) as u8,
    };
    Rgb::new(channel(), channel(), channel())
}

fn scenario(name: &str, queries: Vec<(String, String)>) -> Scenario {
    let (events, lines): (Vec<String>, Vec<String>) = queries.into_iter().unzip();
    let mut transcript = lines.join("\n");
    transcript.push('\n');
    Scenario {
        name: name.to_string(),
        events: events.join("\n"),
        transcript,
    }
}

/// The ramp, the shipped ramps, the bands and the roles answer as the
/// model does: ramps between random and edge colors (equal ends, the
/// range ends) of every length up to 12 and some far longer than any
/// channel distance; every shipped ramp up to 8 rungs; token counts at,
/// just below and just above every band of small and huge windows, the
/// unknown window, and random counts.
#[test]
fn the_rust_terminal_colors_equal_the_bend_model() {
    let mut rng = Rng(0x7c01_0a5e_eff0_47a5);
    let mut ramps = Vec::new();
    let black = Rgb::new(0, 0, 0);
    let white = Rgb::new(255, 255, 255);
    for rungs in 0..=12 {
        ramps.push(ramp(black, white, rungs));
        ramps.push(ramp(white, black, rungs));
        ramps.push(ramp(Rgb::new(9, 9, 9), Rgb::new(9, 9, 9), rungs));
    }
    for _ in 0..400 {
        let (low, high) = (rgb(&mut rng), rgb(&mut rng));
        let rungs = if rng.below(10) == 0 {
            rng.range(256, 600) as usize
        } else {
            rng.range(1, 12) as usize
        };
        ramps.push(ramp(low, high, rungs));
    }
    let mut themes = Vec::new();
    for index in 0..SHIPPED.len() {
        for rungs in 0..=8 {
            themes.push(shipped(index, rungs));
        }
    }
    let mut bands = vec![band(0, 0), band(5_000, 0), band(0, 128_000)];
    for window in [10, 128_000, 200_000, 1_000_000, 10_000_000_000] {
        for (num, den) in [(1, 2), (7, 10), (9, 10)] {
            let at = window * num / den;
            bands.extend([band(at - 1, window), band(at, window), band(at + 1, window)]);
        }
        bands.push(band(window, window));
        bands.push(band(window * 3, window));
    }
    for _ in 0..300 {
        let window = rng.range(1, 2_000_000);
        bands.push(band(rng.range(0, window + window / 4), window));
    }
    compare(
        MODEL,
        [
            scenario("ramps", ramps),
            scenario("shipped ramps", themes),
            scenario("bands", bands),
            scenario("roles", vec![roles()]),
        ],
    );
}
