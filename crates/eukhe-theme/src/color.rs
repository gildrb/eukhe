//! Color math on sRGB colors: the strict `#rrggbb` form, the WCAG relative
//! luminance and contrast ratio as exact integer comparisons, the one
//! ANSI-16 table, the one ANSI-256 palette and the one quantization to it.
//! `bend/color.bend` models every function here; the bridge test in
//! eukhe-core compares the two.

use std::fmt;

/// An sRGB color, 8 bits per channel.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Rgb {
    pub r: u8,
    pub g: u8,
    pub b: u8,
}

impl Rgb {
    #[must_use]
    pub const fn new(r: u8, g: u8, b: u8) -> Self {
        Self { r, g, b }
    }

    /// `#rrggbb`, exactly: a `#` and six hex digits (either case).
    #[must_use]
    pub fn parse_hex(text: &str) -> Option<Self> {
        let hex = text.strip_prefix('#')?;
        if hex.len() != 6 || !hex.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return None;
        }
        let channel = |at: usize| u8::from_str_radix(&hex[at..at + 2], 16).ok();
        Some(Self::new(channel(0)?, channel(2)?, channel(4)?))
    }

    /// The channels scaled by `factor` (above 1 brighter, below 1 darker),
    /// each rounded and clamped to 0-255.
    #[must_use]
    pub fn scaled(self, factor: f64) -> Self {
        // The clamp keeps the value in 0..=255, so the cast is exact.
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let channel = |c: u8| (f64::from(c) * factor).round().clamp(0.0, 255.0) as u8;
        Self::new(channel(self.r), channel(self.g), channel(self.b))
    }
}

/// `#rrggbb`, lowercase: the only color form the HTML export writes.
impl fmt::Display for Rgb {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "#{:02x}{:02x}{:02x}", self.r, self.g, self.b)
    }
}

/// A linear channel value of 1.0 (see [`linear_channel`]).
pub const LINEAR_ONE: u32 = 10_000;

/// A relative luminance of 1.0 (see [`luminance`]).
pub const LUMINANCE_ONE: u32 = 100_000_000;

/// The WCAG flare term, 0.05, in [`luminance`] units.
const FLARE: u32 = 5_000_000;

/// The sRGB channel `channel` linearized (the sRGB transfer function), in
/// units of 1/[`LINEAR_ONE`], rounded to the nearest unit.
#[must_use]
pub fn linear_channel(channel: u8) -> u32 {
    let encoded = f64::from(channel) / 255.0;
    let linear = if encoded <= 0.04045 {
        encoded / 12.92
    } else {
        ((encoded + 0.055) / 1.055).powf(2.4)
    };
    // `linear` is in 0.0..=1.0, so the product is in 0..=LINEAR_ONE.
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let units = (linear * f64::from(LINEAR_ONE)).round() as u32;
    units
}

/// The WCAG relative luminance of `color`, in units of
/// 1/[`LUMINANCE_ONE`]: `0.2126 R + 0.7152 G + 0.0722 B` over the
/// linearized channels, computed exactly on integers.
#[must_use]
pub fn luminance(color: Rgb) -> u32 {
    2126 * linear_channel(color.r) + 7152 * linear_channel(color.g) + 722 * linear_channel(color.b)
}

/// A minimum WCAG contrast ratio, `numerator / denominator`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ContrastRatio {
    pub numerator: u32,
    pub denominator: u32,
}

impl ContrastRatio {
    /// WCAG 1.4.3: text, 4.5:1.
    pub const TEXT: Self = Self {
        numerator: 9,
        denominator: 2,
    };
    /// WCAG 1.4.11: non-text user-interface parts, 3:1.
    pub const NON_TEXT: Self = Self {
        numerator: 3,
        denominator: 1,
    };
}

/// True when the WCAG contrast ratio of `a` and `b`,
/// `(L_light + 0.05) / (L_dark + 0.05)`, is at least `ratio`. The
/// comparison is exact: `(L_dark + 0.05) * n <= (L_light + 0.05) * d`
/// on integers.
#[must_use]
pub fn contrast_at_least(a: Rgb, b: Rgb, ratio: ContrastRatio) -> bool {
    let (la, lb) = (luminance(a), luminance(b));
    let (light, dark) = if la >= lb { (la, lb) } else { (lb, la) };
    u64::from(dark + FLARE) * u64::from(ratio.numerator)
        <= u64::from(light + FLARE) * u64::from(ratio.denominator)
}

/// Light or dark: a color is light when its relative luminance is above
/// one half.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mode {
    Dark,
    Light,
}

impl Mode {
    /// The mode of a theme whose background is `background`.
    #[must_use]
    pub fn of_background(background: Rgb) -> Self {
        if luminance(background) > LUMINANCE_ONE / 2 {
            Mode::Light
        } else {
            Mode::Dark
        }
    }
}

/// The ANSI-16 palette (indices 0-15): the standard eight, then the bright
/// eight. A terminal may define them differently; these are the values a
/// page that cannot ask the terminal paints.
const ANSI_16: [Rgb; 16] = [
    Rgb::new(0x00, 0x00, 0x00),
    Rgb::new(0x80, 0x00, 0x00),
    Rgb::new(0x00, 0x80, 0x00),
    Rgb::new(0x80, 0x80, 0x00),
    Rgb::new(0x00, 0x00, 0x80),
    Rgb::new(0x80, 0x00, 0x80),
    Rgb::new(0x00, 0x80, 0x80),
    Rgb::new(0xc0, 0xc0, 0xc0),
    Rgb::new(0x80, 0x80, 0x80),
    Rgb::new(0xff, 0x00, 0x00),
    Rgb::new(0x00, 0xff, 0x00),
    Rgb::new(0xff, 0xff, 0x00),
    Rgb::new(0x00, 0x00, 0xff),
    Rgb::new(0xff, 0x00, 0xff),
    Rgb::new(0x00, 0xff, 0xff),
    Rgb::new(0xff, 0xff, 0xff),
];

/// The channel levels of the xterm 6x6x6 color cube.
const CUBE_LEVELS: [u8; 6] = [0, 95, 135, 175, 215, 255];

/// The first gray of the xterm gray ramp (index 232) and the step to the
/// next one (24 grays).
const GRAY_FIRST: u8 = 8;
const GRAY_STEP: u8 = 10;

/// True for the indices a terminal defines itself (0-15, the ANSI-16
/// slots): their rendered color is unknown to a terminal program.
#[must_use]
pub fn is_terminal_defined(index: u8) -> bool {
    index < 16
}

/// The color of xterm-256 palette index `index`: the ANSI-16 table, the
/// 6x6x6 cube, then the 24-step gray ramp.
#[must_use]
pub fn ansi256(index: u8) -> Rgb {
    match index {
        0..=15 => ANSI_16[usize::from(index)],
        16..=231 => {
            let slot = usize::from(index - 16);
            Rgb::new(
                CUBE_LEVELS[slot / 36],
                CUBE_LEVELS[slot / 6 % 6],
                CUBE_LEVELS[slot % 6],
            )
        }
        232..=255 => {
            let gray = GRAY_FIRST + (index - 232) * GRAY_STEP;
            Rgb::new(gray, gray, gray)
        }
    }
}

/// The perceptual channel weights the quantization measures distance
/// with, per mille (red, green, blue).
const WEIGHTS: [u32; 3] = [299, 587, 114];

/// The weighted squared distance of two colors.
fn weighted_distance(a: Rgb, b: Rgb) -> u32 {
    let square = |x: u8, y: u8| u32::from(x.abs_diff(y)) * u32::from(x.abs_diff(y));
    WEIGHTS[0] * square(a.r, b.r) + WEIGHTS[1] * square(a.g, b.g) + WEIGHTS[2] * square(a.b, b.b)
}

/// The index of the cube level nearest `value` (the lower one on a tie).
fn nearest_level(value: u8) -> u8 {
    let mut best = 0;
    for (at, level) in (0u8..).zip(CUBE_LEVELS) {
        if value.abs_diff(level) < value.abs_diff(CUBE_LEVELS[usize::from(best)]) {
            best = at;
        }
    }
    best
}

/// Quantize `color` to the xterm-256 palette: the nearest cube level per
/// channel, or, for a near-neutral color (channel spread below 10), the
/// gray nearest its weighted lightness when that gray is strictly closer
/// than the cube color. Ties take the lower index. All arithmetic is on
/// integers.
#[must_use]
pub fn rgb_to_256(color: Rgb) -> u8 {
    let (ri, gi, bi) = (
        nearest_level(color.r),
        nearest_level(color.g),
        nearest_level(color.b),
    );
    let cube = Rgb::new(
        CUBE_LEVELS[usize::from(ri)],
        CUBE_LEVELS[usize::from(gi)],
        CUBE_LEVELS[usize::from(bi)],
    );
    let cube_index = 16 + 36 * ri + 6 * gi + bi;
    // The weighted lightness, per mille; the gray slot nearest it.
    let lightness = WEIGHTS[0] * u32::from(color.r)
        + WEIGHTS[1] * u32::from(color.g)
        + WEIGHTS[2] * u32::from(color.b);
    let gray_at = |slot: u8| GRAY_FIRST + slot * GRAY_STEP;
    let mut slot = 0;
    for candidate in 1..24 {
        let off = |s: u8| lightness.abs_diff(1000 * u32::from(gray_at(s)));
        if off(candidate) < off(slot) {
            slot = candidate;
        }
    }
    let gray = Rgb::new(gray_at(slot), gray_at(slot), gray_at(slot));
    let spread = color.r.max(color.g).max(color.b) - color.r.min(color.g).min(color.b);
    if spread < 10 && weighted_distance(color, gray) < weighted_distance(color, cube) {
        232 + slot
    } else {
        cube_index
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every cube and gray-ramp color quantizes back to its own index.
    #[test]
    fn the_palette_colors_quantize_to_themselves() {
        let back: Vec<u8> = (16..=255).map(|index| rgb_to_256(ansi256(index))).collect();
        assert_eq!(back, (16..=255).collect::<Vec<u8>>());
    }

    /// Black on white is 21:1, the maximum: it clears both ratios; a color
    /// on itself is 1:1 and clears neither.
    #[test]
    fn contrast_extremes() {
        let (black, white) = (Rgb::new(0, 0, 0), Rgb::new(255, 255, 255));
        assert_eq!(
            [
                contrast_at_least(black, white, ContrastRatio::TEXT),
                contrast_at_least(white, black, ContrastRatio::NON_TEXT),
                contrast_at_least(white, white, ContrastRatio::NON_TEXT),
            ],
            [true, true, false]
        );
    }

    #[test]
    fn hex_is_strict() {
        assert_eq!(
            ["#0A0b0c", "#abc", "0a0b0c", "#0a0b0g", "#0a0b0c0"].map(Rgb::parse_hex),
            [Some(Rgb::new(10, 11, 12)), None, None, None, None]
        );
    }
}
