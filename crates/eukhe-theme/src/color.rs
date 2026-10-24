//! Colors: an sRGB color and its `#rrggbb` form, light or dark, and the
//! xterm-256 indices a terminal defines itself. The color math (luminance,
//! contrast, the xterm-256 palette and quantization) runs in the compiled
//! Bend core (`bend/color.bend`; eukhe-bend `rules::color`).

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

    /// The color of `[red, green, blue]` channels.
    #[must_use]
    pub const fn from_channels([r, g, b]: [u8; 3]) -> Self {
        Self { r, g, b }
    }

    /// The `[red, green, blue]` channels.
    #[must_use]
    pub const fn channels(self) -> [u8; 3] {
        [self.r, self.g, self.b]
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

/// Light or dark: a theme is light when its background's relative
/// luminance is above one half (decided by the compiled core).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mode {
    Dark,
    Light,
}

/// True for the indices a terminal defines itself (0-15, the ANSI-16
/// slots): their rendered color is unknown to a terminal program.
#[must_use]
pub fn is_terminal_defined(index: u8) -> bool {
    index < 16
}
