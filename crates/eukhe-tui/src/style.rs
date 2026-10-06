//! Cell styles: a foreground, a background, and text modifiers. The SGR
//! encoding lives in [`crate::ansi::line_to_ansi`].

use std::fmt;
use std::ops::{BitOr, BitOrAssign};

/// A terminal color.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Color {
    /// The terminal's default color (SGR 39 / 49).
    Reset,
    /// A 256-color palette index (SGR 38;5 / 48;5).
    Indexed(u8),
    /// A 24-bit color (SGR 38;2 / 48;2).
    Rgb(u8, u8, u8),
}

/// A set of text modifiers.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Modifier(u8);

impl Modifier {
    pub const BOLD: Self = Self(1);
    pub const DIM: Self = Self(1 << 1);
    pub const ITALIC: Self = Self(1 << 2);
    pub const UNDERLINED: Self = Self(1 << 3);
    pub const REVERSED: Self = Self(1 << 4);
    pub const CROSSED_OUT: Self = Self(1 << 5);

    /// Every modifier with its builder name, in SGR-writing order.
    const NAMES: [(Self, &'static str); 6] = [
        (Self::BOLD, "bold"),
        (Self::DIM, "dim"),
        (Self::ITALIC, "italic"),
        (Self::UNDERLINED, "underlined"),
        (Self::REVERSED, "reversed"),
        (Self::CROSSED_OUT, "crossed_out"),
    ];

    #[must_use]
    pub const fn empty() -> Self {
        Self(0)
    }

    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// Whether every modifier in `other` is set.
    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }
}

impl BitOr for Modifier {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for Modifier {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl fmt::Debug for Modifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut set = f.debug_set();
        for (modifier, name) in Self::NAMES {
            if self.contains(modifier) {
                set.entry(&format_args!("{name}"));
            }
        }
        set.finish()
    }
}

/// A cell style. `None` colors leave the terminal's current color.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Style {
    pub fg: Option<Color>,
    pub bg: Option<Color>,
    pub add_modifier: Modifier,
}

impl Style {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            fg: None,
            bg: None,
            add_modifier: Modifier::empty(),
        }
    }

    #[must_use]
    pub const fn fg(mut self, color: Color) -> Self {
        self.fg = Some(color);
        self
    }

    #[must_use]
    pub const fn bg(mut self, color: Color) -> Self {
        self.bg = Some(color);
        self
    }

    #[must_use]
    pub const fn add_modifier(mut self, modifier: Modifier) -> Self {
        self.add_modifier = Modifier(self.add_modifier.0 | modifier.0);
        self
    }

    /// Layer `other` over this style: its colors win where set, its
    /// modifiers add.
    #[must_use]
    pub const fn patch(self, other: Self) -> Self {
        Self {
            fg: match other.fg {
                Some(color) => Some(color),
                None => self.fg,
            },
            bg: match other.bg {
                Some(color) => Some(color),
                None => self.bg,
            },
            add_modifier: Modifier(self.add_modifier.0 | other.add_modifier.0),
        }
    }
}

/// The builder chain that rebuilds the style:
/// `Style::new().fg(Color::Rgb(1, 2, 3)).bold()`.
impl fmt::Debug for Style {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Style::new()")?;
        if let Some(fg) = self.fg {
            write!(f, ".fg(Color::{fg:?})")?;
        }
        if let Some(bg) = self.bg {
            write!(f, ".bg(Color::{bg:?})")?;
        }
        for (modifier, name) in Modifier::NAMES {
            if self.add_modifier.contains(modifier) {
                write!(f, ".{name}()")?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn patch_layers_colors_and_adds_modifiers() {
        let base = Style::new()
            .fg(Color::Indexed(1))
            .bg(Color::Rgb(1, 2, 3))
            .add_modifier(Modifier::BOLD);
        let over = Style::new().fg(Color::Reset).add_modifier(Modifier::ITALIC);
        assert_eq!(
            base.patch(over),
            Style {
                fg: Some(Color::Reset),
                bg: Some(Color::Rgb(1, 2, 3)),
                add_modifier: Modifier::BOLD | Modifier::ITALIC,
            }
        );
    }

    #[test]
    fn debug_prints_the_builder_chain() {
        let style = Style::new()
            .fg(Color::Rgb(161, 161, 170))
            .bg(Color::Indexed(5))
            .add_modifier(Modifier::CROSSED_OUT | Modifier::BOLD);
        assert_eq!(
            format!("{style:?}"),
            "Style::new().fg(Color::Rgb(161, 161, 170)).bg(Color::Indexed(5)).bold().crossed_out()"
        );
    }
}
