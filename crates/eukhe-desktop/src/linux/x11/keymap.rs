//! Keysyms for chords and text, and the keycodes that type them (port of omp
//! `crates/natives/src/desktop/linux/x11/keymap.rs` and `x11/text_mapping.rs`).

use crate::keys::{Chord, Key, Modifier};

/// An X keysym.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Keysym(pub(super) u32);

/// An X keycode.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Keycode(pub(super) u8);

const NO_SYMBOL: u32 = 0;
const SHIFT_L: Keysym = Keysym(0xffe1);

impl Keysym {
    fn of_modifier(modifier: Modifier) -> Self {
        Self(match modifier {
            Modifier::Ctrl => 0xffe3,
            Modifier::Alt => 0xffe9,
            Modifier::Shift => 0xffe1,
            Modifier::Meta => 0xffeb,
        })
    }

    fn of_key(key: Key) -> Self {
        match key {
            Key::Enter => Self(0xff0d),
            Key::Escape => Self(0xff1b),
            Key::Tab => Self(0xff09),
            Key::Space => Self(0x20),
            Key::Backspace => Self(0xff08),
            Key::Delete => Self(0xffff),
            Key::Insert => Self(0xff63),
            Key::Home => Self(0xff50),
            Key::End => Self(0xff57),
            Key::PageUp => Self(0xff55),
            Key::PageDown => Self(0xff56),
            Key::Up => Self(0xff52),
            Key::Down => Self(0xff54),
            Key::Left => Self(0xff51),
            Key::Right => Self(0xff53),
            Key::CapsLock => Self(0xffe5),
            Key::NumLock => Self(0xff7f),
            Key::PrintScreen => Self(0xff61),
            // F1 is 0xffbe and the function keys run on without gaps.
            Key::Function(key) => Self(0xffbd + u32::from(key.number())),
            Key::Char(character) => Self::of_char(character),
        }
    }

    /// Latin-1 characters are their own keysym; the rest of Unicode sits at
    /// `0x0100_0000` plus the code point.
    pub(super) fn of_char(character: char) -> Self {
        match character {
            '\n' | '\r' => Self(0xff0d),
            '\t' => Self(0xff09),
            ' '..='~' | '\u{a0}'..='\u{ff}' => Self(u32::from(character)),
            other => Self(0x0100_0000 | u32::from(other)),
        }
    }
}

/// Where a keysym sits on a keycode: its first column, or the second, which
/// Shift reaches.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Level {
    Base,
    Shifted,
}

/// The core keyboard mapping: `per_code` keysyms for each keycode from `min`.
pub(super) struct Keymap {
    min: u8,
    per_code: u8,
    keysyms: Vec<u32>,
}

impl Keymap {
    pub(super) fn new(min: u8, per_code: u8, keysyms: Vec<u32>) -> Self {
        Self {
            min,
            per_code,
            keysyms,
        }
    }

    fn rows(&self) -> impl Iterator<Item = (Keycode, &[u32])> {
        let width = usize::from(self.per_code.max(1));
        self.keysyms
            .chunks(width)
            .zip(self.min..=u8::MAX)
            .map(|(row, code)| (Keycode(code), row))
    }

    /// The keycode and level typing `keysym`, base level first.
    pub(super) fn find(&self, keysym: Keysym) -> Option<(Keycode, Level)> {
        let at = |column: usize, level| {
            self.rows()
                .find(|(_, row)| row.get(column) == Some(&keysym.0))
                .map(|(code, _)| (code, level))
        };
        at(0, Level::Base).or_else(|| at(1, Level::Shifted))
    }

    /// A keycode with no keysym at all, which text can borrow for a keysym
    /// the layout lacks.
    pub(super) fn spare(&self) -> Option<Keycode> {
        self.rows()
            .filter(|(code, _)| code.0 >= 8)
            .find(|(_, row)| row.iter().all(|sym| *sym == NO_SYMBOL))
            .map(|(code, _)| code)
    }

    pub(super) fn per_code(&self) -> u8 {
        self.per_code
    }
}

/// One key press and release with its modifiers, as planned against a keymap.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Stroke {
    /// Press `modifiers` in order, tap `key` (none for a modifier-only
    /// chord), release them in reverse.
    Mapped {
        modifiers: Vec<Keycode>,
        key: Option<Keycode>,
    },
    /// A character the layout lacks: borrow a spare keycode for `keysym`.
    Borrowed { keysym: Keysym },
}

/// Why keys could not be planned.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub(super) enum PlanError {
    #[error("the keyboard layout has no key for keysym {0:#x}")]
    Unmapped(u32),
}

/// The strokes typing `text`: a character the layout lacks borrows a spare
/// keycode.
pub(super) fn plan_text(keymap: &Keymap, text: &str) -> Result<Vec<Stroke>, PlanError> {
    let shift = keymap.find(SHIFT_L).map(|(code, _)| code);
    text.chars()
        .map(|character| {
            let keysym = Keysym::of_char(character);
            Ok(match (keymap.find(keysym), shift) {
                (Some((code, Level::Base)), _) => Stroke::Mapped {
                    modifiers: Vec::new(),
                    key: Some(code),
                },
                (Some((code, Level::Shifted)), Some(shift)) => Stroke::Mapped {
                    modifiers: vec![shift],
                    key: Some(code),
                },
                (Some((_, Level::Shifted)), None) => {
                    return Err(PlanError::Unmapped(SHIFT_L.0));
                }
                (None, _) => Stroke::Borrowed { keysym },
            })
        })
        .collect()
}

/// The one stroke a chord makes. A key only Shift reaches adds Shift.
pub(super) fn plan_chord(keymap: &Keymap, chord: Chord) -> Result<Stroke, PlanError> {
    let code = |keysym: Keysym| keymap.find(keysym).ok_or(PlanError::Unmapped(keysym.0));
    let mut modifiers = chord
        .modifiers
        .iter()
        .map(|modifier| code(Keysym::of_modifier(modifier)).map(|(code, _)| code))
        .collect::<Result<Vec<_>, _>>()?;
    let key = match chord.key {
        None => None,
        Some(key) => {
            let (key, level) = code(Keysym::of_key(key))?;
            if level == Level::Shifted && !chord.modifiers.contains(Modifier::Shift) {
                modifiers.push(code(SHIFT_L)?.0);
            }
            Some(key)
        }
    };
    Ok(Stroke::Mapped { modifiers, key })
}

/// The keycodes holding `modifiers` down for a pointer gesture.
pub(super) fn modifier_codes(
    keymap: &Keymap,
    modifiers: crate::keys::Modifiers,
) -> Result<Vec<Keycode>, PlanError> {
    modifiers
        .iter()
        .map(|modifier| {
            let keysym = Keysym::of_modifier(modifier);
            keymap
                .find(keysym)
                .map(|(code, _)| code)
                .ok_or(PlanError::Unmapped(keysym.0))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Keycodes 8.. of a US layout fragment: `a A`, `1 !`, `Shift_L`,
    /// `Control_L`, `Return`, then a free keycode.
    fn us() -> Keymap {
        Keymap::new(
            8,
            2,
            vec![
                0x61, 0x41, //
                0x31, 0x21, //
                0xffe1, 0, //
                0xffe3, 0, //
                0xff0d, 0, //
                0, 0,
            ],
        )
    }

    #[test]
    fn text_takes_shift_for_the_second_column_and_borrows_for_the_rest() {
        let plan = plan_text(&us(), "aA!\n€").unwrap_or_default();
        assert_eq!(
            plan,
            vec![
                Stroke::Mapped {
                    modifiers: vec![],
                    key: Some(Keycode(8))
                },
                Stroke::Mapped {
                    modifiers: vec![Keycode(10)],
                    key: Some(Keycode(8))
                },
                Stroke::Mapped {
                    modifiers: vec![Keycode(10)],
                    key: Some(Keycode(9))
                },
                Stroke::Mapped {
                    modifiers: vec![],
                    key: Some(Keycode(12))
                },
                Stroke::Borrowed {
                    keysym: Keysym(0x0100_20ac)
                },
            ]
        );
        assert_eq!(us().spare(), Some(Keycode(13)));
    }

    #[test]
    fn a_chord_presses_its_modifiers_and_adds_shift_for_a_shifted_key() {
        let chord = |text: &str| text.parse::<Chord>().map(|chord| plan_chord(&us(), chord));
        assert_eq!(
            chord("ctrl+a"),
            Ok(Ok(Stroke::Mapped {
                modifiers: vec![Keycode(11)],
                key: Some(Keycode(8))
            }))
        );
        assert_eq!(
            chord("ctrl+!"),
            Ok(Ok(Stroke::Mapped {
                modifiers: vec![Keycode(11), Keycode(10)],
                key: Some(Keycode(9))
            }))
        );
        assert_eq!(chord("alt+a"), Ok(Err(PlanError::Unmapped(0xffe9))));
    }

    #[test]
    fn keysyms_follow_the_latin1_and_unicode_ranges() {
        assert_eq!(Keysym::of_char('é'), Keysym(0xe9));
        assert_eq!(Keysym::of_char('ł'), Keysym(0x0100_0142));
        assert_eq!(Keysym::of_char('\t'), Keysym(0xff09));
    }
}
