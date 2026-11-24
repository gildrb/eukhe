//! Chords and text as macOS key presses (port of omp
//! `crates/natives/src/desktop/macos/keymap.rs` and the key tables of its
//! `input.rs`). Chord keys use the ANSI virtual key codes; a character no
//! ANSI key types goes out as its Unicode text on virtual key 0, which
//! `AppKit` reads.

use crate::keys::{Chord, Key, Modifier};

/// One key transition with the modifier flags held during it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Press {
    pub(super) code: u16,
    pub(super) edge: Edge,
    pub(super) flags: u64,
    /// The text the key types, when it types any.
    pub(super) text: Option<char>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Edge {
    Down,
    Up,
}

const RETURN: u16 = 36;
const TAB: u16 = 48;
/// The key whose code carries Unicode text it does not itself type.
const UNICODE_CARRIER: u16 = 0;

const fn modifier_code(modifier: Modifier) -> u16 {
    match modifier {
        Modifier::Ctrl => 59,
        Modifier::Alt => 58,
        Modifier::Shift => 56,
        Modifier::Meta => 55,
    }
}

/// `kCGEventFlagMask*` of a modifier.
const fn modifier_flag(modifier: Modifier) -> u64 {
    match modifier {
        Modifier::Ctrl => 0x0004_0000,
        Modifier::Alt => 0x0008_0000,
        Modifier::Shift => 0x0002_0000,
        Modifier::Meta => 0x0010_0000,
    }
}

/// Virtual codes of F1 through F20.
const FUNCTION_CODES: [u16; 20] = [
    122, 120, 99, 118, 96, 97, 98, 100, 101, 109, 103, 111, 105, 107, 113, 106, 64, 79, 80, 90,
];

/// The ANSI keys that type these characters unshifted.
const CHAR_CODES: &[(char, u16)] = &[
    ('a', 0),
    ('s', 1),
    ('d', 2),
    ('f', 3),
    ('h', 4),
    ('g', 5),
    ('z', 6),
    ('x', 7),
    ('c', 8),
    ('v', 9),
    ('b', 11),
    ('q', 12),
    ('w', 13),
    ('e', 14),
    ('r', 15),
    ('y', 16),
    ('t', 17),
    ('1', 18),
    ('2', 19),
    ('3', 20),
    ('4', 21),
    ('6', 22),
    ('5', 23),
    ('=', 24),
    ('9', 25),
    ('7', 26),
    ('-', 27),
    ('8', 28),
    ('0', 29),
    (']', 30),
    ('o', 31),
    ('u', 32),
    ('[', 33),
    ('i', 34),
    ('p', 35),
    ('l', 37),
    ('j', 38),
    ('\'', 39),
    ('k', 40),
    (';', 41),
    ('\\', 42),
    (',', 43),
    ('/', 44),
    ('n', 45),
    ('m', 46),
    ('.', 47),
    ('`', 50),
];

/// A chord key's virtual code and the text it carries; `None` for a key
/// macOS keyboards lack (F21 to F24).
fn key_code(key: Key) -> Option<(u16, Option<char>)> {
    let code = match key {
        Key::Enter => RETURN,
        Key::Escape => 53,
        Key::Tab => TAB,
        Key::Space => return Some((49, Some(' '))),
        Key::Backspace => 51,
        Key::Delete => 117,
        Key::Insert => 114,
        Key::Home => 115,
        Key::End => 119,
        Key::PageUp => 116,
        Key::PageDown => 121,
        Key::Up => 126,
        Key::Down => 125,
        Key::Left => 123,
        Key::Right => 124,
        Key::CapsLock => 57,
        Key::NumLock => 71,
        Key::PrintScreen => 105,
        Key::Function(function) => {
            return FUNCTION_CODES
                .get(usize::from(function.number()).checked_sub(1)?)
                .map(|code| (*code, None));
        }
        Key::Char(character) => {
            let code = CHAR_CODES
                .iter()
                .find(|(typed, _)| *typed == character)
                .map_or(UNICODE_CARRIER, |(_, code)| *code);
            return Some((code, Some(character)));
        }
    };
    Some((code, None))
}

/// Why a chord has no macOS keys.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct NoKey;

/// The presses of `chord`: modifiers down in order, the key down and up,
/// then the modifiers up in reverse.
pub(super) fn chord_presses(chord: Chord) -> Result<Vec<Press>, NoKey> {
    let key = chord
        .key
        .map(key_code)
        .map(|code| code.ok_or(NoKey))
        .transpose()?;
    let modifiers: Vec<Modifier> = chord.modifiers.iter().collect();
    let mut presses = Vec::with_capacity(modifiers.len() * 2 + 2);
    let mut flags = 0;
    for modifier in &modifiers {
        flags |= modifier_flag(*modifier);
        presses.push(Press {
            code: modifier_code(*modifier),
            edge: Edge::Down,
            flags,
            text: None,
        });
    }
    if let Some((code, text)) = key {
        for edge in [Edge::Down, Edge::Up] {
            presses.push(Press {
                code,
                edge,
                flags,
                text,
            });
        }
    }
    for modifier in modifiers.iter().rev() {
        flags &= !modifier_flag(*modifier);
        presses.push(Press {
            code: modifier_code(*modifier),
            edge: Edge::Up,
            flags,
            text: None,
        });
    }
    Ok(presses)
}

/// The presses that type `text`: each character's Unicode text on virtual
/// key 0, line breaks and tabs as their own keys, which web content reads
/// by code.
pub(super) fn text_presses(text: &str) -> Vec<Press> {
    let mut presses = Vec::with_capacity(text.len() * 2);
    let mut characters = text.chars().peekable();
    while let Some(character) = characters.next() {
        let code = match character {
            '\r' => {
                if characters.peek() == Some(&'\n') {
                    characters.next();
                }
                RETURN
            }
            '\n' => RETURN,
            '\t' => TAB,
            _ => UNICODE_CARRIER,
        };
        let typed = match code {
            UNICODE_CARRIER => Some(character),
            _ => None,
        };
        for edge in [Edge::Down, Edge::Up] {
            presses.push(Press {
                code,
                edge,
                flags: 0,
                text: typed,
            });
        }
    }
    presses
}

#[cfg(test)]
mod tests {
    use super::*;

    fn chord(text: &str) -> Chord {
        text.parse().unwrap_or_else(|error| panic!("{error}"))
    }

    #[test]
    fn a_chord_holds_its_modifiers_around_the_key_and_releases_in_reverse() {
        let presses = chord_presses(chord("cmd+shift+s")).unwrap_or_default();
        let steps: Vec<(u16, Edge, u64)> = presses
            .iter()
            .map(|press| (press.code, press.edge, press.flags))
            .collect();
        assert_eq!(
            steps,
            [
                (56, Edge::Down, 0x2_0000),
                (55, Edge::Down, 0x12_0000),
                (1, Edge::Down, 0x12_0000),
                (1, Edge::Up, 0x12_0000),
                (55, Edge::Up, 0x2_0000),
                (56, Edge::Up, 0),
            ]
        );
        assert_eq!(presses[2].text, Some('s'));
    }

    #[test]
    fn named_keys_and_function_keys_have_their_codes() {
        let code = |text: &str| chord_presses(chord(text)).map(|presses| presses[0].code);
        assert_eq!(code("enter"), Ok(36));
        assert_eq!(code("f1"), Ok(122));
        assert_eq!(code("f20"), Ok(90));
        assert_eq!(chord_presses(chord("f24")), Err(NoKey));
    }

    #[test]
    fn a_character_no_ansi_key_types_rides_on_key_zero() {
        let presses = chord_presses(chord("é")).unwrap_or_default();
        assert_eq!((presses[0].code, presses[0].text), (0, Some('é')));
    }

    #[test]
    fn text_types_each_character_and_breaks_lines_with_return() {
        let presses = text_presses("a\r\nb\t");
        let downs: Vec<(u16, Option<char>)> = presses
            .iter()
            .filter(|press| press.edge == Edge::Down)
            .map(|press| (press.code, press.text))
            .collect();
        assert_eq!(
            downs,
            [(0, Some('a')), (RETURN, None), (0, Some('b')), (TAB, None)]
        );
        assert_eq!(presses.len(), 8);
    }
}
