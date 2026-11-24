//! Key chords, parsed once at the edge into [`Chord`] (port of omp
//! `crates/natives/src/desktop/keys.rs`).

use std::borrow::Cow;
use std::fmt;
use std::str::FromStr;

use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// A modifier key.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Modifier {
    Ctrl,
    Alt,
    Shift,
    /// Command on macOS, Super elsewhere.
    Meta,
}

impl Modifier {
    const ALL: [Self; 4] = [Self::Ctrl, Self::Alt, Self::Shift, Self::Meta];

    const fn bit(self) -> u8 {
        match self {
            Self::Ctrl => 1,
            Self::Alt => 2,
            Self::Shift => 4,
            Self::Meta => 8,
        }
    }

    const fn name(self) -> &'static str {
        match self {
            Self::Ctrl => "ctrl",
            Self::Alt => "alt",
            Self::Shift => "shift",
            Self::Meta => "meta",
        }
    }
}

/// A set of held modifiers.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Modifiers(u8);

impl Modifiers {
    pub const NONE: Self = Self(0);

    #[must_use]
    pub const fn contains(self, modifier: Modifier) -> bool {
        self.0 & modifier.bit() != 0
    }

    #[must_use]
    pub const fn with(self, modifier: Modifier) -> Self {
        Self(self.0 | modifier.bit())
    }

    /// The held modifiers in press order: ctrl, alt, shift, meta.
    pub fn iter(self) -> impl Iterator<Item = Modifier> {
        Modifier::ALL
            .into_iter()
            .filter(move |modifier| self.contains(*modifier))
    }
}

impl Serialize for Modifiers {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_seq(self.iter())
    }
}

impl<'de> Deserialize<'de> for Modifiers {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let list = Vec::<Modifier>::deserialize(deserializer)?;
        list.into_iter().try_fold(Self::NONE, |held, modifier| {
            if held.contains(modifier) {
                Err(serde::de::Error::custom(KeyError::DuplicateModifier {
                    modifier,
                }))
            } else {
                Ok(held.with(modifier))
            }
        })
    }
}

/// A function key, F1 through F24.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FunctionKey(u8);

impl FunctionKey {
    #[must_use]
    pub const fn number(self) -> u8 {
        self.0
    }
}

/// A key that is not a modifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Key {
    Enter,
    Escape,
    Tab,
    Space,
    Backspace,
    Delete,
    Insert,
    Home,
    End,
    PageUp,
    PageDown,
    Up,
    Down,
    Left,
    Right,
    CapsLock,
    NumLock,
    PrintScreen,
    Function(FunctionKey),
    /// The key that types this character, lowercased.
    Char(char),
}

/// A chord component: a modifier or a key.
#[derive(Clone, Copy)]
enum Part {
    Modifier(Modifier),
    Key(Key),
}

/// Names a chord component takes, ignoring ASCII case.
const NAMES: &[(&str, Part)] = &[
    ("ctrl", Part::Modifier(Modifier::Ctrl)),
    ("control", Part::Modifier(Modifier::Ctrl)),
    ("shift", Part::Modifier(Modifier::Shift)),
    ("alt", Part::Modifier(Modifier::Alt)),
    ("option", Part::Modifier(Modifier::Alt)),
    ("meta", Part::Modifier(Modifier::Meta)),
    ("cmd", Part::Modifier(Modifier::Meta)),
    ("command", Part::Modifier(Modifier::Meta)),
    ("super", Part::Modifier(Modifier::Meta)),
    ("win", Part::Modifier(Modifier::Meta)),
    ("windows", Part::Modifier(Modifier::Meta)),
    ("enter", Part::Key(Key::Enter)),
    ("return", Part::Key(Key::Enter)),
    ("esc", Part::Key(Key::Escape)),
    ("escape", Part::Key(Key::Escape)),
    ("tab", Part::Key(Key::Tab)),
    ("space", Part::Key(Key::Space)),
    ("backspace", Part::Key(Key::Backspace)),
    ("delete", Part::Key(Key::Delete)),
    ("del", Part::Key(Key::Delete)),
    ("insert", Part::Key(Key::Insert)),
    ("home", Part::Key(Key::Home)),
    ("end", Part::Key(Key::End)),
    ("pageup", Part::Key(Key::PageUp)),
    ("pagedown", Part::Key(Key::PageDown)),
    ("up", Part::Key(Key::Up)),
    ("arrowup", Part::Key(Key::Up)),
    ("down", Part::Key(Key::Down)),
    ("arrowdown", Part::Key(Key::Down)),
    ("left", Part::Key(Key::Left)),
    ("arrowleft", Part::Key(Key::Left)),
    ("right", Part::Key(Key::Right)),
    ("arrowright", Part::Key(Key::Right)),
    ("capslock", Part::Key(Key::CapsLock)),
    ("numlock", Part::Key(Key::NumLock)),
    ("printscreen", Part::Key(Key::PrintScreen)),
    ("printscr", Part::Key(Key::PrintScreen)),
];

fn part(name: &str) -> Result<Part, KeyError> {
    if let Some((_, part)) = NAMES
        .iter()
        .find(|(known, _)| known.eq_ignore_ascii_case(name))
    {
        return Ok(*part);
    }
    if let Some(key) = function_key(name) {
        return Ok(Part::Key(Key::Function(key)));
    }
    let mut chars = name.chars();
    match (chars.next(), chars.next()) {
        (Some(character), None) => Ok(Part::Key(Key::Char(
            character.to_lowercase().next().unwrap_or(character),
        ))),
        _ => Err(KeyError::Unknown {
            name: name.to_owned(),
        }),
    }
}

fn function_key(name: &str) -> Option<FunctionKey> {
    let number = name
        .strip_prefix('f')
        .or_else(|| name.strip_prefix('F'))?
        .parse::<u8>()
        .ok()?;
    (1..=24).contains(&number).then_some(FunctionKey(number))
}

/// Modifiers held while one key is pressed, or the modifiers alone.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Chord {
    pub modifiers: Modifiers,
    /// `None`: the chord presses and releases its modifiers alone.
    pub key: Option<Key>,
}

impl FromStr for Chord {
    type Err = KeyError;

    /// Parses `cmd+shift+p`: `+`-separated names, at most one non-modifier.
    fn from_str(chord: &str) -> Result<Self, KeyError> {
        chord.split('+').map(str::trim).try_fold(
            Self {
                modifiers: Modifiers::NONE,
                key: None,
            },
            |held, name| {
                if name.is_empty() {
                    return Err(KeyError::Empty {
                        chord: chord.to_owned(),
                    });
                }
                held.add(part(name)?)
            },
        )
    }
}

impl Chord {
    fn add(self, part: Part) -> Result<Self, KeyError> {
        match (part, self.key) {
            (Part::Modifier(modifier), _) if self.modifiers.contains(modifier) => {
                Err(KeyError::DuplicateModifier { modifier })
            }
            (Part::Modifier(modifier), key) => Ok(Self {
                modifiers: self.modifiers.with(modifier),
                key,
            }),
            (Part::Key(key), None) => Ok(Self {
                modifiers: self.modifiers,
                key: Some(key),
            }),
            (Part::Key(second), Some(first)) => Err(KeyError::TwoKeys {
                first: KeyName(first).to_string(),
                second: KeyName(second).to_string(),
            }),
        }
    }
}

struct KeyName(Key);

impl fmt::Display for KeyName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Key::Enter => f.write_str("enter"),
            Key::Escape => f.write_str("escape"),
            Key::Tab => f.write_str("tab"),
            Key::Space => f.write_str("space"),
            Key::Backspace => f.write_str("backspace"),
            Key::Delete => f.write_str("delete"),
            Key::Insert => f.write_str("insert"),
            Key::Home => f.write_str("home"),
            Key::End => f.write_str("end"),
            Key::PageUp => f.write_str("pageup"),
            Key::PageDown => f.write_str("pagedown"),
            Key::Up => f.write_str("up"),
            Key::Down => f.write_str("down"),
            Key::Left => f.write_str("left"),
            Key::Right => f.write_str("right"),
            Key::CapsLock => f.write_str("capslock"),
            Key::NumLock => f.write_str("numlock"),
            Key::PrintScreen => f.write_str("printscreen"),
            Key::Function(key) => write!(f, "f{}", key.number()),
            Key::Char(character) => write!(f, "{character}"),
        }
    }
}

impl fmt::Display for Chord {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for modifier in self.modifiers.iter() {
            if !first {
                f.write_str("+")?;
            }
            f.write_str(modifier.name())?;
            first = false;
        }
        if let Some(key) = self.key {
            if !first {
                f.write_str("+")?;
            }
            KeyName(key).fmt(f)?;
        }
        Ok(())
    }
}

impl Serialize for Chord {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_str(self)
    }
}

impl<'de> Deserialize<'de> for Chord {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Cow::<'de, str>::deserialize(deserializer)?
            .parse()
            .map_err(serde::de::Error::custom)
    }
}

/// Why a chord did not parse.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum KeyError {
    #[error("chord {chord:?} has an empty component; nothing was sent")]
    Empty { chord: String },
    #[error("unknown key {name:?}; nothing was sent")]
    Unknown { name: String },
    #[error("modifier {} appears twice; nothing was sent", .modifier.name())]
    DuplicateModifier { modifier: Modifier },
    #[error("a chord presses one key with its modifiers, not {first} and {second}; send one key step per key; nothing was sent")]
    TwoKeys { first: String, second: String },
}

#[cfg(test)]
mod tests {
    use super::*;

    fn chord(modifiers: &[Modifier], key: Option<Key>) -> Chord {
        Chord {
            modifiers: modifiers
                .iter()
                .fold(Modifiers::NONE, |held, modifier| held.with(*modifier)),
            key,
        }
    }

    #[test]
    fn every_alias_parses_to_its_key() {
        let cases: [(&[&str], Chord); 11] = [
            (
                &["cmd", "META", "super", "win", "windows", "command"],
                chord(&[Modifier::Meta], None),
            ),
            (&["option", "alt"], chord(&[Modifier::Alt], None)),
            (&["control", "Ctrl"], chord(&[Modifier::Ctrl], None)),
            (&["enter", "return"], chord(&[], Some(Key::Enter))),
            (&["esc", "Escape"], chord(&[], Some(Key::Escape))),
            (&["delete", "del"], chord(&[], Some(Key::Delete))),
            (&["up", "arrowup"], chord(&[], Some(Key::Up))),
            (&["down", "arrowdown"], chord(&[], Some(Key::Down))),
            (&["left", "arrowleft"], chord(&[], Some(Key::Left))),
            (&["right", "arrowright"], chord(&[], Some(Key::Right))),
            (
                &["printscreen", "printscr"],
                chord(&[], Some(Key::PrintScreen)),
            ),
        ];
        for (aliases, expected) in cases {
            for alias in aliases {
                assert_eq!(alias.parse::<Chord>(), Ok(expected), "{alias}");
            }
        }
    }

    #[test]
    fn a_chord_holds_its_modifiers_around_one_key() {
        assert_eq!(
            "cmd + Shift+P".parse::<Chord>(),
            Ok(chord(
                &[Modifier::Meta, Modifier::Shift],
                Some(Key::Char('p'))
            ))
        );
        assert_eq!(
            "ctrl+f12".parse::<Chord>(),
            Ok(chord(
                &[Modifier::Ctrl],
                Some(Key::Function(FunctionKey(12)))
            ))
        );
        assert_eq!(
            "shift+meta+ctrl+é".parse::<Chord>().map(|c| c.to_string()),
            Ok("ctrl+shift+meta+é".to_owned())
        );
    }

    #[test]
    fn malformed_chords_are_refused() {
        assert_eq!(
            "ctrl++".parse::<Chord>(),
            Err(KeyError::Empty {
                chord: "ctrl++".to_owned()
            })
        );
        assert_eq!(
            "garbage".parse::<Chord>(),
            Err(KeyError::Unknown {
                name: "garbage".to_owned()
            })
        );
        assert_eq!(
            "f25".parse::<Chord>(),
            Err(KeyError::Unknown {
                name: "f25".to_owned()
            })
        );
        assert_eq!(
            "cmd+command+s".parse::<Chord>(),
            Err(KeyError::DuplicateModifier {
                modifier: Modifier::Meta
            })
        );
        assert_eq!(
            "a+b".parse::<Chord>(),
            Err(KeyError::TwoKeys {
                first: "a".to_owned(),
                second: "b".to_owned()
            })
        );
    }

    #[test]
    fn chords_decode_from_json_strings() {
        assert_eq!(
            serde_json::from_str::<Chord>("\"cmd+s\"").ok(),
            Some(chord(&[Modifier::Meta], Some(Key::Char('s'))))
        );
        assert!(serde_json::from_str::<Chord>("\"cmd+\"").is_err());
    }
}
