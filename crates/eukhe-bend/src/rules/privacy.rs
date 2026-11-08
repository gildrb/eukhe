//! The outbound scrubber (`privacy.anonymizeRemote`, spec/README.md H7):
//! the models `bend/privacy/ip.bend` and `bend/privacy/token.bend`, entry
//! `bend/ffi_privacy.bend`, laws `laws/privacy/`, spec
//! `spec/harness/privacy.bend`. Its host is `eukhe-ai` `privacy`: the
//! scan of a text (which positions to ask about, which other classes
//! match there) stays in Rust; the core decides the rest.
//!
//! - The call ([`ip_ends`]): which candidate positions of one text start
//!   an IP address (an IPv6 with a digit-bearing group and three explicit
//!   groups when compressed, whose value is no loopback, unspecified, or
//!   IPv4-mapped or -compatible loopback, 0.x or 255.x; an IPv4 that is
//!   no version, loopback, 0.x or 255.x), all of them in one call.
//! - The stepper ([`Tokens`]): the token map of the daemon. A personal
//!   value's token is its index in its class, kept for the map's life; a
//!   credential's is one way (its hash, which the host writes). One step
//!   asks the tokens of one text's values, one step the values of one
//!   text's tokens.

use crate::wire::{Reader, Writer};
use crate::{call, expect_core, Entry, Error, Stepper};

/// The class of a scrubbed value (`Tk.Class`, in its wire order).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Class {
    /// A phrase of `privacy.terms`.
    Person,
    Email,
    Phone,
    /// An IPv4 or IPv6 address.
    Ip,
    /// A US social security number.
    Id,
    /// An API key, token or private key.
    Key,
    Card,
    Iban,
}

impl Class {
    /// Every class, in wire order.
    pub const ALL: [Class; 8] = [
        Class::Person,
        Class::Email,
        Class::Phone,
        Class::Ip,
        Class::Id,
        Class::Key,
        Class::Card,
        Class::Iban,
    ];

    /// The token name (`IP` in `IP_3`).
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Class::Person => "PERSON",
            Class::Email => "EMAIL",
            Class::Phone => "PHONE",
            Class::Ip => "IP",
            Class::Id => "ID",
            Class::Key => "KEY",
            Class::Card => "CARD",
            Class::Iban => "IBAN",
        }
    }

    const fn tag(self) -> u32 {
        match self {
            Class::Person => 0,
            Class::Email => 1,
            Class::Phone => 2,
            Class::Ip => 3,
            Class::Id => 4,
            Class::Key => 5,
            Class::Card => 6,
            Class::Iban => 7,
        }
    }
}

/// The longest `before` of a candidate, in bytes: the line before the
/// position, cut at most this far back (at a char boundary).
pub const BEFORE_BYTES: usize = 48;

/// The longest `rest` of a candidate, in chars: an address is at most 45
/// chars, and the grammar reads at most two chars past one.
pub const REST_CHARS: usize = 48;

/// The char that stands for a non-ASCII word char in a candidate.
pub const WORD_MARK: char = '\u{aa}';

/// The char that stands for any other non-ASCII char in a candidate.
pub const OTHER_MARK: char = '\u{a0}';

/// One candidate position of a text: the text before it and from it
/// ([`BEFORE_BYTES`], [`REST_CHARS`]), each non-ASCII char written as
/// [`WORD_MARK`] or [`OTHER_MARK`] by whether it is a word char.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Candidate {
    pub before: String,
    pub rest: String,
}

/// For each candidate, the length in chars of the IP address its `rest`
/// starts with, or `None` (`Ip.ip`). One call for all of them; no call
/// for none.
#[must_use]
pub fn ip_ends(candidates: &[Candidate]) -> Vec<Option<usize>> {
    if candidates.is_empty() {
        return Vec::new();
    }
    expect_core(Entry::Privacy, ip_ends_call(candidates))
}

fn ip_ends_call(candidates: &[Candidate]) -> Result<Vec<Option<usize>>, Error> {
    let mut request = Writer::new();
    request.count(candidates.len() * 2);
    for candidate in candidates {
        request.str(&candidate.before).str(&candidate.rest);
    }
    let reply = call(Entry::Privacy, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let count = reader.count()?;
    let mut ends = Vec::with_capacity(count);
    for _ in 0..count {
        let code = reader.count()?;
        ends.push(code.checked_sub(1));
    }
    reader.end()?;
    Ok(ends)
}

/// The token of a value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Token {
    /// A personal value's index in its class (from 1): `CLASS_<index>`.
    Mapped(u64),
    /// A credential: the host writes its one-way hash.
    OneWay,
}

/// The token map, kept in the compiled core: append-only, one index
/// space per class, for the life of this value.
#[derive(Debug)]
pub struct Tokens {
    stepper: Stepper,
    mapped: Vec<Class>,
}

impl Default for Tokens {
    fn default() -> Self {
        Self::open()
    }
}

impl Tokens {
    /// An empty map.
    #[must_use]
    pub fn open() -> Self {
        let (stepper, reply) = expect_core(Entry::Privacy, Stepper::open(Entry::Privacy, ""));
        let mapped = expect_core(Entry::Privacy, read_classes(&reply));
        Tokens { stepper, mapped }
    }

    /// The classes whose tokens map back to their values, as the core
    /// answered at open: a literal that reads as a token of one of them is
    /// a value of its class.
    #[must_use]
    pub fn mapped(&self) -> &[Class] {
        &self.mapped
    }

    /// The token of each value of one text, in order.
    ///
    /// # Errors
    ///
    /// A value is longer than the wire carries ([`crate::wire::STR_MAX`]
    /// chars): nothing was asked and the map is unchanged.
    pub fn scrub(&mut self, values: &[(Class, &str)]) -> Result<Vec<Token>, Error> {
        let mut event = Writer::new();
        event.tag(0).count(values.len());
        for (class, _) in values {
            event.tag(class.tag());
        }
        event.count(values.len());
        for (_, value) in values {
            event.str(value);
        }
        let event = event.finish()?;
        let reply = expect_core(Entry::Privacy, self.stepper.step(&event));
        Ok(expect_core(
            Entry::Privacy,
            read_tokens(&reply, values.len()),
        ))
    }

    /// The value of each token of one text, in order (`None`: no value the
    /// map holds, or a class that goes one way).
    #[must_use]
    pub fn restore(&mut self, tokens: &[(Class, u32)]) -> Vec<Option<String>> {
        let mut event = Writer::new();
        event.tag(1).count(tokens.len());
        for (class, _) in tokens {
            event.tag(class.tag());
        }
        event.count(tokens.len());
        for (_, index) in tokens {
            event.nat(u64::from(*index));
        }
        let event = expect_core(Entry::Privacy, event.finish());
        let reply = expect_core(Entry::Privacy, self.stepper.step(&event));
        expect_core(Entry::Privacy, read_values(&reply, tokens.len()))
    }
}

fn class_of(tag: u64) -> Option<Class> {
    Class::ALL
        .into_iter()
        .find(|class| u64::from(class.tag()) == tag)
}

fn read_classes(reply: &str) -> Result<Vec<Class>, Error> {
    let mut reader = Reader::reply(reply)?;
    let count = reader.count()?;
    let mut classes = Vec::with_capacity(count);
    for _ in 0..count {
        let tag = reader.nat()?;
        classes.push(class_of(tag).ok_or(crate::wire::WireError::Malformed {
            at: 0,
            expected: "a class tag",
        })?);
    }
    reader.end()?;
    Ok(classes)
}

fn read_tokens(reply: &str, expected: usize) -> Result<Vec<Token>, Error> {
    let mut reader = Reader::reply(reply)?;
    let count = reader.count()?;
    if count != expected {
        return Err(crate::wire::WireError::Malformed {
            at: 0,
            expected: "one token per value",
        }
        .into());
    }
    let mut tokens = Vec::with_capacity(count);
    for _ in 0..count {
        tokens.push(match reader.nat()? {
            0 => Token::OneWay,
            index => Token::Mapped(index),
        });
    }
    reader.end()?;
    Ok(tokens)
}

fn read_values(reply: &str, expected: usize) -> Result<Vec<Option<String>>, Error> {
    let mut reader = Reader::reply(reply)?;
    let count = reader.count()?;
    if count != expected {
        return Err(crate::wire::WireError::Malformed {
            at: 0,
            expected: "one value per token",
        }
        .into());
    }
    let mut values = Vec::with_capacity(count);
    for _ in 0..count {
        values.push(if reader.maybe()? {
            Some(reader.str()?.to_owned())
        } else {
            None
        });
    }
    reader.end()?;
    Ok(values)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn candidate(before: &str, rest: &str) -> Candidate {
        Candidate {
            before: before.to_owned(),
            rest: rest.to_owned(),
        }
    }

    /// The core decides each candidate: `::` paths, pseudo-elements,
    /// loopback and versions are no address; a public IPv4 and an IPv6 with
    /// a digit-bearing group are, to their last char.
    #[test]
    fn the_core_decides_each_candidate() {
        assert_eq!(
            ip_ends(&[
                candidate("", "a::before {"),
                candidate("a", "::before {"),
                candidate("std", "::sync::Arc"),
                candidate("http://", "127.0.0.1:5180"),
                candidate("version = \"", "1.2.3.4\""),
                candidate("", "1.2.3 x"),
                candidate("ssh deploy@", "203.0.113.7"),
                candidate("upstream [", "2001:db8::8a2e:370:7334]:443"),
                candidate("x", "\u{aa}::1:2:3"),
            ]),
            [None, None, None, None, None, None, Some(11), Some(23), None]
        );
        assert_eq!(ip_ends(&[]), Vec::<Option<usize>>::new());
    }

    /// The map: personal values take their class's next index, a value
    /// seen again keeps its index, a credential goes one way; each mapped
    /// token restores to its value, a credential's never.
    #[test]
    fn the_core_keeps_the_token_map() {
        let mut tokens = Tokens::open();
        assert_eq!(
            tokens.mapped(),
            [
                Class::Person,
                Class::Email,
                Class::Phone,
                Class::Ip,
                Class::Id
            ]
        );
        assert_eq!(
            tokens
                .scrub(&[
                    (Class::Ip, "203.0.113.7"),
                    (Class::Key, "sk-abc"),
                    (Class::Ip, "IP_1"),
                    (Class::Ip, "203.0.113.7"),
                    (Class::Email, "a@b.cd"),
                ])
                .expect("short values"),
            [
                Token::Mapped(1),
                Token::OneWay,
                Token::Mapped(2),
                Token::Mapped(1),
                Token::Mapped(1)
            ]
        );
        assert_eq!(
            tokens.restore(&[
                (Class::Ip, 2),
                (Class::Ip, 1),
                (Class::Key, 1),
                (Class::Ip, 9)
            ]),
            [
                Some("IP_1".to_owned()),
                Some("203.0.113.7".to_owned()),
                None,
                None
            ]
        );
        assert_eq!(tokens.restore(&[]), Vec::<Option<String>>::new());
    }
}
