//! The quirks rulebook (`bend/infer.bend` section 1, entry
//! `bend/ffi_quirks.bend`; `laws/quirks.bend`): the compiler's verdict on
//! each rule, and the lookup of a directive for a query. A rulebook is
//! numbers: each layer's targets, the directives and the values are ids the
//! caller gives. [`Book::open`] compiles one in the core's stepper, which
//! keeps it, so a lookup ships only the query.

use crate::wire::{Reader, Writer};
use crate::{Entry, Error, Stepper};

/// The layer of a rule (`If.Lay`, its wire tag). A higher layer wins.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Layer {
    Family,
    Model,
    Host,
}

impl Layer {
    const fn tag(self) -> u64 {
        match self {
            Self::Family => 0,
            Self::Model => 1,
            Self::Host => 2,
        }
    }
}

/// One rule (`If.Rule`): at `layer`, for `target`, `directive` has
/// `value`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rule {
    pub layer: Layer,
    pub target: u64,
    pub directive: u64,
    pub value: u64,
}

/// The compiler's verdict on one rule (`If.Verdict`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// The rule compiles.
    Fine,
    /// Its directive is not one of the known directives.
    UnknownDirective,
    /// It clashes with the rule of this index (the first later rule of its
    /// layer, target and directive with another value).
    ClashesWith(usize),
}

/// The targets a query names, one per layer (`If.Query`). A layer that
/// names no target takes an id that no rule targets.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Query {
    pub family: u64,
    pub model: u64,
    pub host: u64,
}

/// A rulebook that compiles, kept in the core's stepper.
#[derive(Debug)]
pub struct Book {
    stepper: Stepper,
}

impl Book {
    /// Compiles `rules` over the directives `known`: the verdict on each
    /// rule, in order, and the book when every verdict is
    /// [`Verdict::Fine`] (the rulebook compiles).
    ///
    /// # Errors
    ///
    /// [`Error`] only from an inconsistent build (see [`crate::expect_core`]),
    /// or a number past the wire's largest Nat.
    pub fn open(known: &[u64], rules: &[Rule]) -> Result<(Option<Book>, Vec<Verdict>), Error> {
        let mut request = Writer::new();
        request.count(known.len());
        for directive in known {
            request.nat(*directive);
        }
        request.count(rules.len() * 4);
        for rule in rules {
            request
                .nat(rule.layer.tag())
                .nat(rule.target)
                .nat(rule.directive)
                .nat(rule.value);
        }
        let (stepper, reply) = Stepper::open(Entry::Quirks, &request.finish()?)?;
        let mut reply = Reader::reply(&reply)?;
        let compiles = reply.bool()?;
        let count = reply.count()?;
        let mut verdicts = Vec::with_capacity(count);
        for _ in 0..count {
            verdicts.push(match reply.tag_of(3, "a verdict")? {
                0 => Verdict::Fine,
                1 => Verdict::UnknownDirective,
                _ => Verdict::ClashesWith(reply.count()?),
            });
        }
        reply.end()?;
        Ok((compiles.then_some(Book { stepper }), verdicts))
    }

    /// The value of `directive` for `query`: the rule of the highest layer
    /// whose target the query names; `None` when no rule applies.
    ///
    /// # Errors
    ///
    /// [`Error`] only from an inconsistent build (see [`crate::expect_core`]),
    /// or a number past the wire's largest Nat.
    pub fn lookup(&mut self, query: Query, directive: u64) -> Result<Option<u64>, Error> {
        let mut request = Writer::new();
        request
            .count(4)
            .nat(query.family)
            .nat(query.model)
            .nat(query.host)
            .nat(directive);
        let reply = self.stepper.step(&request.finish()?)?;
        let mut reply = Reader::reply(&reply)?;
        let value = if reply.maybe()? {
            Some(reply.nat()?)
        } else {
            None
        };
        reply.end()?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::{Book, Layer, Query, Rule, Verdict};

    /// The compiled core answers: a rulebook that compiles answers the
    /// highest layer that applies; one with a clash and an unknown
    /// directive opens no book and names both.
    #[test]
    fn the_core_compiles_and_looks_up() {
        let rule = |layer, target, directive, value| Rule {
            layer,
            target,
            directive,
            value,
        };
        let (book, verdicts) = Book::open(
            &[0, 1],
            &[
                rule(Layer::Family, 1, 0, 5),
                rule(Layer::Model, 2, 0, 7),
                rule(Layer::Host, 3, 1, 9),
            ],
        )
        .unwrap();
        let mut book = book.unwrap();
        let query = Query {
            family: 1,
            model: 2,
            host: 0,
        };
        assert_eq!(
            (
                verdicts,
                book.lookup(query, 0).unwrap(),
                book.lookup(query, 1).unwrap(),
            ),
            (vec![Verdict::Fine; 3], Some(7), None)
        );
        let (book, verdicts) = Book::open(
            &[0],
            &[
                rule(Layer::Model, 2, 0, 7),
                rule(Layer::Model, 2, 0, 8),
                rule(Layer::Host, 3, 4, 1),
            ],
        )
        .unwrap();
        assert!(book.is_none());
        assert_eq!(
            verdicts,
            vec![
                Verdict::ClashesWith(1),
                Verdict::Fine,
                Verdict::UnknownDirective
            ]
        );
    }
}
