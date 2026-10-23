//! The expansion of the command language (docs/control.md S4.4, S4.5): the
//! model `bend/cvar.bend` (`expand`, `press`), entry `bend/ffi_cvar.bend`.
//!
//! The model sees numbers: an alias is its place in the table (a name the
//! table does not hold gets a number past it), and every command that is not
//! a run of an alias is kept here and crosses as its place in [`Opaque`]
//! (the model passes such commands through unchanged). The reply's numbers
//! map back to the names and the commands.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_types::cvar::{Aliases, Binds, Command, ExpandError};

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Stepper};

/// The numbers of the alias names, and the commands kept aside.
#[derive(Debug, Default)]
struct Opaque {
    names: Vec<String>,
    numbers: HashMap<String, usize>,
    kept: Vec<Command>,
}

impl Opaque {
    /// The table's aliases take the numbers 0.. in table order.
    fn of(aliases: &Aliases) -> Self {
        let mut opaque = Opaque::default();
        for (name, _) in aliases.iter() {
            opaque.number(name);
        }
        opaque
    }

    fn number(&mut self, name: &str) -> usize {
        if let Some(n) = self.numbers.get(name) {
            return *n;
        }
        let n = self.names.len();
        self.names.push(name.to_owned());
        self.numbers.insert(name.to_owned(), n);
        n
    }

    /// `commands` as the model's list: a run is `CRun{n}` (tag 2), any
    /// other command `CToggle{i}` (tag 1) with `i` its place in `kept`.
    fn commands(&mut self, w: &mut Writer, commands: &[Command]) {
        w.count(commands.len());
        for command in commands {
            match command {
                Command::Run { alias } => {
                    let n = self.number(alias);
                    w.tag(2).count(n);
                }
                Command::Set { .. }
                | Command::Toggle { .. }
                | Command::Alias { .. }
                | Command::Bind { .. }
                | Command::Action { .. } => {
                    w.tag(1).count(self.kept.len());
                    self.kept.push(command.clone());
                }
            }
        }
    }

    fn aliases(&mut self, w: &mut Writer, aliases: &Aliases) {
        w.count(aliases.len());
        for (name, body) in aliases.iter() {
            let n = self.number(name);
            w.count(n);
            self.commands(w, body);
        }
    }

    fn name(&self, n: u64) -> Result<String, WireError> {
        usize::try_from(n)
            .ok()
            .and_then(|n| self.names.get(n))
            .cloned()
            .ok_or(WireError::Malformed {
                at: 0,
                expected: "the number of an alias",
            })
    }

    /// The expansion the reply holds (the model's `Exp`).
    fn expansion(&self, reply: &str) -> Result<Result<Vec<Command>, ExpandError>, WireError> {
        let mut r = Reader::reply(reply)?;
        let tag = r.tag_of(3, "an expansion")?;
        let out = if tag == 0 {
            let count = r.count()?;
            let mut commands = Vec::with_capacity(count);
            for _ in 0..count {
                if r.tag_of(4, "a command")? != 1 {
                    return Err(WireError::Malformed {
                        at: 0,
                        expected: "a command kept aside (an expansion runs no alias)",
                    });
                }
                let i = r.count()?;
                let command = self.kept.get(i).ok_or(WireError::Malformed {
                    at: 0,
                    expected: "the place of a command kept aside",
                })?;
                commands.push(command.clone());
            }
            Ok(commands)
        } else if tag == 1 {
            Err(ExpandError::Cycle {
                alias: self.name(r.nat()?)?,
            })
        } else {
            Err(ExpandError::Unknown {
                alias: self.name(r.nat()?)?,
            })
        };
        r.end()?;
        Ok(out)
    }
}

/// `commands` with every run of an alias replaced by its commands: the top
/// level and one level per alias of the table; the first error, left to
/// right, stops it (`bend/cvar.bend` `expand`).
///
/// # Errors
///
/// [`ExpandError::Cycle`] for a nest deeper than the table,
/// [`ExpandError::Unknown`] for a run of an alias that does not exist.
pub fn expand(commands: &[Command], aliases: &Aliases) -> Result<Vec<Command>, ExpandError> {
    let mut opaque = Opaque::of(aliases);
    let mut w = Writer::new();
    opaque.aliases(&mut w, aliases);
    opaque.commands(&mut w, commands);
    let request = expect_core(Entry::Cvar, w.finish());
    let reply = expect_core(Entry::Cvar, call(Entry::Cvar, &request));
    expect_core(Entry::Cvar, opaque.expansion(&reply))
}

/// The presses of a bind table: the binds and the aliases live in the
/// compiled core, so a press sends only its key. A clone shares the table.
#[derive(Debug, Clone)]
pub struct Presses {
    opaque: Arc<Opaque>,
    /// The number of each bound key (keys bound twice keep one number).
    keys: Arc<HashMap<String, usize>>,
    table: Arc<Mutex<Stepper>>,
}

impl Presses {
    /// The presses of `binds` with the alias table `aliases`.
    #[must_use]
    pub fn new(binds: &Binds, aliases: &Aliases) -> Self {
        let mut opaque = Opaque::of(aliases);
        let mut keys: HashMap<String, usize> = HashMap::new();
        let mut w = Writer::new();
        let count = binds.iter().count();
        w.count(count);
        for (key, body) in binds.iter() {
            let next = keys.len();
            let n = *keys.entry(key.to_owned()).or_insert(next);
            w.count(n);
            opaque.commands(&mut w, body);
        }
        opaque.aliases(&mut w, aliases);
        let request = expect_core(Entry::Cvar, w.finish());
        let (table, reply) = expect_core(Entry::Cvar, Stepper::open(Entry::Cvar, &request));
        expect_core(Entry::Cvar, Reader::reply(&reply).and_then(Reader::end));
        Presses {
            opaque: Arc::new(opaque),
            keys: Arc::new(keys),
            table: Arc::new(Mutex::new(table)),
        }
    }

    /// The commands a press of `key` runs: its first bind's commands,
    /// expanded (`bend/cvar.bend` `press`); none for an unbound key.
    ///
    /// # Errors
    ///
    /// As [`expand`].
    pub fn press(&self, key: &str) -> Result<Vec<Command>, ExpandError> {
        // An unbound key takes a number no bind has.
        let n = self.keys.get(key).copied().unwrap_or(self.keys.len());
        let mut w = Writer::new();
        w.count(n);
        let event = expect_core(Entry::Cvar, w.finish());
        let reply = {
            let mut table = self.table.lock().unwrap_or_else(PoisonError::into_inner);
            expect_core(Entry::Cvar, table.step(&event))
        };
        expect_core(Entry::Cvar, self.opaque.expansion(&reply))
    }
}

#[cfg(test)]
mod tests {
    use super::{expand, Presses};
    use eukhe_types::cvar::{Aliases, Binds, Command, ExpandError};

    fn set(id: &str, value: &str) -> Command {
        Command::Set {
            id: id.to_owned(),
            value: value.to_owned(),
        }
    }

    fn run(alias: &str) -> Command {
        Command::Run {
            alias: alias.to_owned(),
        }
    }

    /// The glue the laws do not see: names and commands map to the model's
    /// numbers and back (the rule itself is pinned by `laws/cvar.bend` S4).
    #[test]
    fn names_and_commands_cross_the_core_and_back() {
        let mut aliases = Aliases::default();
        aliases.define("a".to_owned(), vec![set("x", "1"), run("b")]);
        aliases.define(
            "b".to_owned(),
            vec![Command::Action {
                id: "app.clear".to_owned(),
            }],
        );
        aliases.define("loop".to_owned(), vec![run("loop")]);
        assert_eq!(
            [
                expand(&[run("a"), set("z", "é 3")], &aliases),
                expand(&[run("loop")], &aliases),
                expand(&[set("q", "1"), run("missing"), run("loop")], &aliases),
            ],
            [
                Ok(vec![
                    set("x", "1"),
                    Command::Action {
                        id: "app.clear".to_owned()
                    },
                    set("z", "é 3"),
                ]),
                Err(ExpandError::Cycle {
                    alias: "loop".to_owned()
                }),
                Err(ExpandError::Unknown {
                    alias: "missing".to_owned()
                }),
            ]
        );
        let mut binds = Binds::default();
        binds.push("f1".to_owned(), vec![run("a")]);
        binds.push("f1".to_owned(), vec![set("ignored", "1")]);
        binds.push("f2".to_owned(), vec![run("gone")]);
        let presses = Presses::new(&binds, &aliases);
        assert_eq!(
            [
                presses.press("f1"),
                presses.press("f2"),
                presses.press("f9")
            ],
            [
                expand(&[run("a")], &aliases),
                Err(ExpandError::Unknown {
                    alias: "gone".to_owned()
                }),
                Ok(Vec::new()),
            ]
        );
    }
}
