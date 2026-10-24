//! The resolution of the cvars (docs/control.md S4): the model
//! `bend/cvar.bend` (`refusal`, `value`, `layered`, `tog`, `check`,
//! `written`, `document`), entry `bend/ffi_cvar_layers.bend`, laws
//! `laws/cvar.bend` and `laws/cvar_layers.bend`.
//!
//! The model sees numbers: the caller numbers the cvars, and a value is a
//! Bool (a toggle flips it) or a number, the caller's reference to a value
//! it keeps. A value crosses with the type of its cvar when it has that
//! type, with the other type when it does not (the caller reads its own
//! values' syntax); the model decides everything else. Every request is
//! the caller's own encoding, so a failure is an inconsistent build
//! ([`expect_core`]).

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry};

/// A value: a Bool, or the caller's reference to a value of another type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Val {
    Nat(u64),
    Bool(bool),
}

/// The type of a cvar: Bool, or any other (a [`Val::Nat`] reference).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ty {
    Nat,
    Bool,
}

/// A declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Decl {
    pub id: u64,
    pub ty: Ty,
    /// Local (each agent may have its own value), else Global.
    pub local: bool,
    pub persist: bool,
    pub replicate: bool,
    pub init: Val,
}

/// A set: cvar `id` takes `val`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bind {
    pub id: u64,
    pub val: Val,
}

/// An agent of a family: its profile and its own sets.
#[derive(Clone, Copy, Debug)]
pub struct Agent<'a> {
    pub profile: &'a [Bind],
    pub sets: &'a [Bind],
}

/// The layer a set goes to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Layer {
    /// settings.json and config.cfg.
    Config,
    /// A profile or an agent's own sets.
    Agent,
}

/// The flag [`written`] selects.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Flag {
    Persist,
    Replicate,
}

/// The first declaration a registry drops.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refusal {
    /// It repeats this id.
    Twice(u64),
    /// Its default does not have its type.
    BadInit(u64),
}

/// The value of one cvar.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Resolved {
    /// Its value (the default when no layer sets it).
    pub value: Val,
    /// A layer sets it (else only the default applies).
    pub layered: bool,
}

/// The verdict on a toggle.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Toggle {
    Undeclared,
    /// A Global cvar, in an agent layer.
    Global,
    /// Its value is not a Bool.
    NotBool,
    /// The set that flips it.
    Flip(Bind),
}

/// The verdict on a set.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Check {
    Undeclared,
    /// A Global cvar, in an agent layer.
    Global,
    /// A value of the wrong type.
    BadType,
    Valid,
}

fn val(w: &mut Writer, v: Val) {
    match v {
        Val::Nat(n) => w.tag(0).nat(n),
        Val::Bool(b) => w.tag(1).bool(b),
    };
}

fn decls(w: &mut Writer, decls: &[Decl]) {
    w.count(decls.len());
    for d in decls {
        w.nat(d.id)
            .tag(match d.ty {
                Ty::Nat => 0,
                Ty::Bool => 1,
            })
            .tag(u32::from(d.local))
            .bool(d.persist)
            .bool(d.replicate);
        val(w, d.init);
    }
}

fn binds(w: &mut Writer, binds: &[Bind]) {
    w.count(binds.len());
    for b in binds {
        w.nat(b.id);
        val(w, b.val);
    }
}

fn family(w: &mut Writer, family: &[Agent<'_>]) {
    w.count(family.len());
    for a in family {
        binds(w, a.profile);
        binds(w, a.sets);
    }
}

fn layer(w: &mut Writer, layer: Layer) {
    w.tag(match layer {
        Layer::Config => 0,
        Layer::Agent => 1,
    });
}

fn read_val(r: &mut Reader<'_>) -> Result<Val, WireError> {
    Ok(match r.tag_of(2, "a value")? {
        0 => Val::Nat(r.nat()?),
        _ => Val::Bool(r.bool()?),
    })
}

fn read_mval(r: &mut Reader<'_>) -> Result<Option<Val>, WireError> {
    Ok(if r.maybe()? { Some(read_val(r)?) } else { None })
}

fn read_bind(r: &mut Reader<'_>) -> Result<Bind, WireError> {
    let id = r.nat()?;
    Ok(Bind {
        id,
        val: read_val(r)?,
    })
}

fn read_binds(r: &mut Reader<'_>) -> Result<Vec<Bind>, WireError> {
    let count = r.count()?;
    (0..count).map(|_| read_bind(r)).collect()
}

/// Send the request `w` holds and read its reply with `read`.
fn ask<T>(w: &mut Writer, read: impl FnOnce(&mut Reader<'_>) -> Result<T, WireError>) -> T {
    let request = expect_core(Entry::CvarLayers, w.finish());
    let reply = expect_core(Entry::CvarLayers, call(Entry::CvarLayers, &request));
    expect_core(
        Entry::CvarLayers,
        Reader::reply(&reply).and_then(|mut r| {
            let out = read(&mut r)?;
            r.end()?;
            Ok(out)
        }),
    )
}

/// The first declaration of `decls` a registry drops (`Cv.refusal`): a
/// second declaration of an id, or a default of the wrong type; `None`
/// when every declaration is kept.
#[must_use]
pub fn refusal(table: &[Decl]) -> Option<Refusal> {
    let mut w = Writer::new();
    w.tag(0);
    decls(&mut w, table);
    ask(&mut w, |r| {
        Ok(match r.tag_of(3, "a refusal")? {
            0 => None,
            1 => Some(Refusal::Twice(r.nat()?)),
            _ => Some(Refusal::BadInit(r.nat()?)),
        })
    })
}

/// The value of each cvar of `table`, in order, for the last agent of the
/// family chain `chain` (root first) over config.cfg `cfg` (`Cv.value`,
/// `Cv.layered`).
#[must_use]
pub fn values(table: &[Decl], cfg: &[Bind], chain: &[Agent<'_>]) -> Vec<Resolved> {
    let mut w = Writer::new();
    w.tag(1);
    decls(&mut w, table);
    binds(&mut w, cfg);
    family(&mut w, chain);
    ask(&mut w, |r| {
        let count = r.count()?;
        (0..count)
            .map(|_| {
                let value = read_mval(r)?.ok_or(WireError::Malformed {
                    at: 0,
                    expected: "the value of a declared cvar",
                })?;
                let layered = read_mval(r)?.is_some();
                Ok(Resolved { value, layered })
            })
            .collect()
    })
}

/// A toggle of cvar `id` into `into` by the last agent of `chain`
/// (`Cv.tog`).
#[must_use]
pub fn toggle(table: &[Decl], cfg: &[Bind], chain: &[Agent<'_>], into: Layer, id: u64) -> Toggle {
    let mut w = Writer::new();
    w.tag(2);
    decls(&mut w, table);
    binds(&mut w, cfg);
    family(&mut w, chain);
    layer(&mut w, into);
    w.nat(id);
    ask(&mut w, |r| {
        Ok(match r.tag_of(4, "a toggle verdict")? {
            0 => Toggle::Undeclared,
            1 => Toggle::Global,
            2 => Toggle::NotBool,
            _ => Toggle::Flip(read_bind(r)?),
        })
    })
}

/// The verdict on the set `set` in a layer `into` (`Cv.check`).
#[must_use]
pub fn check(table: &[Decl], into: Layer, set: Bind) -> Check {
    let mut w = Writer::new();
    w.tag(3);
    decls(&mut w, table);
    layer(&mut w, into);
    w.nat(set.id);
    val(&mut w, set.val);
    ask(&mut w, |r| {
        Ok(match r.tag_of(4, "a set verdict")? {
            0 => Check::Undeclared,
            1 => Check::Global,
            2 => Check::BadType,
            _ => Check::Valid,
        })
    })
}

/// The sets of `sets` an agent writes to its cfg ([`Flag::Persist`]) or
/// replicates ([`Flag::Replicate`]), in order (`Cv.written`).
#[must_use]
pub fn written(table: &[Decl], sets: &[Bind], flag: Flag) -> Vec<Bind> {
    let mut w = Writer::new();
    w.tag(4);
    decls(&mut w, table);
    binds(&mut w, sets);
    w.tag(match flag {
        Flag::Persist => 0,
        Flag::Replicate => 1,
    });
    ask(&mut w, read_binds)
}

/// The config layer of a settings document (`Cv.document`): per
/// declaration, the set of `merged` (a Local cvar) or of `global` (a
/// Global cvar) when it is valid.
#[must_use]
pub fn document(table: &[Decl], merged: &[Bind], global: &[Bind]) -> Vec<Bind> {
    let mut w = Writer::new();
    w.tag(5);
    decls(&mut w, table);
    binds(&mut w, merged);
    binds(&mut w, global);
    ask(&mut w, read_binds)
}
