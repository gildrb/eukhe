# default_model: the model a new session runs on when nothing requests
# one, and the notice the session shows when the saved default model
# (`defaultProvider`/`defaultModel`) does not run. The Rust code is
# crates/eukhe-core/src/durable/models.rs (`resolve_session_model` and
# `resolve_open_model`) over `saved_default_miss` in
# crates/eukhe-core/src/models/resolver.rs.
#
# A resolution has the saved default (none, or the model m), whether the
# model catalog has m, whether m's provider has credentials, whether a set
# `enabledModels` scope leaves m out, and the model the startup chain picks
# without m (none, or another model n). The checks run in this order:
#
#   - nothing saved: the chain picks a model, with nothing to say, or
#     there is no model;
#   - a catalog without m: the chain picks another model with the reason
#     0 (not in the catalog);
#   - m's provider without credentials: a typed error with the reason 1
#     (no credentials); the session never moves to another provider;
#   - a scope that leaves m out: the chain picks another model with the
#     reason 2 (not in the scope);
#   - else the session runs on m.
#
# When no other model can take the place of a saved default that does not
# run, the resolution is the typed error with its reason.
#
# A session opens on the resolution. A typed error opens it with no model
# and the notice of the error; a substitution opens it on the other model
# and the notice of the substitution.

import Base

# The saved default.
type Saved is Data:
  NoDefault{}
  Default{m: Nat}

# The model the chain picks without the saved default.
type Next is Data:
  NoNext{}
  Next{n: Nat}

# One resolution.
type In is Data:
  In{saved: Saved, cat: Bool, key: Bool, out: Bool, next: Next}

# Why the saved default does not run.
type Reason is Data:
  NotInCatalog{}
  NoCredentials{}
  NotInScope{}

# The key of a notice: the saved default and the reason.
type Key is Data:
  K{m: Nat, r: Reason}

# The model a session runs on: the saved default, or another model.
type Pick is Data:
  Saved{}
  Other{n: Nat}

# The saved default runs, or another model runs in its place.
type Sub is Data:
  Kept{}
  Swapped{k: Key}

# What the resolver answers: a model, no model, or the typed error.
type Res is Data:
  Runs{p: Pick, s: Sub}
  Nothing{}
  Refused{k: Key}

# The model a session opens on: a model, or none.
type Run is Data:
  On{p: Pick}
  Idle{}

# An opened session: the model it runs on and its notices.
type Session is Data:
  Session{run: Run, notes: List<&2, Key>}

# The resolver
# ------------

# the chain's pick, with nothing saved
def chain(next: Next) -> Res:
  match next:
    case NoNext{}:
      Nothing{}
    case Next{n}:
      Runs{Other{n}, Kept{}}

# another model in place of the saved default, for the key k
def swap(k: Key, next: Next) -> Res:
  match next:
    case NoNext{}:
      Refused{k}
    case Next{n}:
      Runs{Other{n}, Swapped{k}}

# the saved default m in a scope that leaves it out, or not
def scoped(+m: Nat, out: Bool, next: Next) -> Res:
  match out:
    case True{}:
      swap(K{m, NotInScope{}}, next)
    case False{}:
      Runs{Saved{}, Kept{}}

# the saved default m with or without credentials
def keyed(+m: Nat, key: Bool, out: Bool, next: Next) -> Res:
  match key:
    case True{}:
      scoped(m, out, next)
    case False{}:
      Refused{K{m, NoCredentials{}}}

# the saved default m in the catalog, or not
def listed_in(+m: Nat, cat: Bool, key: Bool, out: Bool, next: Next) -> Res:
  match cat:
    case True{}:
      keyed(m, key, out, next)
    case False{}:
      swap(K{m, NotInCatalog{}}, next)

# what the resolver answers for x
def resolve(x: In) -> Res:
  match x:
    case In{saved, cat, key, out, next}:
      match saved:
        case NoDefault{}:
          chain(next)
        case Default{m}:
          listed_in(m, cat, key, out, next)

# The session
# -----------

def noted(s: Sub) -> List<&2, Key>:
  match s:
    case Kept{}:
      Nil{}
    case Swapped{k}:
      [k]

# the session that opens on the answer r
def open(r: Res) -> Session:
  match r:
    case Runs{p, s}:
      Session{On{p}, noted(s)}
    case Nothing{}:
      Session{Idle{}, Nil{}}
    case Refused{k}:
      Session{Idle{}, [k]}

def Session.run(s: Session) -> Run:
  match s:
    case Session{run, notes}:
      run

def Session.notes(s: Session) -> List<&2, Key>:
  match s:
    case Session{run, notes}:
      notes
