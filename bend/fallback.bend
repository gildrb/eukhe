# fallback: the model a run goes on with after its model failed (Rust:
# eukhe-core durable/models/fallback.rs, asked by the provider runtime,
# durable/models/provider.rs, when a request gives up). The candidates are
# the models the user configured whose providers have credentials (the
# `enabledModels` scope, the default model, then the models of the chat
# roles), in that order; the defaults are the default model of every
# other provider the user is signed in to (credentials present, the
# allowlist permits), tried after every candidate; the tried models are
# those the request already left (its own model first). The failure says
# why the model cannot go on:
#
#   - Failed{n, retries}: the n-th retryable failure in a row of the
#     model, with the run's `retries` (`retry.maxRetries`, 0 when retries
#     are off): while n <= retries the run's own retry goes on (Keep);
#   - Login{}: the model's provider login expired and its refresh failed;
#   - Quota{until}: the provider's usage limit holds until `until` (epoch
#     ms);
#   - Unset{}: no model was chosen.
#
# Past a Keep, the run switches to the first candidate in order that it
# has not tried, then to the first such default. With none left, a usage
# limit waits for its reset; every other failure ends the request, and
# the end carries the failure: the cause the run's end report names.
# Pure: no IO, no @unsafe.

import Base

# why the model cannot go on
type Why is Data:
  Failed{n: Nat, retries: Nat}
  Login{}
  Quota{until: Nat}
  Unset{}

# what the run does
type Choice is Data:
  Keep{}
  Switch{m: Nat}
  Hold{until: Nat}
  End{k: Why}

# one decision: the failure, the candidates in order, the signed-in
# defaults in order, the tried models
type In is Data:
  In{k: Why, cands: List<&2, Nat>, defaults: List<&2, Nat>, tried: List<&2, Nat>}

# the same model
def same(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 0n 1n+q:
      False{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      same(p, q)

# m is among the tried models
def tried_has(+m: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(same(m, x), tried_has(m, t))

# the run's own retry goes on
def kept(k: Why) -> Bool:
  match k:
    case Failed{n, retries}:
      Nat.is_le(n, retries)
    case Login{}:
      False{}
    case Quota{until}:
      False{}
    case Unset{}:
      False{}

# no candidate left: a usage limit waits for its reset, else the end with
# the failure
def none_left(k: Why) -> Choice:
  match k:
    case Failed{n, retries}:
      End{Failed{n, retries}}
    case Login{}:
      End{Login{}}
    case Quota{until}:
      Hold{until}
    case Unset{}:
      End{Unset{}}

def pick(+c: Nat, hit: Bool, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      rest
    case False{}:
      Some{c}

# the first candidate not tried
def first(cands: List<&2, Nat>, +tried: List<&2, Nat>) -> Maybe<&2, Nat>:
  match cands:
    case Nil{}:
      None{}
    case +c <> t:
      pick(c, tried_has(c, tried), first(t, tried))

def next.of(k: Why, m: Maybe<&2, Nat>) -> Choice:
  match m:
    case None{}:
      none_left(k)
    case Some{c}:
      Switch{c}

# the first candidate not tried, else what no candidate left does
def next(cands: List<&2, Nat>, tried: List<&2, Nat>, k: Why) -> Choice:
  next.of(k, first(cands, tried))

def choose.if(k: Why, cands: List<&2, Nat>, tried: List<&2, Nat>, keep: Bool) -> Choice:
  match keep:
    case True{}:
      Keep{}
    case False{}:
      next(cands, tried, k)

# what the run does after its model failed: the candidates, then the
# signed-in defaults
def choose(x: In) -> Choice:
  match x:
    case In{+k, cands, defaults, tried}:
      choose.if(k, List.append(&2, Nat, cands, defaults), tried, kept(k))
