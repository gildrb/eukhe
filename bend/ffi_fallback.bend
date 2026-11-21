# ffi_fallback: the entry of the compiled Bend core for the model a run
# goes on with after its model failed (bend/fallback.bend `choose`; Rust:
# eukhe-bend rules/fallback.rs). Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  one List<Nat>: the failure, then the count of candidates, the
#            candidates in order, the count of signed-in defaults, the
#            defaults in order, then the tried models
#            failure  0, n, retries (Failed) | 1 (Login) | 2, until
#                     (Quota) | 3 (Unset)
#   reply    0 (keep) | 1, m (switch) | 2, until (wait) | 3, failure (end,
#            with the failure it carries)
#
# Malformed input, or input left after the request, answers
# `E fallback: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./fallback.bend as F

# Decoding
# --------

# a list cut in two: the first items, then the rest
type Parts is Data:
  Parts{head: List<&2, Nat>, rest: List<&2, Nat>}

def split.cons(x: Nat, r: Maybe<&2, Parts>) -> Maybe<&2, Parts>:
  match r:
    case None{}:
      None{}
    case Some{p}:
      match p:
        case Parts{a, b}:
          Some{Parts{x <> a, b}}

# the first n items, then the rest; None when fewer than n
def split(n: Nat, xs: List<&2, Nat>) -> Maybe<&2, Parts>:
  match n:
    case 0n:
      Some{Parts{[], xs}}
    case 1n+p:
      match xs:
        case Nil{}:
          None{}
        case x <> t:
          split.cons(x, split(p, t))

def parse.cut_defaults(k: F.Why, cands: List<&2, Nat>, r: Maybe<&2, Parts>) -> Maybe<&2, F.In>:
  match r:
    case None{}:
      None{}
    case Some{p}:
      match p:
        case Parts{defaults, tried}:
          Some{F.In{k, cands, defaults, tried}}

# the signed-in defaults (their count first), then the tried models
def parse.defaults(k: F.Why, cands: List<&2, Nat>, xs: List<&2, Nat>) -> Maybe<&2, F.In>:
  match xs:
    case Nil{}:
      None{}
    case n <> t:
      parse.cut_defaults(k, cands, split(n, t))

def parse.cut(k: F.Why, r: Maybe<&2, Parts>) -> Maybe<&2, F.In>:
  match r:
    case None{}:
      None{}
    case Some{p}:
      match p:
        case Parts{cands, rest}:
          parse.defaults(k, cands, rest)

# the candidates (their count first), then the defaults and the tried
# models
def parse.lists(k: F.Why, xs: List<&2, Nat>) -> Maybe<&2, F.In>:
  match xs:
    case Nil{}:
      None{}
    case n <> t:
      parse.cut(k, split(n, t))

def parse.failed(xs: List<&2, Nat>) -> Maybe<&2, F.In>:
  match xs:
    case Nil{}:
      None{}
    case n <> t:
      match t:
        case Nil{}:
          None{}
        case r <> u:
          parse.lists(F.Failed{n, r}, u)

def parse.quota(xs: List<&2, Nat>) -> Maybe<&2, F.In>:
  match xs:
    case Nil{}:
      None{}
    case u <> t:
      parse.lists(F.Quota{u}, t)

def parse.kind(k: Nat, xs: List<&2, Nat>) -> Maybe<&2, F.In>:
  match k:
    case 0n:
      parse.failed(xs)
    case 1n:
      parse.lists(F.Login{}, xs)
    case 2n:
      parse.quota(xs)
    case 3n:
      parse.lists(F.Unset{}, xs)
    case 4n+q:
      None{}

# the request a list of Nats spells, None when it spells none
def parse(xs: List<&2, Nat>) -> Maybe<&2, F.In>:
  match xs:
    case Nil{}:
      None{}
    case k <> t:
      parse.kind(k, t)

# the list at the start of s
def get_req(s: String) -> W.Dec<List<&2, Nat>>:
  W.get_list(~Nat, ~W.get_nat, s)

# The entry
# ---------

# the spelling of a failure, then rest
def put_why(k: F.Why, rest: String) -> String:
  match k:
    case F.Failed{n, retries}:
      W.put_nat(0n, W.put_nat(n, W.put_nat(retries, rest)))
    case F.Login{}:
      W.put_nat(1n, rest)
    case F.Quota{until}:
      W.put_nat(2n, W.put_nat(until, rest))
    case F.Unset{}:
      W.put_nat(3n, rest)

# the reply's spelling of a choice
def put_choice(c: F.Choice) -> String:
  match c:
    case F.Keep{}:
      W.put_nat(0n, "")
    case F.Switch{m}:
      W.put_nat(1n, W.put_nat(m, ""))
    case F.Hold{until}:
      W.put_nat(2n, W.put_nat(until, ""))
    case F.End{k}:
      W.put_nat(3n, put_why(k, ""))

def ffi.parsed(r: Maybe<&2, F.In>) -> String:
  match r:
    case None{}:
      W.err("fallback: malformed request")
    case Some{x}:
      put_choice(F.choose(x))

def ffi.done(xs: List<&2, Nat>, end: Bool) -> String:
  match end:
    case True{}:
      ffi.parsed(parse(xs))
    case False{}:
      W.err("fallback: malformed request")

def ffi.got(r: W.Dec<List<&2, Nat>>) -> String:
  match r:
    case W.Got{xs, +s}:
      ffi.done(xs, W.end(s))
    case W.Bad{}:
      W.err("fallback: malformed request")

# the entry: decode the request, answer the model's choice
def ffi(input: String) -> String:
  ffi.got(get_req(input))
