# ffi_default_model: the entry of the compiled Bend core for the model a
# session opens on with no model requested (bend/default_model.bend
# `resolve`, the Rust `resolve_default`). The codec is the wire format of
# bend/wire.bend:
#
#   request  saved: 0 (none) | 1, m: Nat; cat: Bool; key: Bool; out:
#            Bool; next: 0 (none) | 1, n: Nat
#   reply    0, Pick, Sub (runs) | 1 (no model) | 2, Key (refused)
#   Pick     0 (the saved default) | 1, n: Nat (another model)
#   Sub      0 (kept) | 1, Key (swapped)
#   Key      m: Nat, Reason (0 not in the catalog | 1 no credentials
#            | 2 not in the scope)
#
# A malformed request, or one with input left over, answers the wire's
# error form.

import Base
import ./wire.bend as W
import ./default_model.bend as M

# Encoders
# --------

def put_reason(r: M.Reason, rest: String) -> String:
  match r:
    case M.NotInCatalog{}:
      W.put_nat(0n, rest)
    case M.NoCredentials{}:
      W.put_nat(1n, rest)
    case M.NotInScope{}:
      W.put_nat(2n, rest)

def put_key(k: M.Key, rest: String) -> String:
  match k:
    case M.K{m, r}:
      W.put_nat(m, put_reason(r, rest))

def put_pick(p: M.Pick, rest: String) -> String:
  match p:
    case M.Saved{}:
      W.put_nat(0n, rest)
    case M.Other{n}:
      W.put_nat(1n, W.put_nat(n, rest))

def put_sub(s: M.Sub, rest: String) -> String:
  match s:
    case M.Kept{}:
      W.put_nat(0n, rest)
    case M.Swapped{k}:
      W.put_nat(1n, put_key(k, rest))

def put_res(r: M.Res, rest: String) -> String:
  match r:
    case M.Runs{p, s}:
      W.put_nat(0n, put_pick(p, put_sub(s, rest)))
    case M.Nothing{}:
      W.put_nat(1n, rest)
    case M.Refused{k}:
      W.put_nat(2n, put_key(k, rest))

# Decoders
# --------

def get_saved.m(r: W.Dec<Nat>) -> W.Dec<M.Saved>:
  match r:
    case W.Got{m, s}:
      W.Got{M.Default{m}, s}
    case W.Bad{}:
      W.Bad{}

def get_saved.tag(n: Nat, s: String) -> W.Dec<M.Saved>:
  match n:
    case 0n:
      W.Got{M.NoDefault{}, s}
    case 1n+a:
      match a:
        case 0n:
          get_saved.m(W.get_nat(s))
        case 1n+b:
          W.Bad{}

def get_saved.go(r: W.Dec<Nat>) -> W.Dec<M.Saved>:
  match r:
    case W.Got{n, s}:
      get_saved.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_next.n(r: W.Dec<Nat>) -> W.Dec<M.Next>:
  match r:
    case W.Got{n, s}:
      W.Got{M.Next{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_next.tag(n: Nat, s: String) -> W.Dec<M.Next>:
  match n:
    case 0n:
      W.Got{M.NoNext{}, s}
    case 1n+a:
      match a:
        case 0n:
          get_next.n(W.get_nat(s))
        case 1n+b:
          W.Bad{}

def get_next.go(r: W.Dec<Nat>) -> W.Dec<M.Next>:
  match r:
    case W.Got{n, s}:
      get_next.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_in.next(saved: M.Saved, cat: Bool, key: Bool, out: Bool, r: W.Dec<M.Next>) -> W.Dec<M.In>:
  match r:
    case W.Got{next, s}:
      W.Got{M.In{saved, cat, key, out, next}, s}
    case W.Bad{}:
      W.Bad{}

def get_in.out(saved: M.Saved, cat: Bool, key: Bool, r: W.Dec<Bool>) -> W.Dec<M.In>:
  match r:
    case W.Got{out, s}:
      get_in.next(saved, cat, key, out, get_next.go(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_in.key(saved: M.Saved, cat: Bool, r: W.Dec<Bool>) -> W.Dec<M.In>:
  match r:
    case W.Got{key, s}:
      get_in.out(saved, cat, key, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_in.cat(saved: M.Saved, r: W.Dec<Bool>) -> W.Dec<M.In>:
  match r:
    case W.Got{cat, s}:
      get_in.key(saved, cat, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_in.go(r: W.Dec<M.Saved>) -> W.Dec<M.In>:
  match r:
    case W.Got{saved, s}:
      get_in.cat(saved, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_in(s: String) -> W.Dec<M.In>:
  get_in.go(get_saved.go(W.get_nat(s)))

# The entry
# ---------

def ffi.end(done: Bool, x: M.In) -> String:
  match done:
    case True{}:
      put_res(M.resolve(x), "")
    case False{}:
      W.err("default_model: input left over")

def ffi.go(r: W.Dec<M.In>) -> String:
  match r:
    case W.Got{x, s}:
      ffi.end(W.end(s), x)
    case W.Bad{}:
      W.err("default_model: malformed request")

# One resolution: the saved default's facts and the chain's pick in, the
# resolver's answer out.
def ffi(input: String) -> String:
  ffi.go(get_in(input))
