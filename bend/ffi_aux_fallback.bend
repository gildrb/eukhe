# ffi_aux_fallback: the entry of the compiled Bend core for where a
# summarizer pass runs and the notices of a session
# (bend/aux_fallback.bend: `gate`, `settle`, and a pass's `put` and
# `after`). The codec is the wire format of bend/wire.bend:
#
#   request  0, Gate | 1, Settle | 2, Pass
#   Gate     p: Nat, Sel, ok: Bool                 reply: GateR
#   Settle   GateR, Look, need: Nat                reply: Route
#   Pass     Route, shown: List<Key>               reply: List<Ev>, List<Key>
#   Sel      0 unset | 1 the session model | 2, s: Nat
#   GateR    0, Route (decided) | 1, p: Nat, s: Nat (look up)
#   Look     0, r: Nat (nothing usable) | 1, w: Nat (found, its window)
#   Route    0 session | 1 routed | 2, Key (fallback)
#   Key      p: Nat, s: Nat, r: Nat
#   Ev       0 stay | 1 went | 2, Key (substitution) | 3, Key (notice)
#
# A malformed request, or one with input left over, answers the wire's
# error form.

import Base
import ./wire.bend as W
import ./aux_fallback.bend as M

# Encoders
# --------

def put_key(k: M.Key, rest: String) -> String:
  match k:
    case M.K{p, s, r}:
      W.put_nat(p, W.put_nat(s, W.put_nat(r, rest)))

def put_route(r: M.Route, rest: String) -> String:
  match r:
    case M.Session{}:
      W.put_nat(0n, rest)
    case M.Routed{}:
      W.put_nat(1n, rest)
    case M.Fallback{k}:
      W.put_nat(2n, put_key(k, rest))

def put_gate(g: M.Gate, rest: String) -> String:
  match g:
    case M.Known{r}:
      W.put_nat(0n, put_route(r, rest))
    case M.Lookup{p, s}:
      W.put_nat(1n, W.put_nat(p, W.put_nat(s, rest)))

def put_ev(e: M.Ev, rest: String) -> String:
  match e:
    case M.Stay{}:
      W.put_nat(0n, rest)
    case M.Went{}:
      W.put_nat(1n, rest)
    case M.Sub{k}:
      W.put_nat(2n, put_key(k, rest))
    case M.Note{k}:
      W.put_nat(3n, put_key(k, rest))

# Decoders
# --------

def get_key.r(p: Nat, s: Nat, d: W.Dec<Nat>) -> W.Dec<M.Key>:
  match d:
    case W.Got{r, rest}:
      W.Got{M.K{p, s, r}, rest}
    case W.Bad{}:
      W.Bad{}

def get_key.s(p: Nat, d: W.Dec<Nat>) -> W.Dec<M.Key>:
  match d:
    case W.Got{s, rest}:
      get_key.r(p, s, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_key.go(d: W.Dec<Nat>) -> W.Dec<M.Key>:
  match d:
    case W.Got{p, rest}:
      get_key.s(p, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_key(s: String) -> W.Dec<M.Key>:
  get_key.go(W.get_nat(s))

def get_route.fallback(d: W.Dec<M.Key>) -> W.Dec<M.Route>:
  match d:
    case W.Got{k, rest}:
      W.Got{M.Fallback{k}, rest}
    case W.Bad{}:
      W.Bad{}

def get_route.tag(n: Nat, s: String) -> W.Dec<M.Route>:
  match n:
    case 0n:
      W.Got{M.Session{}, s}
    case 1n+a:
      match a:
        case 0n:
          W.Got{M.Routed{}, s}
        case 1n+b:
          match b:
            case 0n:
              get_route.fallback(get_key(s))
            case 1n+c:
              W.Bad{}

def get_route.go(d: W.Dec<Nat>) -> W.Dec<M.Route>:
  match d:
    case W.Got{n, s}:
      get_route.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_route(s: String) -> W.Dec<M.Route>:
  get_route.go(W.get_nat(s))

def get_gate.known(d: W.Dec<M.Route>) -> W.Dec<M.Gate>:
  match d:
    case W.Got{r, s}:
      W.Got{M.Known{r}, s}
    case W.Bad{}:
      W.Bad{}

def get_gate.s(p: Nat, d: W.Dec<Nat>) -> W.Dec<M.Gate>:
  match d:
    case W.Got{s, rest}:
      W.Got{M.Lookup{p, s}, rest}
    case W.Bad{}:
      W.Bad{}

def get_gate.p(d: W.Dec<Nat>) -> W.Dec<M.Gate>:
  match d:
    case W.Got{p, rest}:
      get_gate.s(p, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_gate.tag(n: Nat, s: String) -> W.Dec<M.Gate>:
  match n:
    case 0n:
      get_gate.known(get_route(s))
    case 1n+a:
      match a:
        case 0n:
          get_gate.p(W.get_nat(s))
        case 1n+b:
          W.Bad{}

def get_gate.go(d: W.Dec<Nat>) -> W.Dec<M.Gate>:
  match d:
    case W.Got{n, s}:
      get_gate.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_gate(s: String) -> W.Dec<M.Gate>:
  get_gate.go(W.get_nat(s))

def get_sel.other(d: W.Dec<Nat>) -> W.Dec<M.Sel>:
  match d:
    case W.Got{s, rest}:
      W.Got{M.Other{s}, rest}
    case W.Bad{}:
      W.Bad{}

def get_sel.tag(n: Nat, s: String) -> W.Dec<M.Sel>:
  match n:
    case 0n:
      W.Got{M.Unset{}, s}
    case 1n+a:
      match a:
        case 0n:
          W.Got{M.Same{}, s}
        case 1n+b:
          match b:
            case 0n:
              get_sel.other(W.get_nat(s))
            case 1n+c:
              W.Bad{}

def get_sel.go(d: W.Dec<Nat>) -> W.Dec<M.Sel>:
  match d:
    case W.Got{n, s}:
      get_sel.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_look.tag(d: W.Dec<Nat>, n: Nat) -> W.Dec<M.Look>:
  match d:
    case W.Got{x, s}:
      match n:
        case 0n:
          W.Got{M.Miss{x}, s}
        case 1n+a:
          W.Got{M.Hit{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_look.go(d: W.Dec<Nat>) -> W.Dec<M.Look>:
  match d:
    case W.Got{n, s}:
      match n:
        case 0n:
          get_look.tag(W.get_nat(s), 0n)
        case 1n+a:
          match a:
            case 0n:
              get_look.tag(W.get_nat(s), 1n)
            case 1n+b:
              W.Bad{}
    case W.Bad{}:
      W.Bad{}

# The entry
# ---------

def fin(done: Bool, reply: String) -> String:
  match done:
    case True{}:
      reply
    case False{}:
      W.err("aux_fallback: input left over")

def gate.ok(p: Nat, sel: M.Sel, d: W.Dec<Bool>) -> String:
  match d:
    case W.Got{ok, s}:
      fin(W.end(s), put_gate(M.gate(p, sel, ok), ""))
    case W.Bad{}:
      W.err("aux_fallback: malformed allowedModels answer")

def gate.sel(p: Nat, d: W.Dec<M.Sel>) -> String:
  match d:
    case W.Got{sel, s}:
      gate.ok(p, sel, W.get_bool(s))
    case W.Bad{}:
      W.err("aux_fallback: malformed selector")

def gate.go(d: W.Dec<Nat>) -> String:
  match d:
    case W.Got{p, s}:
      gate.sel(p, get_sel.go(W.get_nat(s)))
    case W.Bad{}:
      W.err("aux_fallback: malformed purpose")

def settle.need(g: M.Gate, look: M.Look, d: W.Dec<Nat>) -> String:
  match d:
    case W.Got{need, s}:
      fin(W.end(s), put_route(M.settle(g, look, need), ""))
    case W.Bad{}:
      W.err("aux_fallback: malformed request size")

def settle.look(g: M.Gate, d: W.Dec<M.Look>) -> String:
  match d:
    case W.Got{look, s}:
      settle.need(g, look, W.get_nat(s))
    case W.Bad{}:
      W.err("aux_fallback: malformed lookup")

def settle.go(d: W.Dec<M.Gate>) -> String:
  match d:
    case W.Got{g, s}:
      settle.look(g, get_look.go(W.get_nat(s)))
    case W.Bad{}:
      W.err("aux_fallback: malformed gate")

def pass.reply(+r: M.Route, +sh: List<&2, M.Key>) -> String:
  W.put_list(~M.Ev, ~put_ev, M.put(r, sh, Nil{}), W.put_list(~M.Key, ~put_key, M.after(r, sh), ""))

def pass.shown(r: M.Route, d: W.Dec<List<&2, M.Key>>) -> String:
  match d:
    case W.Got{sh, s}:
      fin(W.end(s), pass.reply(r, sh))
    case W.Bad{}:
      W.err("aux_fallback: malformed shown keys")

def pass.go(d: W.Dec<M.Route>) -> String:
  match d:
    case W.Got{r, s}:
      pass.shown(r, W.get_list(~M.Key, ~get_key, s))
    case W.Bad{}:
      W.err("aux_fallback: malformed route")

def ffi.tag(n: Nat, s: String) -> String:
  match n:
    case 0n:
      gate.go(W.get_nat(s))
    case 1n+a:
      match a:
        case 0n:
          settle.go(get_gate(s))
        case 1n+b:
          match b:
            case 0n:
              pass.go(get_route(s))
            case 1n+c:
              W.err("aux_fallback: unknown request")

def ffi.go(d: W.Dec<Nat>) -> String:
  match d:
    case W.Got{n, s}:
      ffi.tag(n, s)
    case W.Bad{}:
      W.err("aux_fallback: malformed request")

# One request: a pass's gate, its route once the lookups ran, or the
# events and shown keys of a routed pass.
def ffi(input: String) -> String:
  ffi.go(W.get_nat(input))
