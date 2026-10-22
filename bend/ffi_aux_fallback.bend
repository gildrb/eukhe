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

# A request: a pass's gate, its route once the lookups ran, or a routed
# pass and the keys the session has shown.
type Req is Data:
  GateReq{p: Nat, sel: M.Sel, ok: Bool}
  SettleReq{g: M.Gate, look: M.Look, need: Nat}
  PassReq{r: M.Route, shown: List<&2, M.Key>}

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

def put_sel(x: M.Sel, rest: String) -> String:
  match x:
    case M.Unset{}:
      W.put_nat(0n, rest)
    case M.Same{}:
      W.put_nat(1n, rest)
    case M.Other{s}:
      W.put_nat(2n, W.put_nat(s, rest))

def put_look(x: M.Look, rest: String) -> String:
  match x:
    case M.Miss{r}:
      W.put_nat(0n, W.put_nat(r, rest))
    case M.Hit{w}:
      W.put_nat(1n, W.put_nat(w, rest))

def put_req(x: Req, rest: String) -> String:
  match x:
    case GateReq{p, sel, ok}:
      W.put_nat(0n, W.put_nat(p, put_sel(sel, W.put_bool(ok, rest))))
    case SettleReq{g, look, need}:
      W.put_nat(1n, put_gate(g, put_look(look, W.put_nat(need, rest))))
    case PassReq{r, sh}:
      W.put_nat(2n, put_route(r, W.put_list(~M.Key, ~put_key, sh, rest)))

# the reply to a pass: its events, then the keys shown after it
def put_pass(d: List<&2, M.Ev> & List<&2, M.Key>, rest: String) -> String:
  (es, ks) = d
  W.put_list(~M.Ev, ~put_ev, es, W.put_list(~M.Key, ~put_key, ks, rest))

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

def get_sel(s: String) -> W.Dec<M.Sel>:
  get_sel.go(W.get_nat(s))

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

def get_look(s: String) -> W.Dec<M.Look>:
  get_look.go(W.get_nat(s))

def get_req.ok(p: Nat, sel: M.Sel, d: W.Dec<Bool>) -> W.Dec<Req>:
  match d:
    case W.Got{ok, s}:
      W.Got{GateReq{p, sel, ok}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.sel(p: Nat, d: W.Dec<M.Sel>) -> W.Dec<Req>:
  match d:
    case W.Got{sel, s}:
      get_req.ok(p, sel, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_req.gate(d: W.Dec<Nat>) -> W.Dec<Req>:
  match d:
    case W.Got{p, s}:
      get_req.sel(p, get_sel(s))
    case W.Bad{}:
      W.Bad{}

def get_req.need(g: M.Gate, look: M.Look, d: W.Dec<Nat>) -> W.Dec<Req>:
  match d:
    case W.Got{need, s}:
      W.Got{SettleReq{g, look, need}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.look(g: M.Gate, d: W.Dec<M.Look>) -> W.Dec<Req>:
  match d:
    case W.Got{look, s}:
      get_req.need(g, look, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.settle(d: W.Dec<M.Gate>) -> W.Dec<Req>:
  match d:
    case W.Got{g, s}:
      get_req.look(g, get_look(s))
    case W.Bad{}:
      W.Bad{}

def get_req.shown(r: M.Route, d: W.Dec<List<&2, M.Key>>) -> W.Dec<Req>:
  match d:
    case W.Got{sh, s}:
      W.Got{PassReq{r, sh}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.pass(d: W.Dec<M.Route>) -> W.Dec<Req>:
  match d:
    case W.Got{r, s}:
      get_req.shown(r, W.get_list(~M.Key, ~get_key, s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(n: Nat, s: String) -> W.Dec<Req>:
  match n:
    case 0n:
      get_req.gate(W.get_nat(s))
    case 1n+a:
      match a:
        case 0n:
          get_req.settle(get_gate(s))
        case 1n+b:
          match b:
            case 0n:
              get_req.pass(get_route(s))
            case 1n+c:
              W.Bad{}

def get_req.go(d: W.Dec<Nat>) -> W.Dec<Req>:
  match d:
    case W.Got{n, s}:
      get_req.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.go(W.get_nat(s))

# The replies, as the Rust Reader reads them (a gate's and a route's
# decoders are above)

def get_ev.sub(d: W.Dec<M.Key>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{k, s}:
      W.Got{M.Sub{k}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.note(d: W.Dec<M.Key>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{k, s}:
      W.Got{M.Note{k}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.tag(n: Nat, s: String) -> W.Dec<M.Ev>:
  match n:
    case 0n:
      W.Got{M.Stay{}, s}
    case 1n+a:
      match a:
        case 0n:
          W.Got{M.Went{}, s}
        case 1n+b:
          match b:
            case 0n:
              get_ev.sub(get_key(s))
            case 1n+c:
              match c:
                case 0n:
                  get_ev.note(get_key(s))
                case 1n+d:
                  W.Bad{}

def get_ev.go(d: W.Dec<Nat>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{n, s}:
      get_ev.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_ev(s: String) -> W.Dec<M.Ev>:
  get_ev.go(W.get_nat(s))

def get_pass.keys(es: List<&2, M.Ev>, d: W.Dec<List<&2, M.Key>>) -> W.Dec<+Sigma<List<&2, M.Ev>, x => List<&2, M.Key>>>:
  match d:
    case W.Got{ks, s}:
      W.Got{(es, ks), s}
    case W.Bad{}:
      W.Bad{}

def get_pass.go(d: W.Dec<List<&2, M.Ev>>) -> W.Dec<+Sigma<List<&2, M.Ev>, x => List<&2, M.Key>>>:
  match d:
    case W.Got{es, s}:
      get_pass.keys(es, W.get_list(~M.Key, ~get_key, s))
    case W.Bad{}:
      W.Bad{}

def get_pass(s: String) -> W.Dec<+Sigma<List<&2, M.Ev>, x => List<&2, M.Key>>>:
  get_pass.go(W.get_list(~M.Ev, ~get_ev, s))

# The entry
# ---------

# The model's answer to a request, encoded.
def answer(x: Req) -> String:
  match x:
    case GateReq{p, sel, ok}:
      put_gate(M.gate(p, sel, ok), "")
    case SettleReq{g, look, need}:
      put_route(M.settle(g, look, need), "")
    case PassReq{+r, +sh}:
      put_pass((M.put(r, sh, Nil{}), M.after(r, sh)), "")

# the answer, when nothing is left of the input
def ffi.end(done: Bool, x: Req) -> String:
  match done:
    case True{}:
      answer(x)
    case False{}:
      W.err("aux_fallback: input left over")

def ffi.go(d: W.Dec<Req>) -> String:
  match d:
    case W.Got{x, s}:
      ffi.end(W.end(s), x)
    case W.Bad{}:
      W.err("aux_fallback: malformed request")

# One request: a pass's gate, its route once the lookups ran, or the
# events and shown keys of a routed pass.
def ffi(input: String) -> String:
  ffi.go(get_req(input))
