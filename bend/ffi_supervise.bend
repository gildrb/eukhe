# ffi_supervise: the compiled Bend core's entry for the restart budget
# (bend/supervise.bend `decide`). Rust `restart_budget::decide` calls it
# through `eukhe_bend::call`.
#
# Request (crates/eukhe-bend/WIRE.md): a record
#   k, w, base, max: Nat   the budget's configuration (M.Cfg)
#   ages: List<Nat>        the ages (ms, newest first) of the failures in
#                          the window, relative to the last failure
#   gap:  Nat              the ms since the last failure (Rust saturates
#                          it at w: a gap of a whole window drops every age)
# Reply: a record
#   ages: List<Nat>        the new ages, this failure at 0 in front
#   verdict: tag           0 Relaunch{failure: Nat, backoff: Nat},
#                          1 GiveUp{failures: Nat}
# A malformed request or input left over answers the wire error form.

import Base
import ./wire.bend as W
import ./supervise.bend as M

type Req is Data:
  Req{cfg: M.Cfg, ages: List<&2, Nat>, gap: Nat}

type Reply is Data:
  Reply{ages: List<&2, Nat>, verdict: M.Verdict}

def put_ages(xs: List<&2, Nat>, rest: String) -> String:
  W.put_list(~Nat, ~W.put_nat, xs, rest)

def get_ages(s: String) -> W.Dec<List<&2, Nat>>:
  W.get_list(~Nat, ~W.get_nat, s)

# the configuration: four Nats

def put_cfg(c: M.Cfg, rest: String) -> String:
  match c:
    case M.Cfg{k, w, b, m}:
      W.put_nat(k, W.put_nat(w, W.put_nat(b, W.put_nat(m, rest))))

def get_cfg.m(k: Nat, w: Nat, b: Nat, r: W.Dec<Nat>) -> W.Dec<M.Cfg>:
  match r:
    case W.Got{m, rest}:
      W.Got{M.Cfg{k, w, b, m}, rest}
    case W.Bad{}:
      W.Bad{}

def get_cfg.b(k: Nat, w: Nat, r: W.Dec<Nat>) -> W.Dec<M.Cfg>:
  match r:
    case W.Got{b, rest}:
      get_cfg.m(k, w, b, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_cfg.w(k: Nat, r: W.Dec<Nat>) -> W.Dec<M.Cfg>:
  match r:
    case W.Got{w, rest}:
      get_cfg.b(k, w, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_cfg.k(r: W.Dec<Nat>) -> W.Dec<M.Cfg>:
  match r:
    case W.Got{k, rest}:
      get_cfg.w(k, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_cfg(s: String) -> W.Dec<M.Cfg>:
  get_cfg.k(W.get_nat(s))

# the verdict: a tag and its fields

def put_verdict(v: M.Verdict, rest: String) -> String:
  match v:
    case M.Relaunch{f, b}:
      W.put_nat(0n, W.put_nat(f, W.put_nat(b, rest)))
    case M.GiveUp{f}:
      W.put_nat(1n, W.put_nat(f, rest))

def get_verdict.backoff(f: Nat, r: W.Dec<Nat>) -> W.Dec<M.Verdict>:
  match r:
    case W.Got{b, rest}:
      W.Got{M.Relaunch{f, b}, rest}
    case W.Bad{}:
      W.Bad{}

def get_verdict.relaunch(r: W.Dec<Nat>) -> W.Dec<M.Verdict>:
  match r:
    case W.Got{f, rest}:
      get_verdict.backoff(f, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_verdict.give_up(r: W.Dec<Nat>) -> W.Dec<M.Verdict>:
  match r:
    case W.Got{f, rest}:
      W.Got{M.GiveUp{f}, rest}
    case W.Bad{}:
      W.Bad{}

def get_verdict.tag(t: Nat, rest: String) -> W.Dec<M.Verdict>:
  match t:
    case 0n:
      get_verdict.relaunch(W.get_nat(rest))
    case 1n+p:
      match p:
        case 0n:
          get_verdict.give_up(W.get_nat(rest))
        case 1n+q:
          W.Bad{}

def get_verdict.of(r: W.Dec<Nat>) -> W.Dec<M.Verdict>:
  match r:
    case W.Got{t, rest}:
      get_verdict.tag(t, rest)
    case W.Bad{}:
      W.Bad{}

def get_verdict(s: String) -> W.Dec<M.Verdict>:
  get_verdict.of(W.get_nat(s))

# the request

def put_req(q: Req, rest: String) -> String:
  match q:
    case Req{c, a, g}:
      put_cfg(c, put_ages(a, W.put_nat(g, rest)))

def get_req.gap(c: M.Cfg, a: List<&2, Nat>, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{g, rest}:
      W.Got{Req{c, a, g}, rest}
    case W.Bad{}:
      W.Bad{}

def get_req.ages(c: M.Cfg, r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{a, rest}:
      get_req.gap(c, a, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_req.cfg(r: W.Dec<M.Cfg>) -> W.Dec<Req>:
  match r:
    case W.Got{c, rest}:
      get_req.ages(c, get_ages(rest))
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.cfg(get_cfg(s))

# the reply

def put_reply(p: Reply, rest: String) -> String:
  match p:
    case Reply{a, v}:
      put_ages(a, put_verdict(v, rest))

def get_reply.verdict(a: List<&2, Nat>, r: W.Dec<M.Verdict>) -> W.Dec<Reply>:
  match r:
    case W.Got{v, rest}:
      W.Got{Reply{a, v}, rest}
    case W.Bad{}:
      W.Bad{}

def get_reply.ages(r: W.Dec<List<&2, Nat>>) -> W.Dec<Reply>:
  match r:
    case W.Got{a, rest}:
      get_reply.verdict(a, get_verdict(rest))
    case W.Bad{}:
      W.Bad{}

def get_reply(s: String) -> W.Dec<Reply>:
  get_reply.ages(get_ages(s))

# the decision on a request: the model's state is the ages and their count
def decide.of(d: M.Decision) -> Reply:
  match d:
    case M.Decision{s, v}:
      Reply{M.St.ages(s), v}

def decide(q: Req) -> Reply:
  match q:
    case Req{c, +a, g}:
      decide.of(M.decide(c, M.St{a, List.length(&2, Nat, a)}, g))

def ffi.fin(done: Bool, q: Req) -> String:
  match done:
    case True{}:
      put_reply(decide(q), "")
    case False{}:
      W.err("supervise: input left over")

def ffi.go(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, rest}:
      ffi.fin(W.end(rest), q)
    case W.Bad{}:
      W.err("supervise: malformed request")

def ffi(input: String) -> String:
  ffi.go(get_req(input))
