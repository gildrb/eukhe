# ffi_path_own: the own paths (bend/path_own.bend) as an entry of the
# compiled Bend core (crates/eukhe-bend/src/rules/path_own.rs). Rust
# gathers the facts: the own rules and the real path, every name interned
# by Rust (equal names, equal numbers; paths deepest first), the judge's
# class of the path and whether the access writes; the model decides. The
# rules cross as one list (bend/wire_flat.bend): a rule is 0 then its path
# (Tree) or 1 then its path (Dir). The wire format is bend/wire.bend
# (crates/eukhe-bend/WIRE.md is the grammar):
#
#   request  List<Nat> List<Nat> Nat Bool
#            (the own rules, the path, the judge's class: 0 Inside,
#            1 Outside, 2 Protected, 3 Secret; it writes)
#   reply    0, c (the judge's class c: no own rule names the write) |
#            1, i (Own: the write the rule at place i names, from 0)
#
# Every input that is not exactly one request (an unknown rule tag or
# class, a name after the last end mark, a number past the wire, input
# left over) answers the error form "path_own: malformed request", never a
# default. laws/path_own.bend states this file's laws; PROOF.bend proves
# them. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./wire_flat.bend as Fl
import ./path_policy.bend as Pp
import ./path_own.bend as Po

# A request of the entry
type Req is Data:
  Req{rs: List<&2, Po.Rule>, at: List<&2, Nat>, c: Pp.Cls, w: Bool}

# The rules
# ---------

# the rule a path of the flat list spells
def rule.of(xs: List<&2, Nat>) -> Maybe<&2, Po.Rule>:
  match xs:
    case Nil{}:
      None{}
    case t <> p:
      match t:
        case 0n:
          Some{Po.Tree{p}}
        case 1n:
          Some{Po.Dir{p}}
        case 2n+u:
          None{}

def rules.cons(m: Maybe<&2, Po.Rule>, ms: Maybe<&2, List<&2, Po.Rule>>) -> Maybe<&2, List<&2, Po.Rule>>:
  match m ms:
    case Some{r} Some{rs}:
      Some{r <> rs}
    case Some{r} None{}:
      None{}
    case None{} Some{rs}:
      None{}
    case None{} None{}:
      None{}

def rules.of(xss: List<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Po.Rule>>:
  match xss:
    case Nil{}:
      Some{Nil{}}
    case xs <> rest:
      rules.cons(rule.of(xs), rules.of(rest))

# the rules a flat list spells; None when it spells none
def rules.flat(m: Maybe<&2, List<&2, List<&2, Nat>>>) -> Maybe<&2, List<&2, Po.Rule>>:
  match m:
    case None{}:
      None{}
    case Some{xss}:
      rules.of(xss)

# the class a code names
def cls.of(n: Nat) -> Maybe<&2, Pp.Cls>:
  match n:
    case 0n:
      Some{Pp.Inside{}}
    case 1n:
      Some{Pp.Outside{}}
    case 2n:
      Some{Pp.Protected{}}
    case 3n:
      Some{Pp.Secret{}}
    case 4n+u:
      None{}

# the code of a class
def cls(c: Pp.Cls) -> Nat:
  match c:
    case Pp.Inside{}:
      0n
    case Pp.Outside{}:
      1n
    case Pp.Protected{}:
      2n
    case Pp.Secret{}:
      3n

# Requests
# --------

def get_ns(s: String) -> W.Dec<List<&2, Nat>>:
  W.get_list(~Nat, ~W.get_nat, s)

def get_req.w(rs: List<&2, Po.Rule>, at: List<&2, Nat>, c: Pp.Cls, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{w, s}:
      W.Got{Req{rs, at, c, w}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.c(rs: List<&2, Po.Rule>, at: List<&2, Nat>, m: Maybe<&2, Pp.Cls>, s: String) -> W.Dec<Req>:
  match m:
    case None{}:
      W.Bad{}
    case Some{c}:
      get_req.w(rs, at, c, W.get_bool(s))

def get_req.cls(rs: List<&2, Po.Rule>, at: List<&2, Nat>, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{k, s}:
      get_req.c(rs, at, cls.of(k), s)
    case W.Bad{}:
      W.Bad{}

def get_req.at(rs: List<&2, Po.Rule>, r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{at, s}:
      get_req.cls(rs, at, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.rs(m: Maybe<&2, List<&2, Po.Rule>>, s: String) -> W.Dec<Req>:
  match m:
    case None{}:
      W.Bad{}
    case Some{rs}:
      get_req.at(rs, get_ns(s))

def get_req.rules(r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{ns, s}:
      get_req.rs(rules.flat(Fl.unflat(ns)), s)
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.rules(get_ns(s))

# Replies
# -------

def put_wc(x: Po.Wc, rest: String) -> String:
  match x:
    case Po.Judged{c}:
      W.put_nat(0n, W.put_nat(cls(c), rest))
    case Po.Own{i}:
      W.put_nat(1n, W.put_nat(i, rest))

# the model's decision on a request, encoded
def answer(q: Req) -> String:
  match q:
    case Req{rs, at, c, w}:
      put_wc(Po.class(rs, at, c, w), "")

def malformed() -> String:
  W.err("path_own: malformed request")

def run.end(whole: Bool, q: Req) -> String:
  match whole:
    case True{}:
      answer(q)
    case False{}:
      malformed()

def run(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, s}:
      run.end(W.end(s), q)
    case W.Bad{}:
      malformed()

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  run(get_req(input))
