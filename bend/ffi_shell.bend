# ffi_shell: the approval gate of a shell step (bend/tools.bend part 4)
# as an entry of the compiled Bend core (crates/eukhe-shell/src/run.rs,
# crates/eukhe-core/src/durable/path_policy.rs through
# crates/eukhe-bend/src/rules/shell.rs). Rust gathers the facts of a step:
# the auto set and, per part of the step, its own effect codes and whether
# it names a path that is or holds a secret; the model decides the step's
# effects, whether it runs unasked, and what an answer does. A request
# names its question (crates/eukhe-bend/WIRE.md is the grammar):
#
#   tag 0  step     the auto set (List<Nat>), the parts (one List<Nat> of
#                   bend/wire_flat.bend: each part is [1 when it names a
#                   secret path else 0, then its own codes])
#                   -> the step's effects (List<Nat>, `join` of the
#                      parts' effects), then T when it runs unasked
#                      (`within`)
#   tag 1  allows   the auto set, effects (List<Nat>)
#                   -> T when they run unasked (`within`)
#   tag 2  answer   a gated step's id (Nat), the user's answer (Bool)
#                   -> 0 (the step runs) | 1, id (the script stops at it):
#                      `gate`
#
# Every input that is not exactly one request (an unknown tag, a part with
# no flag or a flag past 1, a number past the wire, input left over)
# answers the error form "shell: malformed request", never a default.
# laws/shell.bend states this file's laws; PROOF.bend proves them. Pure:
# no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./wire_flat.bend as Fl
import ./tools.bend as Tl

# A request of the entry
type Req is Data:
  QStep{auto: List<&2, Nat>, parts: List<&2, Tl.Part>}
  QAllows{auto: List<&2, Nat>, effs: List<&2, Nat>}
  QAnswer{id: Nat, yes: Bool}

# Parts
# -----

# the part an inner list of the flat parts spells: its flag, then its codes
def part.of(xs: List<&2, Nat>) -> Maybe<&2, Tl.Part>:
  match xs:
    case Nil{}:
      None{}
    case f <> own:
      match f:
        case 0n:
          Some{Tl.Part{own, False{}}}
        case 1n+g:
          match g:
            case 0n:
              Some{Tl.Part{own, True{}}}
            case 1n+h:
              None{}

def parts.cons(m: Maybe<&2, Tl.Part>, ms: Maybe<&2, List<&2, Tl.Part>>) -> Maybe<&2, List<&2, Tl.Part>>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      match ms:
        case None{}:
          None{}
        case Some{ps}:
          Some{p <> ps}

def parts.of(xss: List<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Tl.Part>>:
  match xss:
    case Nil{}:
      Some{Nil{}}
    case xs <> rest:
      parts.cons(part.of(xs), parts.of(rest))

def parts.flat(m: Maybe<&2, List<&2, List<&2, Nat>>>) -> Maybe<&2, List<&2, Tl.Part>>:
  match m:
    case None{}:
      None{}
    case Some{xss}:
      parts.of(xss)

# Requests
# --------

def get_ns(s: String) -> W.Dec<List<&2, Nat>>:
  W.get_list(~Nat, ~W.get_nat, s)

def get_step.parts(auto: List<&2, Nat>, m: Maybe<&2, List<&2, Tl.Part>>, s: String) -> W.Dec<Req>:
  match m:
    case None{}:
      W.Bad{}
    case Some{ps}:
      W.Got{QStep{auto, ps}, s}

def get_step.flat(auto: List<&2, Nat>, r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{ns, s}:
      get_step.parts(auto, parts.flat(Fl.unflat(ns)), s)
    case W.Bad{}:
      W.Bad{}

def get_step(r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{auto, s}:
      get_step.flat(auto, get_ns(s))
    case W.Bad{}:
      W.Bad{}

def get_allows.effs(auto: List<&2, Nat>, r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{es, s}:
      W.Got{QAllows{auto, es}, s}
    case W.Bad{}:
      W.Bad{}

def get_allows(r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{auto, s}:
      get_allows.effs(auto, get_ns(s))
    case W.Bad{}:
      W.Bad{}

def get_answer.yes(i: Nat, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{y, s}:
      W.Got{QAnswer{i, y}, s}
    case W.Bad{}:
      W.Bad{}

def get_answer(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{i, s}:
      get_answer.yes(i, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_step(get_ns(s))
    case 1n:
      get_allows(get_ns(s))
    case 2n:
      get_answer(W.get_nat(s))
    case 3n+u:
      W.Bad{}

def get_req.go(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.go(W.get_nat(s))

# Replies
# -------

def put_end(e: Tl.End, rest: String) -> String:
  match e:
    case Tl.Finished{}:
      W.put_nat(0n, rest)
    case Tl.Denied{i}:
      W.put_nat(1n, W.put_nat(i, rest))

def answer.step(+auto: List<&2, Nat>, +effs: List<&2, Nat>) -> String:
  W.put_list(~Nat, ~W.put_nat, effs, W.put_bool(Tl.within(effs, auto), ""))

# the model's decision on a request, encoded
def answer(q: Req) -> String:
  match q:
    case QStep{+auto, ps}:
      answer.step(auto, Tl.join(Tl.parts.effs(ps)))
    case QAllows{+auto, es}:
      W.put_bool(Tl.within(es, auto), "")
    case QAnswer{i, y}:
      put_end(Tl.Ran.end(Tl.gate(y, Tl.Step{i, Nil{}}, Tl.Ran{Nil{}, Tl.Finished{}})), "")

def malformed() -> String:
  W.err("shell: malformed request")

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
