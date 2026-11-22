# ffi_shell: the shell step (bend/tools.bend part 4) as an entry of the
# compiled Bend core (crates/eukhe-shell/src/run.rs through
# crates/eukhe-bend/src/rules/shell.rs). Rust gathers the facts of a step:
# per part of the step, its own effect codes, whether it names a path
# that is or holds a secret and whether it writes an own path; the model
# decides the step's effects and whether it runs. A request names its
# question (crates/eukhe-bend/WIRE.md is the grammar):
#
#   tag 3  verdict  the parts (one List<Nat> of bend/wire_flat.bend: each
#                   part is [1 when it names a secret path else 0, 1 when
#                   it writes an own path else 0, then its own codes])
#                   -> the step's effects (List<Nat>, `pieces.effs`), then
#                      0 (it runs) | 1 (it is refused): `verdict`
#
# Tags 0 to 2 name no question (they were the approval gate's `step`,
# `allows` and `answer`); the tags keep their numbers.
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
  QVerdict{parts: List<&2, Tl.Piece>}

# Parts
# -----

# a flag of a part: 0 is False, 1 is True, anything else spells nothing
def flag.of(f: Nat) -> Maybe<&2, Bool>:
  match f:
    case 0n:
      Some{False{}}
    case 1n+g:
      match g:
        case 0n:
          Some{True{}}
        case 1n+h:
          None{}

def piece.mine(s: Bool, m: Maybe<&2, Bool>, own: List<&2, Nat>) -> Maybe<&2, Tl.Piece>:
  match m:
    case None{}:
      None{}
    case Some{w}:
      Some{Tl.Piece{own, s, w}}

def piece.secret(m: Maybe<&2, Bool>, xs: List<&2, Nat>) -> Maybe<&2, Tl.Piece>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      match xs:
        case Nil{}:
          None{}
        case w <> own:
          piece.mine(s, flag.of(w), own)

# the piece an inner list of the flat parts spells: its two flags, then
# its codes
def piece.of(xs: List<&2, Nat>) -> Maybe<&2, Tl.Piece>:
  match xs:
    case Nil{}:
      None{}
    case f <> rest:
      piece.secret(flag.of(f), rest)

def pieces.cons(m: Maybe<&2, Tl.Piece>, ms: Maybe<&2, List<&2, Tl.Piece>>) -> Maybe<&2, List<&2, Tl.Piece>>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      match ms:
        case None{}:
          None{}
        case Some{ps}:
          Some{p <> ps}

def pieces.of(xss: List<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Tl.Piece>>:
  match xss:
    case Nil{}:
      Some{Nil{}}
    case xs <> rest:
      pieces.cons(piece.of(xs), pieces.of(rest))

def pieces.flat(m: Maybe<&2, List<&2, List<&2, Nat>>>) -> Maybe<&2, List<&2, Tl.Piece>>:
  match m:
    case None{}:
      None{}
    case Some{xss}:
      pieces.of(xss)

# Requests
# --------

def get_ns(s: String) -> W.Dec<List<&2, Nat>>:
  W.get_list(~Nat, ~W.get_nat, s)

def get_verdict.pieces(m: Maybe<&2, List<&2, Tl.Piece>>, s: String) -> W.Dec<Req>:
  match m:
    case None{}:
      W.Bad{}
    case Some{ps}:
      W.Got{QVerdict{ps}, s}

def get_verdict(r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{ns, s}:
      get_verdict.pieces(pieces.flat(Fl.unflat(ns)), s)
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      W.Bad{}
    case 1n:
      W.Bad{}
    case 2n:
      W.Bad{}
    case 3n:
      get_verdict(get_ns(s))
    case 4n+u:
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

def put_verdict(v: Tl.Verdict, rest: String) -> String:
  match v:
    case Tl.Runs{}:
      W.put_nat(0n, rest)
    case Tl.Refused{}:
      W.put_nat(1n, rest)

# the model's decision on a request, encoded
def answer(q: Req) -> String:
  match q:
    case QVerdict{+ps}:
      W.put_list(~Nat, ~W.put_nat, Tl.pieces.effs(ps), put_verdict(Tl.verdict(ps), ""))

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
