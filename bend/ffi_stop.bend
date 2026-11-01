# ffi_stop: the entry of the compiled Bend core for the Directors at a
# candidate stop (bend/stop.bend; Rust: eukhe-durable
# harness/generation/stop.rs). Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  0, cut, text, broken, pending (Bools)
#              -> the pick (Nat): 0 stands | 1 LengthStop | 2 EmptyStop |
#                 3 MarkupStop | 4 PendingWork
#            1, attempt (Nat), the length note: tokens, row, cap (Nats)
#              -> the note's text (String)
#            2, max, done (Nats)
#              -> the round note (Maybe<String>: 0, | 1, then the text)
#
# A tag past 2, malformed input, or input left after the request answers
# `E stop: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./stop.bend as S

# A request of the entry
type Ask is Data:
  AskWalk{f: S.Facts}
  AskNote{attempt: Nat, n: S.Note}
  AskRounds{max: Nat, done: Nat}

# Reading a request
# -----------------

def get_walk.pending(c: Bool, t: Bool, b: Bool, d: W.Dec<Bool>) -> W.Dec<Ask>:
  match d:
    case W.Got{p, r}:
      W.Got{AskWalk{S.Facts{c, t, b, p}}, r}
    case W.Bad{}:
      W.Bad{}

def get_walk.broken(c: Bool, t: Bool, d: W.Dec<Bool>) -> W.Dec<Ask>:
  match d:
    case W.Got{b, r}:
      get_walk.pending(c, t, b, W.get_bool(r))
    case W.Bad{}:
      W.Bad{}

def get_walk.text(c: Bool, d: W.Dec<Bool>) -> W.Dec<Ask>:
  match d:
    case W.Got{t, r}:
      get_walk.broken(c, t, W.get_bool(r))
    case W.Bad{}:
      W.Bad{}

def get_walk(d: W.Dec<Bool>) -> W.Dec<Ask>:
  match d:
    case W.Got{c, r}:
      get_walk.text(c, W.get_bool(r))
    case W.Bad{}:
      W.Bad{}

def get_cut.cap(a: Nat, t: Nat, w: Nat, d: W.Dec<Nat>) -> W.Dec<Ask>:
  match d:
    case W.Got{k, r}:
      W.Got{AskNote{a, S.Cut{t, w, k}}, r}
    case W.Bad{}:
      W.Bad{}

def get_cut.row(a: Nat, t: Nat, d: W.Dec<Nat>) -> W.Dec<Ask>:
  match d:
    case W.Got{w, r}:
      get_cut.cap(a, t, w, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_cut(a: Nat, d: W.Dec<Nat>) -> W.Dec<Ask>:
  match d:
    case W.Got{t, r}:
      get_cut.row(a, t, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_note(d: W.Dec<Nat>) -> W.Dec<Ask>:
  match d:
    case W.Got{a, r}:
      get_cut(a, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_rounds.done(m: Nat, d: W.Dec<Nat>) -> W.Dec<Ask>:
  match d:
    case W.Got{n, r}:
      W.Got{AskRounds{m, n}, r}
    case W.Bad{}:
      W.Bad{}

def get_rounds(d: W.Dec<Nat>) -> W.Dec<Ask>:
  match d:
    case W.Got{m, r}:
      get_rounds.done(m, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_ask.tag(d: W.Dec<Nat>) -> W.Dec<Ask>:
  match d:
    case W.Got{n, r}:
      match n:
        case 0n:
          get_walk(W.get_bool(r))
        case 1n:
          get_note(W.get_nat(r))
        case 2n:
          get_rounds(W.get_nat(r))
        case 3n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_ask(s: String) -> W.Dec<Ask>:
  get_ask.tag(W.get_nat(s))

# The answers
# -----------

def put_pick(p: S.Pick, rest: String) -> String:
  match p:
    case S.Stands{}:
      W.put_nat(0n, rest)
    case S.Goes{d}:
      match d:
        case S.LengthStop{}:
          W.put_nat(1n, rest)
        case S.EmptyStop{}:
          W.put_nat(2n, rest)
        case S.MarkupStop{}:
          W.put_nat(3n, rest)
        case S.PendingWork{}:
          W.put_nat(4n, rest)

def put_text(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{t}:
      W.put_nat(1n, W.put_str(t, rest))

# the reply of a request: the model's answer, encoded
def answer(a: Ask) -> String:
  match a:
    case AskWalk{f}:
      put_pick(S.walk(f), "")
    case AskNote{at, n}:
      W.put_str(S.note(at, n), "")
    case AskRounds{m, d}:
      put_text(S.rounds(m, d), "")

# The entry
# ---------

def ffi.done(a: Ask, end: Bool) -> String:
  match end:
    case True{}:
      answer(a)
    case False{}:
      W.err("stop: malformed request")

def ffi.got(r: W.Dec<Ask>) -> String:
  match r:
    case W.Got{a, +s}:
      ffi.done(a, W.end(s))
    case W.Bad{}:
      W.err("stop: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_ask(input))
