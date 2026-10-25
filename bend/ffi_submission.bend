# ffi_submission: the compiled Bend core's entry for one staged change of
# a submission's lifecycle (bend/submission.bend). Rust
# `eukhe_bend::rules::submission::step` calls it through `eukhe_bend::call`
# for every staged change a commit applies.
#
# Request (crates/eukhe-bend/WIRE.md): the submission, then the change.
#   submission: tag 0 queued input | 1 input placed at entry (Nat)
#     | 2 input answered (entry, answer: Nats) | 3 input unanswered before
#     its placement | 4 input unanswered at its entry (Nat) | 5 queued write
#     | 6 write placed at entry (Nat) | 7 write unanswered
#   change: tag 0 place at entry (Nat) | 1 answer (Nat) | 2 settle unanswered
# Reply: tag 0 the submission stays | 1 it moves to the submission that
# follows (spelled as above) | 2 the change is refused, then why: 0 the
# submission is not queued, 1 it is not a placed input.
# A malformed request (an unknown tag, a bad number) answers the error form
# "submission: malformed request"; input left after the request answers
# "submission: input left after the request": never a default.
# laws/submission.bend (section entry) states this file's laws. Pure: no
# IO, no @unsafe.

import Base
import ./wire.bend as W
import ./submission.bend as Sb

# Requests
# --------

# a submission with one entry: t 0 placed input, 1 input unanswered at its
# entry, 2 placed write
def get_sub.one(r: W.Dec<Nat>, t: Nat) -> W.Dec<Sb.Sub>:
  match r:
    case W.Got{e, s}:
      match t:
        case 0n:
          W.Got{Sb.InPlaced{e}, s}
        case 1n:
          W.Got{Sb.InDropped{Some{e}}, s}
        case 2n+u:
          W.Got{Sb.WrPlaced{e}, s}
    case W.Bad{}:
      W.Bad{}

def get_sub.answer(e: Nat, r: W.Dec<Nat>) -> W.Dec<Sb.Sub>:
  match r:
    case W.Got{a, s}:
      W.Got{Sb.InAnswered{e, a}, s}
    case W.Bad{}:
      W.Bad{}

def get_sub.two(r: W.Dec<Nat>) -> W.Dec<Sb.Sub>:
  match r:
    case W.Got{e, s}:
      get_sub.answer(e, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_sub.tag(t: Nat, s: String) -> W.Dec<Sb.Sub>:
  match t:
    case 0n:
      W.Got{Sb.InQueued{}, s}
    case 1n:
      get_sub.one(W.get_nat(s), 0n)
    case 2n:
      get_sub.two(W.get_nat(s))
    case 3n:
      W.Got{Sb.InDropped{None{}}, s}
    case 4n:
      get_sub.one(W.get_nat(s), 1n)
    case 5n:
      W.Got{Sb.WrQueued{}, s}
    case 6n:
      get_sub.one(W.get_nat(s), 2n)
    case 7n:
      W.Got{Sb.WrDropped{}, s}
    case 8n+u:
      W.Bad{}

def get_sub(r: W.Dec<Nat>) -> W.Dec<Sb.Sub>:
  match r:
    case W.Got{t, s}:
      get_sub.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# a change with one entry: t 0 place, 1 answer
def get_change.one(r: W.Dec<Nat>, t: Nat) -> W.Dec<Sb.Change>:
  match r:
    case W.Got{n, s}:
      match t:
        case 0n:
          W.Got{Sb.Place{n}, s}
        case 1n+u:
          W.Got{Sb.Answer{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_change.tag(t: Nat, s: String) -> W.Dec<Sb.Change>:
  match t:
    case 0n:
      get_change.one(W.get_nat(s), 0n)
    case 1n:
      get_change.one(W.get_nat(s), 1n)
    case 2n:
      W.Got{Sb.Drop{}, s}
    case 3n+u:
      W.Bad{}

def get_change(r: W.Dec<Nat>) -> W.Dec<Sb.Change>:
  match r:
    case W.Got{t, s}:
      get_change.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# Replies
# -------

def put_sub(x: Sb.Sub, rest: String) -> String:
  match x:
    case Sb.InQueued{}:
      W.put_nat(0n, rest)
    case Sb.InPlaced{e}:
      W.put_nat(1n, W.put_nat(e, rest))
    case Sb.InAnswered{e, a}:
      W.put_nat(2n, W.put_nat(e, W.put_nat(a, rest)))
    case Sb.InDropped{m}:
      match m:
        case None{}:
          W.put_nat(3n, rest)
        case Some{e}:
          W.put_nat(4n, W.put_nat(e, rest))
    case Sb.WrQueued{}:
      W.put_nat(5n, rest)
    case Sb.WrPlaced{e}:
      W.put_nat(6n, W.put_nat(e, rest))
    case Sb.WrDropped{}:
      W.put_nat(7n, rest)

def put_why(y: Sb.Why, rest: String) -> String:
  match y:
    case Sb.NotQueued{}:
      W.put_nat(0n, rest)
    case Sb.NotPlacedInput{}:
      W.put_nat(1n, rest)

def put_out(o: Sb.Out) -> String:
  match o:
    case Sb.Stays{}:
      W.put_nat(0n, "")
    case Sb.Moves{x}:
      W.put_nat(1n, put_sub(x, ""))
    case Sb.Refused{y}:
      W.put_nat(2n, put_why(y, ""))

# The entry
# ---------

def ffi.done(x: Sb.Sub, c: Sb.Change, end: Bool) -> String:
  match end:
    case True{}:
      put_out(Sb.step(x, c))
    case False{}:
      W.err("submission: input left after the request")

def ffi.change(x: Sb.Sub, r: W.Dec<Sb.Change>) -> String:
  match r:
    case W.Got{c, +s}:
      ffi.done(x, c, W.end(s))
    case W.Bad{}:
      W.err("submission: malformed request")

def ffi.got(r: W.Dec<Sb.Sub>) -> String:
  match r:
    case W.Got{x, s}:
      ffi.change(x, get_change(W.get_nat(s)))
    case W.Bad{}:
      W.err("submission: malformed request")

# the entry: decode the submission and the change, answer the outcome
def ffi(input: String) -> String:
  ffi.got(get_sub(W.get_nat(input)))
