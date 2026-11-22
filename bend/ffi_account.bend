# ffi_account: the entry of the compiled Bend core for the account of one
# provider a run goes on with (bend/account.bend `choose`; Rust: eukhe-bend
# rules/account.rs). Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  one List<Nat>: now, cap, waits, then the marks in order to
#            the end
#            mark  0 (Free) | 1, t (Until) | 2 (Dead)
#   reply    0, a (use) | 1, a, until (wait) | 2, a, until (quota) |
#            3 (login)
#
# Malformed input, or input left after the request, answers
# `E account: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./account.bend as A

# Decoding
# --------

def marks.cons(m: A.Mark, r: Maybe<&2, List<&2, A.Mark>>) -> Maybe<&2, List<&2, A.Mark>>:
  match r:
    case None{}:
      None{}
    case Some{ms}:
      Some{m <> ms}

# the marks a list of Nats spells to its end, None when it spells none
def marks(xs: List<&2, Nat>) -> Maybe<&2, List<&2, A.Mark>>:
  match xs:
    case Nil{}:
      Some{[]}
    case k <> rest:
      match k:
        case 0n:
          marks.cons(A.Free{}, marks(rest))
        case 1n:
          match rest:
            case Nil{}:
              None{}
            case t <> more:
              marks.cons(A.Until{t}, marks(more))
        case 2n:
          marks.cons(A.Dead{}, marks(rest))
        case 3n+q:
          None{}

def parse.marks(+now: Nat, +cap: Nat, +waits: Nat, r: Maybe<&2, List<&2, A.Mark>>) -> Maybe<&2, A.In>:
  match r:
    case None{}:
      None{}
    case Some{ms}:
      Some{A.In{now, cap, waits, ms}}

# the request a list of Nats spells, None when it spells none
def parse(xs: List<&2, Nat>) -> Maybe<&2, A.In>:
  match xs:
    case Nil{}:
      None{}
    case now <> t:
      match t:
        case Nil{}:
          None{}
        case cap <> u:
          match u:
            case Nil{}:
              None{}
            case waits <> rest:
              parse.marks(now, cap, waits, marks(rest))

# the list at the start of s
def get_req(s: String) -> W.Dec<List<&2, Nat>>:
  W.get_list(~Nat, ~W.get_nat, s)

# The entry
# ---------

# the reply's spelling of a choice
def put_choice(c: A.Choice) -> String:
  match c:
    case A.Use{a}:
      W.put_nat(0n, W.put_nat(a, ""))
    case A.Hold{a, until}:
      W.put_nat(1n, W.put_nat(a, W.put_nat(until, "")))
    case A.Quota{a, until}:
      W.put_nat(2n, W.put_nat(a, W.put_nat(until, "")))
    case A.Login{}:
      W.put_nat(3n, "")

def ffi.parsed(r: Maybe<&2, A.In>) -> String:
  match r:
    case None{}:
      W.err("account: malformed request")
    case Some{x}:
      put_choice(A.choose(x))

def ffi.done(xs: List<&2, Nat>, end: Bool) -> String:
  match end:
    case True{}:
      ffi.parsed(parse(xs))
    case False{}:
      W.err("account: malformed request")

def ffi.got(r: W.Dec<List<&2, Nat>>) -> String:
  match r:
    case W.Got{xs, +s}:
      ffi.done(xs, W.end(s))
    case W.Bad{}:
      W.err("account: malformed request")

# the entry: decode the request, answer the account's choice
def ffi(input: String) -> String:
  ffi.got(get_req(input))
