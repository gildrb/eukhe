# ffi_retry_note: the compiled Bend core's entry for the note at the end of
# a retry's request (bend/retry_note.bend). Rust
# `eukhe_bend::rules::retry_note::text` calls it through `eukhe_bend::call`
# once per noted retry.
#
# Request (crates/eukhe-bend/WIRE.md): the attempt (Nat), then the cause,
# its tag then its fields:
#   0 repeated   period (Nat), line (String, already quoted)
#   1 no answer
#   2 length     tokens, row, cap (Nats)
#   3 leaked     markup, reason (Strings), row, cap (Nats)
#   4 redirect   the calls (a List of each call's tool and arguments,
#                Strings), rounds, row, cap (Nats)
#   5 stalled    idle_ms (Nat)
# Reply: the note's text (String).
# A malformed request answers the error form "retry_note: malformed
# request"; input left after the request answers "retry_note: input left
# after the request": never a default. laws/retry_note.bend (section entry)
# states this file's laws. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./retry_note.bend as Rn

# A request of the entry
type Req is Data:
  Req{attempt: Nat, cause: Rn.Cause}

# Requests
# --------

def get_call.args(t: String, r: W.Dec<String>) -> W.Dec<Rn.Call>:
  match r:
    case W.Got{a, s}:
      W.Got{Rn.Call{t, a}, s}
    case W.Bad{}:
      W.Bad{}

def get_call.tool(r: W.Dec<String>) -> W.Dec<Rn.Call>:
  match r:
    case W.Got{t, s}:
      get_call.args(t, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

# one call: its tool, then its arguments
def get_call(s: String) -> W.Dec<Rn.Call>:
  get_call.tool(W.get_str(s))

# three Nats in a row
type Three is Data:
  Three{a: Nat, b: Nat, c: Nat}

def get_three.c(a: Nat, b: Nat, r: W.Dec<Nat>) -> W.Dec<Three>:
  match r:
    case W.Got{c, s}:
      W.Got{Three{a, b, c}, s}
    case W.Bad{}:
      W.Bad{}

def get_three.b(a: Nat, r: W.Dec<Nat>) -> W.Dec<Three>:
  match r:
    case W.Got{b, s}:
      get_three.c(a, b, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_three(r: W.Dec<Nat>) -> W.Dec<Three>:
  match r:
    case W.Got{a, s}:
      get_three.b(a, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_repeated.line(p: Nat, r: W.Dec<String>) -> W.Dec<Rn.Cause>:
  match r:
    case W.Got{l, s}:
      W.Got{Rn.Repeated{p, l}, s}
    case W.Bad{}:
      W.Bad{}

def get_repeated(r: W.Dec<Nat>) -> W.Dec<Rn.Cause>:
  match r:
    case W.Got{p, s}:
      get_repeated.line(p, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_length(r: W.Dec<Three>) -> W.Dec<Rn.Cause>:
  match r:
    case W.Got{x, s}:
      match x:
        case Three{t, w, k}:
          W.Got{Rn.Length{t, w, k}, s}
    case W.Bad{}:
      W.Bad{}

def get_leaked.cap(m: String, why: String, w: Nat, r: W.Dec<Nat>) -> W.Dec<Rn.Cause>:
  match r:
    case W.Got{k, s}:
      W.Got{Rn.Leaked{m, why, w, k}, s}
    case W.Bad{}:
      W.Bad{}

def get_leaked.row(m: String, why: String, r: W.Dec<Nat>) -> W.Dec<Rn.Cause>:
  match r:
    case W.Got{w, s}:
      get_leaked.cap(m, why, w, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_leaked.reason(m: String, r: W.Dec<String>) -> W.Dec<Rn.Cause>:
  match r:
    case W.Got{why, s}:
      get_leaked.row(m, why, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_leaked(r: W.Dec<String>) -> W.Dec<Rn.Cause>:
  match r:
    case W.Got{m, s}:
      get_leaked.reason(m, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_redirect.counts(cs: List<&2, Rn.Call>, r: W.Dec<Three>) -> W.Dec<Rn.Cause>:
  match r:
    case W.Got{x, s}:
      match x:
        case Three{n, w, k}:
          W.Got{Rn.Redirect{cs, n, w, k}, s}
    case W.Bad{}:
      W.Bad{}

def get_redirect(r: W.Dec<List<&2, Rn.Call>>) -> W.Dec<Rn.Cause>:
  match r:
    case W.Got{cs, s}:
      get_redirect.counts(cs, get_three(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_stalled(r: W.Dec<Nat>) -> W.Dec<Rn.Cause>:
  match r:
    case W.Got{ms, s}:
      W.Got{Rn.Stalled{ms}, s}
    case W.Bad{}:
      W.Bad{}

def get_cause(r: W.Dec<Nat>) -> W.Dec<Rn.Cause>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_repeated(W.get_nat(s))
        case 1n:
          W.Got{Rn.NoAnswer{}, s}
        case 2n:
          get_length(get_three(W.get_nat(s)))
        case 3n:
          get_leaked(W.get_str(s))
        case 4n:
          get_redirect(W.get_list(~Rn.Call, ~get_call, s))
        case 5n:
          get_stalled(W.get_nat(s))
        case 6n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_req.cause(a: Nat, r: W.Dec<Rn.Cause>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      W.Got{Req{a, c}, s}
    case W.Bad{}:
      W.Bad{}

def get_req(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      get_req.cause(a, get_cause(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

# The entry
# ---------

def ffi.done(q: Req, end: Bool) -> String:
  match q:
    case Req{a, c}:
      match end:
        case True{}:
          W.put_str(Rn.text(a, c), "")
        case False{}:
          W.err("retry_note: input left after the request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("retry_note: malformed request")

# the entry: decode the attempt and the cause, answer the note's text
def ffi(input: String) -> String:
  ffi.got(get_req(W.get_nat(input)))
