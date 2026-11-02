# ffi_thread: the entry of the compiled Bend core for the history a
# session's request keeps (bend/thread.bend; Rust: eukhe-bend
# rules/thread.rs, asked by eukhe-core memory/view.rs View::kept, with
# which the chat's owner cuts a turn's history and checks it is settled).
# Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  one list of Nats: through (the messages the chat holds),
#            verbatim (the ones the transcript still holds), then the
#            first message of each view line, oldest first
#   reply    how many leading view lines the request keeps (Nat)
#
# Malformed input (a list of fewer than two Nats), or input left after the
# request, answers `E thread: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./thread.bend as Th

# A request of the entry
type Req is Data:
  Req{through: Nat, verbatim: Nat, starts: List<&2, Nat>}

def get_req.of(ns: List<&2, Nat>, s: String) -> W.Dec<Req>:
  match ns:
    case Nil{}:
      W.Bad{}
    case t <> more:
      match more:
        case Nil{}:
          W.Bad{}
        case v <> xs:
          W.Got{Req{t, v, xs}, s}

def get_req.got(r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{ns, s}:
      get_req.of(ns, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.got(W.get_list(~Nat, ~W.get_nat, s))

# The entry
# ---------

# the reply of a request: the model's count, encoded
def answer(q: Req) -> String:
  match q:
    case Req{t, v, xs}:
      W.put_nat(Th.history_lines(t, v, xs), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("thread: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("thread: malformed request")

# the entry: decode the request, answer the model's count
def ffi(input: String) -> String:
  ffi.got(get_req(input))
