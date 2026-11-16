# ffi_work_list: the entry of the compiled Bend core for the hand-back of
# a split child's work list (bend/work_list.bend; Rust: eukhe-bend
# rules/work_list.rs, asked by eukhe-core durable/children/task.rs).
# Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  one Bool per item, in the parent's order (List<Bool>: T the
#            child accounted it done)
#   reply    the hand-back, a tag (Nat): 0 finished | 1, then the
#            positions of the items left (List<Nat>)
#
# Malformed input, or input left after the request, answers
# `E work_list: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./work_list.bend as Wl

# the request at the start of s
def get_req(s: String) -> W.Dec<List<&2, Bool>>:
  W.get_list(~Bool, ~W.get_bool, s)

# The entry
# ---------

# the reply's spelling of a hand-back
def put_outcome(o: Wl.Outcome) -> String:
  match o:
    case Wl.Finished{}:
      W.put_nat(0n, "")
    case Wl.Stopped{xs}:
      W.put_nat(1n, W.put_list(~Nat, ~W.put_nat, xs, ""))

# the reply of a request: the model's hand-back, encoded
def answer(done: List<&2, Bool>) -> String:
  put_outcome(Wl.outcome(done))

def ffi.done(done: List<&2, Bool>, end: Bool) -> String:
  match end:
    case True{}:
      answer(done)
    case False{}:
      W.err("work_list: malformed request")

def ffi.got(r: W.Dec<List<&2, Bool>>) -> String:
  match r:
    case W.Got{done, +s}:
      ffi.done(done, W.end(s))
    case W.Bad{}:
      W.err("work_list: malformed request")

# the entry: decode the request, answer the model's hand-back
def ffi(input: String) -> String:
  ffi.got(get_req(input))
