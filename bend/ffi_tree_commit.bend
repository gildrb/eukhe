# ffi_tree_commit: the entry of the compiled Bend core for the order in
# which the state tree records a commit's changes (bend/tree_commit.bend
# `order`; Rust: crates/eukhe-durable/src/tree/state.rs `apply_commit`).
# The request is the commit's changes in order; the reply is the order
# of their results (crates/eukhe-bend/WIRE.md is the grammar):
#
#   request  List<Ch>    Ch  = 0 Here{key: Nat} | 1 Under{key: Nat, up: Nat}
#                              | 2 Gone
#   reply    List<Res>   Res = 0 Apply{i: Nat} | 1 Orphan{i: Nat}
#                              | 2 Retire{i: Nat}
#
# Malformed input, or input left after the request, answers
# `E tree_commit: malformed request`, never a default. Pure: no IO, no
# @unsafe.

import Base
import ./wire.bend as W
import ./tree_commit.bend as Tc

def get_ch.up(k: Nat, r: W.Dec<Nat>) -> W.Dec<Tc.Ch>:
  match r:
    case W.Got{u, s}:
      W.Got{Tc.Under{k, u}, s}
    case W.Bad{}:
      W.Bad{}

def get_ch.wait(r: W.Dec<Nat>) -> W.Dec<Tc.Ch>:
  match r:
    case W.Got{k, s}:
      get_ch.up(k, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_ch.here(r: W.Dec<Nat>) -> W.Dec<Tc.Ch>:
  match r:
    case W.Got{k, s}:
      W.Got{Tc.Here{k}, s}
    case W.Bad{}:
      W.Bad{}

def get_ch.start(r: W.Dec<Nat>) -> W.Dec<Tc.Ch>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_ch.here(W.get_nat(s))
        case 1n:
          get_ch.wait(W.get_nat(s))
        case 2n:
          W.Got{Tc.Gone{}, s}
        case 3n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# a change: its tag, then its key (and its parent's key for Wait)
def get_ch(s: String) -> W.Dec<Tc.Ch>:
  get_ch.start(W.get_nat(s))

def get_req(s: String) -> W.Dec<List<&2, Tc.Ch>>:
  W.get_list(~Tc.Ch, ~get_ch, s)

def put_res(r: Tc.Res, rest: String) -> String:
  match r:
    case Tc.Apply{i}:
      W.put_nat(0n, W.put_nat(i, rest))
    case Tc.Orphan{i}:
      W.put_nat(1n, W.put_nat(i, rest))
    case Tc.Retire{i}:
      W.put_nat(2n, W.put_nat(i, rest))

# the reply of a request: the model's order, encoded
def answer(+cs: List<&2, Tc.Ch>) -> String:
  W.put_list(~Tc.Res, ~put_res, Tc.order(cs), "")

def ffi.done(cs: List<&2, Tc.Ch>, end: Bool) -> String:
  match end:
    case True{}:
      answer(cs)
    case False{}:
      W.err("tree_commit: malformed request")

def ffi.got(r: W.Dec<List<&2, Tc.Ch>>) -> String:
  match r:
    case W.Got{cs, +s}:
      ffi.done(cs, W.end(s))
    case W.Bad{}:
      W.err("tree_commit: malformed request")

# the entry: decode the request, answer the model's order
def ffi(input: String) -> String:
  ffi.got(get_req(input))
