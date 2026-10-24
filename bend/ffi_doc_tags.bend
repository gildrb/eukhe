# ffi_doc_tags: the entry of the compiled Bend core for grep's tags
# (bend/doc_tags.bend `fates`; Rust: crates/eukhe-docs/src/grep/mod.rs).
# The request is how grep searched each file of a page, in order; the
# reply is what grep does with each file's tag (crates/eukhe-bend/WIRE.md
# is the grammar):
#
#   request  List<Scan>   Scan = 0 Part | 1 Whole{utf8: Bool}
#   reply    List<Fate>   Fate = 0 Tagged | 1 OverLimit | 2 NotUtf8
#
# Malformed input, or input left after the request, answers
# `E doc_tags: malformed request`, never a default. Pure: no IO, no
# @unsafe.

import Base
import ./wire.bend as W
import ./doc_tags.bend as Dt

def get_scan.whole(r: W.Dec<Bool>) -> W.Dec<Dt.Scan>:
  match r:
    case W.Got{u, s}:
      W.Got{Dt.Whole{u}, s}
    case W.Bad{}:
      W.Bad{}

def get_scan.tag(t: Nat, s: String) -> W.Dec<Dt.Scan>:
  match t:
    case 0n:
      W.Got{Dt.Part{}, s}
    case 1n:
      get_scan.whole(W.get_bool(s))
    case 2n+u:
      W.Bad{}

def get_scan.start(r: W.Dec<Nat>) -> W.Dec<Dt.Scan>:
  match r:
    case W.Got{t, s}:
      get_scan.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_scan(s: String) -> W.Dec<Dt.Scan>:
  get_scan.start(W.get_nat(s))

def get_req(s: String) -> W.Dec<List<&2, Dt.Scan>>:
  W.get_list(~Dt.Scan, ~get_scan, s)

def put_fate(f: Dt.Fate, rest: String) -> String:
  match f:
    case Dt.Tagged{}:
      W.put_nat(0n, rest)
    case Dt.OverLimit{}:
      W.put_nat(1n, rest)
    case Dt.NotUtf8{}:
      W.put_nat(2n, rest)

# the reply of a request: the model's choice for each file, encoded
def answer(ss: List<&2, Dt.Scan>) -> String:
  W.put_list(~Dt.Fate, ~put_fate, Dt.fates(ss), "")

def ffi.done(ss: List<&2, Dt.Scan>, end: Bool) -> String:
  match end:
    case True{}:
      answer(ss)
    case False{}:
      W.err("doc_tags: malformed request")

def ffi.got(r: W.Dec<List<&2, Dt.Scan>>) -> String:
  match r:
    case W.Got{ss, +s}:
      ffi.done(ss, W.end(s))
    case W.Bad{}:
      W.err("doc_tags: malformed request")

# the entry: decode the request, answer the model's choices
def ffi(input: String) -> String:
  ffi.got(get_req(input))
