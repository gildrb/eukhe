# ffi_doc_publish: the entry of the compiled Bend core for the step of a
# publish after its re-check (bend/doc_publish.bend; Rust: eukhe-bend
# rules/doc_publish.rs, asked by eukhe-docs write.rs publish). Grammar:
# crates/eukhe-bend/WIRE.md.
#
#   request  the rebases done (Nat); then what the re-check met, a tag
#            (Nat): 0 the base, 1 no file, 2 other bytes
#   reply    the step, a tag (Nat): 0 place, 1 rebase, 2 refuse
#
# Malformed input (a tag past 2, a malformed Nat, input left after the
# request) answers `E doc_publish: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./doc_publish.bend as P

# A request of the entry
type Req is Data:
  Req{rebases: Nat, seen: P.Seen}

# what the re-check met, by tag n
def get_req.seen(+k: Nat, n: Nat, s: String) -> W.Dec<Req>:
  match n:
    case 0n:
      W.Got{Req{k, P.Same{}}, s}
    case 1n+a:
      match a:
        case 0n:
          W.Got{Req{k, P.Gone{}}, s}
        case 1n+b:
          match b:
            case 0n:
              W.Got{Req{k, P.Moved{}}, s}
            case 1n+c:
              W.Bad{}

def get_req.tag(+k: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{n, s}:
      get_req.seen(k, n, s)
    case W.Bad{}:
      W.Bad{}

def get_req.rebases(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{+k, s}:
      get_req.tag(k, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.rebases(W.get_nat(s))

# The entry
# ---------

# the reply's tag of a step
def put_step(p: P.Step) -> String:
  match p:
    case P.Place{}:
      W.put_nat(0n, "")
    case P.Rebase{}:
      W.put_nat(1n, "")
    case P.Refuse{}:
      W.put_nat(2n, "")

# the reply of a request: the model's step, encoded
def answer(q: Req) -> String:
  match q:
    case Req{k, s}:
      put_step(P.step(k, s))

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("doc_publish: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("doc_publish: malformed request")

# the entry: decode the request, answer the model's step
def ffi(input: String) -> String:
  ffi.got(get_req(input))
