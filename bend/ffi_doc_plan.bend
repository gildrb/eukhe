# ffi_doc_plan: the compiled Bend core's entry for what a session commit
# writes and publishes for one staged document (bend/doc_plan.bend). Rust
# `eukhe_bend::rules::doc_plan` calls it through `eukhe_bend::call` once
# per staged document of a commit.
#
# Request (crates/eukhe-bend/WIRE.md), a question:
#   tag 0  content: the stored version, the definition's version (Nats),
#          whether operations are staged (Bool)
#          -> the content: 0 nothing, 1 a new base, 2 a delta (Nat)
#   tag 1  publishes: whether the plan retires its document (Bool), its
#          change (0 none, 1 a created document's, 2 a loaded
#          incarnation's), whether it writes content (Bool)
#          -> whether adoption publishes it (Bool)
# A malformed request answers the error form "doc_plan: malformed
# request"; input left after the request answers "doc_plan: input left
# after the request": never a default. laws/doc_plan.bend (section entry)
# states this file's laws. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./doc_plan.bend as Dp

# A request of the entry
type Req is Data:
  # the content of a loaded incarnation
  QContent{stored: Nat, version: Nat, ops: Bool}
  # whether adoption publishes a plan
  QPublishes{retire: Bool, change: Dp.Change, writes: Bool}

# Requests
# --------

def get_content.ops(s1: Nat, v: Nat, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{o, s}:
      W.Got{QContent{s1, v, o}, s}
    case W.Bad{}:
      W.Bad{}

def get_content.version(s1: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{v, s}:
      get_content.ops(s1, v, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_content(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{s1, s}:
      get_content.version(s1, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_publishes.writes(re: Bool, c: Dp.Change, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{w, s}:
      W.Got{QPublishes{re, c, w}, s}
    case W.Bad{}:
      W.Bad{}

def get_publishes.change(re: Bool, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_publishes.writes(re, Dp.NoChange{}, W.get_bool(s))
        case 1n:
          get_publishes.writes(re, Dp.Fresh{}, W.get_bool(s))
        case 2n:
          get_publishes.writes(re, Dp.OfLoaded{}, W.get_bool(s))
        case 3n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_publishes(r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{re, s}:
      get_publishes.change(re, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_content(W.get_nat(s))
        case 1n:
          get_publishes(W.get_bool(s))
        case 2n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# Replies
# -------

def put_content(c: Dp.Content) -> String:
  match c:
    case Dp.Kept{}:
      W.put_nat(0n, "")
    case Dp.NewBase{}:
      W.put_nat(1n, "")
    case Dp.NewDelta{}:
      W.put_nat(2n, "")

# The entry
# ---------

def ffi.done(q: Req, end: Bool) -> String:
  match q:
    case QContent{s1, v, o}:
      match end:
        case True{}:
          put_content(Dp.content(s1, v, o))
        case False{}:
          W.err("doc_plan: input left after the request")
    case QPublishes{re, c, w}:
      match end:
        case True{}:
          W.put_bool(Dp.publishes(re, c, w), "")
        case False{}:
          W.err("doc_plan: input left after the request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("doc_plan: malformed request")

# the entry: decode the question, answer it
def ffi(input: String) -> String:
  ffi.got(get_req(W.get_nat(input)))
