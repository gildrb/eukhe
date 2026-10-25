# ffi_slash_suggest: the entry of the compiled Bend core for the command
# a mistyped slash command most likely meant (bend/slash_suggest.bend;
# Rust: eukhe-bend rules/slash.rs). Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  the typed name (String), the candidate names (List<String>)
#   reply    the candidate to suggest: 0 none | 1, its index (Nat)
#
# Malformed input, or input left after the request, answers
# `E slash_suggest: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./slash_suggest.bend as Ss

# A request of the entry
type Req is Data:
  QSuggest{typed: String, names: List<&2, String>}

def get_req.names(w: String, r: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{cs, s}:
      W.Got{QSuggest{w, cs}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.typed(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{w, s}:
      get_req.names(w, W.get_list(~String, ~W.get_str, s))
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.typed(W.get_str(s))

# The entry
# ---------

def put_answer(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      W.put_nat(0n, "")
    case Some{j}:
      W.put_nat(1n, W.put_nat(j, ""))

# the reply of a request: the model's suggestion, encoded
def answer(q: Req) -> String:
  match q:
    case QSuggest{w, cs}:
      put_answer(Ss.suggest(w, cs))

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("slash_suggest: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("slash_suggest: malformed request")

# the entry: decode the request, answer the model's suggestion
def ffi(input: String) -> String:
  ffi.got(get_req(input))
