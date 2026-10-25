# ffi_err_text: the entry of the compiled Bend core for whether provider
# error texts read as one kind of error (bend/err_text.bend; Rust:
# eukhe-bend rules/err_text.rs). Grammar: crates/eukhe-bend/WIRE.md.
#
#   rule     0 limit | 1 transient | 2 codex terminal | 3 codex retryable |
#            4 codex usage code | 5 timeout
#   request  rule (Nat), texts (List<String>)
#   reply    whether the rule holds for one of the texts (Bool; no texts: F)
#
# A rule past 5, malformed input, or input left after the request answers
# `E err_text: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./err_text.bend as E

# A request of the entry
type Req is Data:
  Req{rule: E.Rule, texts: List<&2, String>}

def get_rule.tag(r: W.Dec<Nat>) -> W.Dec<E.Rule>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{E.RLimit{}, s}
        case 1n:
          W.Got{E.RTransient{}, s}
        case 2n:
          W.Got{E.RCodexTerminal{}, s}
        case 3n:
          W.Got{E.RCodexRetryable{}, s}
        case 4n:
          W.Got{E.RCodexUsage{}, s}
        case 5n:
          W.Got{E.RTimeout{}, s}
        case 6n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_req.texts(rule: E.Rule, r: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{ts, s}:
      W.Got{Req{rule, ts}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.rule(r: W.Dec<E.Rule>) -> W.Dec<Req>:
  match r:
    case W.Got{rule, s}:
      get_req.texts(rule, W.get_list(~String, ~W.get_str, s))
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.rule(get_rule.tag(W.get_nat(s)))

# The entry
# ---------

# the reply of a request: the model's answer, encoded
def answer(q: Req) -> String:
  match q:
    case Req{rule, ts}:
      W.put_bool(E.holds(rule, ts), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("err_text: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("err_text: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(input))
