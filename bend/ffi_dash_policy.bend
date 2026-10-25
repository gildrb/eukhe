# ffi_dash_policy: the entry of the compiled Bend core for the
# dashboard's command policy (bend/dash_policy.bend; Rust:
# crates/eukhe-dashboard command_policy.rs). Grammar:
# crates/eukhe-bend/WIRE.md.
#
#   request  the command's `type` (a String)
#   reply    0 for the bound session | 1 catalog (no session id)
#            | 2 refused
#
# Malformed input, or input left after the request, answers
# `E dash_policy: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./dash_policy.bend as Dp

# the request at the start of s
def get_req(s: String) -> W.Dec<String>:
  W.get_str(s)

# the reply tag of a verdict
def tag(v: Dp.Verdict) -> Nat:
  match v:
    case Dp.ForSession{}:
      0n
    case Dp.ForCatalog{}:
      1n
    case Dp.NotRun{}:
      2n

# the reply of a request: the model's verdict, encoded
def answer(+n: String) -> String:
  W.put_nat(tag(Dp.verdict(n)), "")

def ffi.done(n: String, end: Bool) -> String:
  match end:
    case True{}:
      answer(n)
    case False{}:
      W.err("dash_policy: malformed request")

def ffi.got(r: W.Dec<String>) -> String:
  match r:
    case W.Got{n, +s}:
      ffi.done(n, W.end(s))
    case W.Bad{}:
      W.err("dash_policy: malformed request")

# the entry: decode the request, answer the model's verdict
def ffi(input: String) -> String:
  ffi.got(get_req(input))
