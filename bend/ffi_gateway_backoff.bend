# ffi_gateway_backoff: the entry of the compiled Bend core for the Signal
# gateway's reconnect wait (bend/gateway_backoff.bend; Rust:
# crates/eukhe-gateway link.rs). Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  the last wait: 0 none | 1, the wait in ms (Nat)
#   reply    the next wait in ms (Nat)
#
# Malformed input, or input left after the request, answers
# `E gateway_backoff: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./gateway_backoff.bend as Gb

def get_req.some(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{d, s}:
      W.Got{Some{d}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_req.some(W.get_nat(s))
    case 2n+u:
      W.Bad{}

def get_req.start(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Maybe<&2, Nat>>:
  get_req.start(W.get_nat(s))

def ffi.done(m: Maybe<&2, Nat>, end: Bool) -> String:
  match end:
    case True{}:
      W.put_nat(Gb.next(m), "")
    case False{}:
      W.err("gateway_backoff: malformed request")

def ffi.got(r: W.Dec<Maybe<&2, Nat>>) -> String:
  match r:
    case W.Got{m, +s}:
      ffi.done(m, W.end(s))
    case W.Bad{}:
      W.err("gateway_backoff: malformed request")

# the entry: decode the last wait, answer the next one
def ffi(input: String) -> String:
  ffi.got(get_req(input))
