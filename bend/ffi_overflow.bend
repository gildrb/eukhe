# ffi_overflow: the entry of the compiled Bend core for whether a model
# reply is a context overflow (bend/overflow.bend; Rust: eukhe-bend
# rules/overflow.rs). Grammar: crates/eukhe-bend/WIRE.md.
#
#   stop     0 stop | 1 length | 2 other (tool use, abort) | 3 error
#   request  0, stop, message (String), provider (String), window, input,
#               cache reads, output (Nats)        the overflow question
#            1, stop, desired output, output (Nats)  the recoverable-length
#                                                    question
#   reply    the answer (Bool)
#
# Malformed input, or input left after the request, answers
# `E overflow: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./overflow.bend as O

# A request of the entry
type Req is Data:
  QOverflow{stop: O.Stop, msg: String, provider: String, window: Nat, input: Nat, cache_read: Nat, output: Nat}
  QRecoverable{stop: O.Stop, desired: Nat, output: Nat}

def get_stop.tag(r: W.Dec<Nat>) -> W.Dec<O.Stop>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{O.SStop{}, s}
        case 1n:
          W.Got{O.SLength{}, s}
        case 2n:
          W.Got{O.SOther{}, s}
        case 3n:
          W.Got{O.SError{}, s}
        case 4n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# how the reply stopped, at the start of s
def get_stop(s: String) -> W.Dec<O.Stop>:
  get_stop.tag(W.get_nat(s))

def get_ov.output(st: O.Stop, m: String, p: String, w: Nat, i: Nat, c: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{o, s}:
      W.Got{QOverflow{st, m, p, w, i, c, o}, s}
    case W.Bad{}:
      W.Bad{}

def get_ov.cache(st: O.Stop, m: String, p: String, w: Nat, i: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_ov.output(st, m, p, w, i, c, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_ov.input(st: O.Stop, m: String, p: String, w: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{i, s}:
      get_ov.cache(st, m, p, w, i, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_ov.window(st: O.Stop, m: String, p: String, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{w, s}:
      get_ov.input(st, m, p, w, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_ov.provider(st: O.Stop, m: String, r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{p, s}:
      get_ov.window(st, m, p, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_ov.msg(st: O.Stop, r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{m, s}:
      get_ov.provider(st, m, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_ov(r: W.Dec<O.Stop>) -> W.Dec<Req>:
  match r:
    case W.Got{st, s}:
      get_ov.msg(st, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_rc.output(st: O.Stop, d: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{o, s}:
      W.Got{QRecoverable{st, d, o}, s}
    case W.Bad{}:
      W.Bad{}

def get_rc.desired(st: O.Stop, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{d, s}:
      get_rc.output(st, d, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_rc(r: W.Dec<O.Stop>) -> W.Dec<Req>:
  match r:
    case W.Got{st, s}:
      get_rc.desired(st, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_ov(get_stop(s))
        case 1n:
          get_rc(get_stop(s))
        case 2n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.tag(W.get_nat(s))

# The entry
# ---------

# the reply of a request: the model's answer, encoded
def answer(q: Req) -> String:
  match q:
    case QOverflow{st, m, p, w, i, c, o}:
      W.put_bool(O.overflow(st, m, p, w, i, c, o), "")
    case QRecoverable{st, d, o}:
      W.put_bool(O.recoverable(st, d, o), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("overflow: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("overflow: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(input))
