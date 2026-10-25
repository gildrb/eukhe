# ffi_error_body: the entry of the compiled Bend core for what a
# provider's HTTP error shows (bend/error_body.bend; Rust: eukhe-bend
# rules/error_body.rs). Grammar: crates/eukhe-bend/WIRE.md.
#
#   probe    0 nothing usable | 1, text (String) | 2, object (String: the
#            serialized object, which has a key)
#   request  0, body, error, response (probes)  -> body (Maybe<String>)
#            1, carried (Bool), status, body, prefix (Maybe<String>),
#               message (String)                       -> display (String)
#            2, text (String), cap (Nat)               -> the cut text (String)
#
# Malformed input, or input left after the request, answers
# `E error_body: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./error_body.bend as Eb

# A request of the entry
type Req is Data:
  QBody{b: Eb.Probe, e: Eb.Probe, r: Eb.Probe}
  QShow{c: Bool, st: Maybe<&2, String>, b: Maybe<&2, String>, p: Maybe<&2, String>, m: String}
  QTruncate{t: String, max: Nat}

# Maybe values and probes
# -----------------------

def get_mstr.of(r: W.Dec<String>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_mstr.tag(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{None{}, s}
        case 1n:
          get_mstr.of(W.get_str(s))
        case 2n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# a Maybe<String> at the start of s
def get_mstr(s: String) -> W.Dec<Maybe<&2, String>>:
  get_mstr.tag(W.get_nat(s))

def put_mstr(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{x}:
      W.put_nat(1n, W.put_str(x, rest))

def get_probe.text(r: W.Dec<String>) -> W.Dec<Eb.Probe>:
  match r:
    case W.Got{x, s}:
      W.Got{Eb.PText{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_probe.obj(r: W.Dec<String>) -> W.Dec<Eb.Probe>:
  match r:
    case W.Got{x, s}:
      W.Got{Eb.PObj{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_probe.tag(r: W.Dec<Nat>) -> W.Dec<Eb.Probe>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Eb.PNone{}, s}
        case 1n:
          get_probe.text(W.get_str(s))
        case 2n:
          get_probe.obj(W.get_str(s))
        case 3n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# a probe at the start of s
def get_probe(s: String) -> W.Dec<Eb.Probe>:
  get_probe.tag(W.get_nat(s))

# Requests
# --------

def get_body.r(b: Eb.Probe, e: Eb.Probe, d: W.Dec<Eb.Probe>) -> W.Dec<Req>:
  match d:
    case W.Got{r, s}:
      W.Got{QBody{b, e, r}, s}
    case W.Bad{}:
      W.Bad{}

def get_body.e(b: Eb.Probe, d: W.Dec<Eb.Probe>) -> W.Dec<Req>:
  match d:
    case W.Got{e, s}:
      get_body.r(b, e, get_probe(s))
    case W.Bad{}:
      W.Bad{}

def get_body(d: W.Dec<Eb.Probe>) -> W.Dec<Req>:
  match d:
    case W.Got{b, s}:
      get_body.e(b, get_probe(s))
    case W.Bad{}:
      W.Bad{}

def get_show.m(c: Bool, st: Maybe<&2, String>, b: Maybe<&2, String>, p: Maybe<&2, String>, d: W.Dec<String>) -> W.Dec<Req>:
  match d:
    case W.Got{m, s}:
      W.Got{QShow{c, st, b, p, m}, s}
    case W.Bad{}:
      W.Bad{}

def get_show.p(c: Bool, st: Maybe<&2, String>, b: Maybe<&2, String>, d: W.Dec<Maybe<&2, String>>) -> W.Dec<Req>:
  match d:
    case W.Got{p, s}:
      get_show.m(c, st, b, p, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_show.b(c: Bool, st: Maybe<&2, String>, d: W.Dec<Maybe<&2, String>>) -> W.Dec<Req>:
  match d:
    case W.Got{b, s}:
      get_show.p(c, st, b, get_mstr(s))
    case W.Bad{}:
      W.Bad{}

def get_show.st(c: Bool, d: W.Dec<Maybe<&2, String>>) -> W.Dec<Req>:
  match d:
    case W.Got{st, s}:
      get_show.b(c, st, get_mstr(s))
    case W.Bad{}:
      W.Bad{}

def get_show(d: W.Dec<Bool>) -> W.Dec<Req>:
  match d:
    case W.Got{c, s}:
      get_show.st(c, get_mstr(s))
    case W.Bad{}:
      W.Bad{}

def get_cut.max(t: String, d: W.Dec<Nat>) -> W.Dec<Req>:
  match d:
    case W.Got{n, s}:
      W.Got{QTruncate{t, n}, s}
    case W.Bad{}:
      W.Bad{}

def get_cut(d: W.Dec<String>) -> W.Dec<Req>:
  match d:
    case W.Got{t, s}:
      get_cut.max(t, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_body(get_probe(s))
        case 1n:
          get_show(W.get_bool(s))
        case 2n:
          get_cut(W.get_str(s))
        case 3n+k:
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
    case QBody{b, e, r}:
      put_mstr(Eb.body(b, e, r), "")
    case QShow{c, st, b, p, m}:
      W.put_str(Eb.show(c, st, b, p, m), "")
    case QTruncate{t, max}:
      W.put_str(Eb.truncate(t, max), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("error_body: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("error_body: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(input))
