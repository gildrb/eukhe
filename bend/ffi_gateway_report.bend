# ffi_gateway_report: the entry of the compiled Bend core for what the
# Signal peer hears of a run (bend/gateway_report.bend; Rust:
# crates/eukhe-gateway report.rs). Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  what the gateway held (an answer), the event's answer, and
#            whether the event ends the run:
#            answer  0 nothing | 1 a text (String) | 2 a failure (String)
#                    | 3 stopped
#            end     0 no run end | 1 a run end: whether work still runs
#                    (Bool), what is left (Maybe<String>)
#   reply    what the gateway holds now (an answer), then what it sends
#            (an answer; 0 sends nothing)
#
# Malformed input, or input left after the request, answers
# `E gateway_report: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./gateway_answer.bend as Ga
import ./ffi_gateway_answer.bend as FGa
import ./gateway_report.bend as Gr

# One request
type Req is Data:
  Req{held: Ga.Answer, answer: Ga.Answer, end: Gr.End}

# Requests
# --------

def get_text(r: W.Dec<String>) -> W.Dec<Ga.Answer>:
  match r:
    case W.Got{t, s}:
      W.Got{Ga.AText{t}, s}
    case W.Bad{}:
      W.Bad{}

def get_failed(r: W.Dec<String>) -> W.Dec<Ga.Answer>:
  match r:
    case W.Got{t, s}:
      W.Got{Ga.AFailed{t}, s}
    case W.Bad{}:
      W.Bad{}

def get_answer.tag(t: Nat, s: String) -> W.Dec<Ga.Answer>:
  match t:
    case 0n:
      W.Got{Ga.ANone{}, s}
    case 1n:
      get_text(W.get_str(s))
    case 2n:
      get_failed(W.get_str(s))
    case 3n:
      W.Got{Ga.AStopped{}, s}
    case 4n+u:
      W.Bad{}

# an answer, after the tag r read
def get_answer(r: W.Dec<Nat>) -> W.Dec<Ga.Answer>:
  match r:
    case W.Got{t, s}:
      get_answer.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_run.left(w: Bool, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Gr.End>:
  match r:
    case W.Got{l, s}:
      W.Got{Gr.ERun{w, l}, s}
    case W.Bad{}:
      W.Bad{}

def get_run(r: W.Dec<Bool>) -> W.Dec<Gr.End>:
  match r:
    case W.Got{w, s}:
      get_run.left(w, FGa.get_maybe(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_end.tag(t: Nat, s: String) -> W.Dec<Gr.End>:
  match t:
    case 0n:
      W.Got{Gr.ENone{}, s}
    case 1n:
      get_run(W.get_bool(s))
    case 2n+u:
      W.Bad{}

# whether the event ends the run, after the tag r read
def get_end(r: W.Dec<Nat>) -> W.Dec<Gr.End>:
  match r:
    case W.Got{t, s}:
      get_end.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_req.end(h: Ga.Answer, a: Ga.Answer, r: W.Dec<Gr.End>) -> W.Dec<Req>:
  match r:
    case W.Got{e, s}:
      W.Got{Req{h, a, e}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.answer(h: Ga.Answer, r: W.Dec<Ga.Answer>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      get_req.end(h, a, get_end(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_req.held(r: W.Dec<Ga.Answer>) -> W.Dec<Req>:
  match r:
    case W.Got{h, s}:
      get_req.answer(h, get_answer(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.held(get_answer(W.get_nat(s)))

# The entry
# ---------

# an answer, encoded before rest
def put_answer(a: Ga.Answer, rest: String) -> String:
  match a:
    case Ga.ANone{}:
      W.put_nat(0n, rest)
    case Ga.AText{t}:
      W.put_nat(1n, W.put_str(t, rest))
    case Ga.AFailed{t}:
      W.put_nat(2n, W.put_str(t, rest))
    case Ga.AStopped{}:
      W.put_nat(3n, rest)

# what the gateway holds, then what it sends
def put_out(o: Gr.Out) -> String:
  match o:
    case Gr.Out{h, s}:
      put_answer(h, put_answer(s, ""))

def ffi.done(end: Bool, q: Req) -> String:
  match end:
    case True{}:
      match q:
        case Req{h, a, e}:
          put_out(Gr.step(h, a, e))
    case False{}:
      W.err("gateway_report: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(W.end(s), q)
    case W.Bad{}:
      W.err("gateway_report: malformed request")

# the entry: decode the request, answer the step
def ffi(input: String) -> String:
  ffi.got(get_req(input))
