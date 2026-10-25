# ffi_gateway_answer: the entry of the compiled Bend core for what a
# settled session event tells the Signal peer (bend/gateway_answer.bend;
# Rust: crates/eukhe-gateway answer.rs). Grammar:
# crates/eukhe-bend/WIRE.md.
#
#   request  an event (Ev):
#            0 agent end: whether an assistant message ran (Bool)
#            1 assistant message: its stop (0 stop | 1 length | 2 error
#              | 3 aborted | 4 tool use), its text blocks (List<String>),
#              its error (Maybe<String>)
#            2 turn end: whether it carries an assistant message (Bool),
#              its error (Maybe<String>)
#            3 any other event
#   reply    0 nothing | 1 the text (String) | 2 the reason (String)
#            | 3 stopped
#
# Malformed input, or input left after the request, answers
# `E gateway_answer: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./gateway_answer.bend as Ga

# Requests
# --------

def get_strs(s: String) -> W.Dec<List<&2, String>>:
  W.get_list(~String, ~W.get_str, s)

def get_some(r: W.Dec<String>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_maybe.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, String>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_some(W.get_str(s))
    case 2n+u:
      W.Bad{}

# a Maybe<String> at the start of s
def get_maybe(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{t, s}:
      get_maybe.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_stop.tag(t: Nat, s: String) -> W.Dec<Ga.Stop>:
  match t:
    case 0n:
      W.Got{Ga.SStop{}, s}
    case 1n:
      W.Got{Ga.SLength{}, s}
    case 2n:
      W.Got{Ga.SError{}, s}
    case 3n:
      W.Got{Ga.SAborted{}, s}
    case 4n:
      W.Got{Ga.SToolUse{}, s}
    case 5n+u:
      W.Bad{}

def get_stop(r: W.Dec<Nat>) -> W.Dec<Ga.Stop>:
  match r:
    case W.Got{t, s}:
      get_stop.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_agent(r: W.Dec<Bool>) -> W.Dec<Ga.Ev>:
  match r:
    case W.Got{a, s}:
      W.Got{Ga.EAgentEnd{a}, s}
    case W.Bad{}:
      W.Bad{}

def get_assistant.error(st: Ga.Stop, ts: List<&2, String>, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Ga.Ev>:
  match r:
    case W.Got{e, s}:
      W.Got{Ga.EAssistant{st, ts, e}, s}
    case W.Bad{}:
      W.Bad{}

def get_assistant.texts(st: Ga.Stop, r: W.Dec<List<&2, String>>) -> W.Dec<Ga.Ev>:
  match r:
    case W.Got{ts, s}:
      get_assistant.error(st, ts, get_maybe(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_assistant(r: W.Dec<Ga.Stop>) -> W.Dec<Ga.Ev>:
  match r:
    case W.Got{st, s}:
      get_assistant.texts(st, get_strs(s))
    case W.Bad{}:
      W.Bad{}

def get_turn.error(a: Bool, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Ga.Ev>:
  match r:
    case W.Got{e, s}:
      W.Got{Ga.ETurnEnd{a, e}, s}
    case W.Bad{}:
      W.Bad{}

def get_turn(r: W.Dec<Bool>) -> W.Dec<Ga.Ev>:
  match r:
    case W.Got{a, s}:
      get_turn.error(a, get_maybe(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Ga.Ev>:
  match t:
    case 0n:
      get_agent(W.get_bool(s))
    case 1n:
      get_assistant(get_stop(W.get_nat(s)))
    case 2n:
      get_turn(W.get_bool(s))
    case 3n:
      W.Got{Ga.EOther{}, s}
    case 4n+u:
      W.Bad{}

def get_req.start(r: W.Dec<Nat>) -> W.Dec<Ga.Ev>:
  match r:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Ga.Ev>:
  get_req.start(W.get_nat(s))

# The entry
# ---------

# an answer, encoded
def put_answer(a: Ga.Answer) -> String:
  match a:
    case Ga.ANone{}:
      W.put_nat(0n, "")
    case Ga.AText{t}:
      W.put_nat(1n, W.put_str(t, ""))
    case Ga.AFailed{t}:
      W.put_nat(2n, W.put_str(t, ""))
    case Ga.AStopped{}:
      W.put_nat(3n, "")

def ffi.done(ev: Ga.Ev, end: Bool) -> String:
  match end:
    case True{}:
      put_answer(Ga.answer(ev))
    case False{}:
      W.err("gateway_answer: malformed request")

def ffi.got(r: W.Dec<Ga.Ev>) -> String:
  match r:
    case W.Got{ev, +s}:
      ffi.done(ev, W.end(s))
    case W.Bad{}:
      W.err("gateway_answer: malformed request")

# the entry: decode the event, answer the model's answer
def ffi(input: String) -> String:
  ffi.got(get_req(input))
