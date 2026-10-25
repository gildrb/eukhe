# ffi_gateway_commands: the entry of the compiled Bend core for what one
# phone text message means to the Signal gateway
# (bend/gateway_commands.bend; Rust: crates/eukhe-gateway commands.rs).
# Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  the message text (String), the session command names
#            (List<String>)
#   reply    0 a command: its tag (0 help | 1 sessions | 2 use, then its
#              argument (String) | 3 latest | 4 new | 5 stop | 6 status
#              | 7 memory)
#            | 1 an answer: its text (String)
#            | 2 a prompt
#
# Malformed input, or input left after the request, answers
# `E gateway_commands: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./gateway_commands.bend as Gc

# A request of the entry
type Req is Data:
  QParse{text: String, sessions: List<&2, String>}

def get_req.sessions(t: String, r: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{ns, s}:
      W.Got{QParse{t, ns}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.text(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_req.sessions(t, W.get_list(~String, ~W.get_str, s))
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.text(W.get_str(s))

# The entry
# ---------

# a command, encoded
def put_cmd(c: Gc.Cmd) -> String:
  match c:
    case Gc.CHelp{}:
      W.put_nat(0n, "")
    case Gc.CSessions{}:
      W.put_nat(1n, "")
    case Gc.CUse{a}:
      W.put_nat(2n, W.put_str(a, ""))
    case Gc.CLatest{}:
      W.put_nat(3n, "")
    case Gc.CNew{}:
      W.put_nat(4n, "")
    case Gc.CStop{}:
      W.put_nat(5n, "")
    case Gc.CStatus{}:
      W.put_nat(6n, "")
    case Gc.CMemory{}:
      W.put_nat(7n, "")

# what the message means, encoded
def put_out(o: Gc.Out) -> String:
  match o:
    case Gc.OCommand{c}:
      W.put_nat(0n, put_cmd(c))
    case Gc.OAnswer{t}:
      W.put_nat(1n, W.put_str(t, ""))
    case Gc.OPrompt{}:
      W.put_nat(2n, "")

# the reply of a request: the model's parse, encoded
def answer(q: Req) -> String:
  match q:
    case QParse{t, ns}:
      put_out(Gc.parse(t, ns))

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("gateway_commands: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("gateway_commands: malformed request")

# the entry: decode the request, answer the model's parse
def ffi(input: String) -> String:
  ffi.got(get_req(input))
