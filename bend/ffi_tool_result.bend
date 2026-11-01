# ffi_tool_result: the entry of the compiled Bend core for the blocks a
# tool result sends (bend/tool_result.bend; Rust: eukhe-bend
# rules/tool_result.rs, asked by the eukhe-ai conversions of Anthropic
# Messages and Bedrock Converse). Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  err (Bool: the result is an error), then one Bool per block
#            of its content, in order (List<Bool>: T an image, F a text)
#   reply    one answer per block, in order (List<Out>): 0 keep the block
#            | 1, the text line (String) it is sent as
#
# Malformed input, or input left after the request, answers
# `E tool_result: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./tool_result.bend as Tr

# A request of the entry
type Req is Data:
  Req{err: Bool, imgs: List<&2, Bool>}

def get_req.imgs(err: Bool, r: W.Dec<List<&2, Bool>>) -> W.Dec<Req>:
  match r:
    case W.Got{ks, s}:
      W.Got{Req{err, ks}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.err(r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{e, s}:
      get_req.imgs(e, W.get_list(~Bool, ~W.get_bool, s))
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.err(W.get_bool(s))

# The entry
# ---------

def put_out(o: Tr.Out, rest: String) -> String:
  match o:
    case Tr.Keep{}:
      W.put_nat(0n, rest)
    case Tr.Omit{l}:
      W.put_nat(1n, W.put_str(l, rest))

# the reply of a request: the model's plan, encoded
def answer(q: Req) -> String:
  match q:
    case Req{e, ks}:
      W.put_list(~Tr.Out, ~put_out, Tr.plan(e, ks), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("tool_result: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("tool_result: malformed request")

# the entry: decode the request, answer the model's plan
def ffi(input: String) -> String:
  ffi.got(get_req(input))
