# ffi_gateway_width: the entry of the compiled Bend core for a Signal
# table's layout (bend/gateway_width.bend `layout`; crates/eukhe-gateway/
# src/style.rs `push_table`). The request is the display width of every
# cell, row by row (Rust measures each cell; the model's cell is the list
# of its glyph widths, so a measured cell is one glyph of its width); the
# reply is the width of every column and the pads of every row. Lists of
# lists cross as one list (bend/wire_flat.bend). The wire format is
# bend/wire.bend; malformed input answers the error form.
#
#   request  List<Nat>                     (the rows, flat)
#   reply    List<Nat> List<Nat>           (the widths; the pads, flat)

import Base
import ./wire.bend as W
import ./wire_flat.bend as Fl
import ./gateway_width.bend as Gw

def put_ns(xs: List<&2, Nat>, rest: String) -> String:
  W.put_list(~Nat, ~W.put_nat, xs, rest)

# a measured row as the model reads it: each cell one glyph of its width
def cells(ws: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      [w] <> cells(rest)

def table(rows: List<&2, List<&2, Nat>>) -> List<&2, List<&2, List<&2, Nat>>>:
  match rows:
    case Nil{}:
      Nil{}
    case r <> rest:
      cells(r) <> table(rest)

def put_req(rows: List<&2, List<&2, Nat>>, rest: String) -> String:
  put_ns(Fl.flat(rows), rest)

def get_req.of(m: Maybe<&2, List<&2, List<&2, Nat>>>, s: String) -> W.Dec<List<&2, List<&2, Nat>>>:
  match m:
    case Some{rows}:
      W.Got{rows, s}
    case None{}:
      W.Bad{}

def get_req.ns(r: W.Dec<List<&2, Nat>>) -> W.Dec<List<&2, List<&2, Nat>>>:
  match r:
    case W.Got{ns, s}:
      get_req.of(Fl.unflat(ns), s)
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<List<&2, List<&2, Nat>>>:
  get_req.ns(W.get_list(~Nat, ~W.get_nat, s))

def put_lay(l: Gw.Lay, rest: String) -> String:
  match l:
    case Gw.Lay{w, p}:
      put_ns(w, put_ns(Fl.flat(p), rest))

# the reply to a request read whole (done: nothing is left)
def reply(done: Bool, rows: List<&2, List<&2, Nat>>) -> String:
  match done:
    case True{}:
      put_lay(Gw.layout(table(rows)), "")
    case False{}:
      W.err("gateway_width: input left over")

def answer(r: W.Dec<List<&2, List<&2, Nat>>>) -> String:
  match r:
    case W.Got{rows, s}:
      reply(W.end(s), rows)
    case W.Bad{}:
      W.err("gateway_width: malformed request")

def ffi(input: String) -> String:
  answer(get_req(input))
