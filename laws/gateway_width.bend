# eukhe: the laws of area gateway_width

import Base
import ../bend/ffi_gateway_width.bend as FGw
import ../bend/gateway_width.bend as Gw
import ../bend/wire.bend as Wr
import ../bend/wire_flat.bend as Fl
import ./base.bend as LawsBase

# ---- gateway_width ----

# LAWS: the Signal gateway aligns a table by display width. Each law is an
# open claim about the model in bend/gateway_width.bend (the formatter
# `push_table` of crates/eukhe-gateway/src/style.rs); PROOF.bend proves
# them (as GatewayWidth.<law>) with the lemmas of
# proof/gateway_width/.

# LAW table_aligned: every row of a formatted table has the same display width per
# column: each row of the table (pre, row, post) renders as the widths of
# the columns, then its own last cell (the last column is not padded)
law table_aligned:
  for +pre: List<&2, List<&2, List<&2, Nat>>>
  for +row: List<&2, List<&2, Nat>>
  for +post: List<&2, List<&2, List<&2, Nat>>>
  {Gw.line(Nat.sub(Gw.cols(List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post)), 1n), Gw.Display{}, List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post), row, 0n) == List.append(&2, Nat, Gw.widths(Nat.sub(Gw.cols(List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post)), 1n), Gw.Display{}, List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post), 0n), [Gw.get.w(row, Gw.Display{}, Nat.sub(Gw.cols(List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post)), 1n))]) : List<&2, Nat>}

# LAW ascii_unchanged: an ASCII table (every glyph 1 wide) renders as the old formatter
# rendered it, which counted the characters of a cell
law ascii_unchanged:
  for +rows: List<&2, List<&2, List<&2, Nat>>>
  for +ones: Gw.Ones.rows(rows)
  {Gw.table(Gw.Display{}, rows) == Gw.table(Gw.Chars{}, rows) : List<&2, List<&2, Nat>>}

# the pads of row from column i over k columns: the width of the column
# less the display width of the row's cell (0 when it has none)
def gw_pads(k: Nat, +rows: List<&2, List<&2, List<&2, Nat>>>, +row: List<&2, List<&2, Nat>>, +i: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      Nat.sub(Gw.col.w(rows, Gw.Display{}, i), Gw.get.w(row, Gw.Display{}, i)) <> gw_pads(p, rows, row, 1n+i)

# the pads of every row of rs over k columns of the table rows
def gw_pads_all(rs: List<&2, List<&2, List<&2, Nat>>>, +k: Nat, +rows: List<&2, List<&2, List<&2, Nat>>>) -> List<&2, List<&2, Nat>>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      gw_pads(k, rows, r, 0n) <> gw_pads_all(rest, k, rows)

# LAW layout_widths: the layout the renderer reads has the width of every column (the
# rule row's `-` runs; the last column too): its widest cell
# EXCLUDES: a rule row narrower or wider than a column, a dropped column
law layout_widths:
  for +rows: List<&2, List<&2, List<&2, Nat>>>
  {Gw.Lay.widths(Gw.layout(rows)) == Gw.widths(Gw.cols(rows), Gw.Display{}, rows, 0n) : List<&2, Nat>}

# LAW layout_pads: the layout pads each row's cell in every column but the last with
# the column's width less the cell's display width, and the last not
# EXCLUDES: a pad by glyph count, a padded last column, a pad that
#   forgets a missing cell (a short row)
law layout_pads:
  for +rows: List<&2, List<&2, List<&2, Nat>>>
  {Gw.Lay.pads(Gw.layout(rows)) == gw_pads_all(rows, Nat.sub(Gw.cols(rows), 1n), rows) : List<&2, List<&2, Nat>>}

# LAW gateway_width_ffi_request_round_trip (compiled core): the table layout entry (bend/ffi_gateway_width.bend) reads back
# the cell widths of a table as Rust writes it, and leaves what follows untouched
# EXCLUDES: a request field misread, dropped, reordered or shifted; a
#   decoder that eats the input after the request
law gateway_width_ffi_request_round_trip:
  for +rows: List<&2, List<&2, Nat>>
  for +rest: String
  for h: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, Fl.flat(rows))), LawsBase.wire_nats_fit(Fl.flat(rows))) == True{} : Bool}
  {FGw.get_req(FGw.put_req(rows, rest)) == Wr.Got{rows, rest} : Wr.Dec<List<&2, List<&2, Nat>>>}

# LAW gateway_width_ffi_answers (compiled core): the table layout entry answers a whole request with the
# model's layout
# EXCLUDES: an entry that answers another rule, a default, or a reply for
#   a request it misread
law gateway_width_ffi_answers:
  for +rows: List<&2, List<&2, Nat>>
  for h: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, Fl.flat(rows))), LawsBase.wire_nats_fit(Fl.flat(rows))) == True{} : Bool}
  {FGw.ffi(FGw.put_req(rows, "")) == FGw.put_lay(Gw.layout(FGw.table(rows)), "") : String}

# LAW gateway_width_ffi_rejects_malformed (compiled core): the table layout entry answers a malformed request with
# the error form, never a default
# EXCLUDES: a decision made on input that is no request
law gateway_width_ffi_rejects_malformed:
  for +s: String
  for bad: {FGw.get_req(s) == Wr.Bad{} : Wr.Dec<List<&2, List<&2, Nat>>>}
  {LawsBase.wire_opens_err(FGw.ffi(s)) == True{} : Bool}

# LAW gateway_width_ffi_rejects_left_over (compiled core): and a request followed by more input with the error
# form
# EXCLUDES: an entry that ignores input left over (a second request, a
#   truncated one)
law gateway_width_ffi_rejects_left_over:
  for +s: String
  for +q: List<&2, List<&2, Nat>>
  for +r: String
  for got: {FGw.get_req(s) == Wr.Got{q, r} : Wr.Dec<List<&2, List<&2, Nat>>>}
  for more: {String.is_empty(r) == False{} : Bool}
  {LawsBase.wire_opens_err(FGw.ffi(s)) == True{} : Bool}
