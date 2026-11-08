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

# The table layout entry, spelled
# -------------------------------
# The entry laws above read and write through the entry's own encoders
# (FGw.put_req, FGw.table, Fl.flat, FGw.put_lay): a drift both sides share
# (a cell offset, the widths and the pads swapped, a measured cell read
# as another) passes them. The laws below spell the request and the reply
# with the wire primitives as Rust writes and reads them (crates/
# eukhe-gateway/src/style.rs `decide`): the rows as one wire list of Nats
# (each cell's display width as 1 + width, each row ended by 0); the
# reply is the width of every column (a wire list of Nats), then every
# row's pads, flat the same way (each pad as 1 + pad, each row ended by
# 0).

# the wire items of the row xs (each 1 + item), its end 0, then rest
def gw_flat_one(xs: List<&2, Nat>, rest: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      0n <> rest
    case x <> t:
      {1n+x : Nat} <> gw_flat_one(t, rest)

# the wire items of the rows xss, in order
def gw_flat(xss: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match xss:
    case Nil{}:
      Nil{}
    case xs <> t:
      gw_flat_one(xs, gw_flat(t))

# a request as Rust spells it: the rows, flat, then rest
def gw_spell_req(rows: List<&2, List<&2, Nat>>, rest: String) -> String:
  LawsBase.wire_spell_nats(gw_flat(rows), rest)

# the count and every item of a request fit the wire
def gw_req_fits(rows: List<&2, List<&2, Nat>>) -> Bool:
  +ns = gw_flat(rows)
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ns)), LawsBase.wire_nats_fit(ns))

# a measured row as the model reads it: each cell one glyph of its width
def gw_cells(ws: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      [w] <> gw_cells(rest)

def gw_table(rows: List<&2, List<&2, Nat>>) -> List<&2, List<&2, List<&2, Nat>>>:
  match rows:
    case Nil{}:
      Nil{}
    case r <> rest:
      gw_cells(r) <> gw_table(rest)

# a layout as Rust reads it: the widths, then the pads, flat
def gw_spell_lay(l: Gw.Lay) -> String:
  match l:
    case Gw.Lay{w, p}:
      LawsBase.wire_spell_nats(w, LawsBase.wire_spell_nats(gw_flat(p), ""))

# the spelled reply to a request: the model's layout of the measured
# table (the laws of section (G) state what it is)
def gw_spell_answer(rows: List<&2, List<&2, Nat>>) -> String:
  gw_spell_lay(Gw.layout(gw_table(rows)))

# LAW gateway_width_ffi_answers_spelled: a table spelled as Rust writes it, every count and width
# within the wire, is answered with the layout of the table whose cells
# are one glyph of their measured width, as Rust reads it: the column
# widths, then the pads, row by row
# EXCLUDES: a request or reply drift both sides of the Bend entry share
#   (a cell or pad offset other than 1, the end mark of a row moved, the
#   widths and the pads swapped), a measured cell split or merged
law gateway_width_ffi_answers_spelled:
  for +rows: List<&2, List<&2, Nat>>
  for fits: {gw_req_fits(rows) == True{} : Bool}
  {FGw.ffi(gw_spell_req(rows, "")) == gw_spell_answer(rows) : String}

# LAW gateway_width_ffi_left_over_spelled: a spelled table that fits, followed by any more input,
# answers the error form "gateway_width: input left over"
# EXCLUDES: trailing input ignored, or read as part of the request, or
#   answered with another error text
law gateway_width_ffi_left_over_spelled:
  for +rows: List<&2, List<&2, Nat>>
  for fits: {gw_req_fits(rows) == True{} : Bool}
  for +c: Char
  for +t: String
  {FGw.ffi(gw_spell_req(rows, SCon{c, t})) == Wr.err("gateway_width: input left over") : String}

# LAW gateway_width_ffi_reads_only_requests: an answer that is not the error form answers a table:
# the input is exactly the spelling of a table whose count and items fit
# the wire, and the answer is the spelled layout
# EXCLUDES: a decoder that accepts items after the last end mark, a short
#   list or input left over, and answers it anyway (a default instead of
#   the error form)
law gateway_width_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FGw.ffi(s)) == False{} : Bool}
  exs rows: List<&2, List<&2, Nat>>
  {(s, (gw_req_fits(rows), FGw.ffi(s))) == (gw_spell_req(rows, ""), (True{}, gw_spell_answer(rows))) : String & (Bool & String)}

# LAW gateway_width_ffi_malformed_unless_request: every answer but the error form "gateway_width:
# malformed request" comes from an input that begins with a spelled table
# that fits (with gateway_width_ffi_answers_spelled and
# gateway_width_ffi_left_over_spelled this pins the entry's answer to
# every input)
# EXCLUDES: the left-over error (or any answer) for input that does not
#   begin with a request, the malformed error spelled with another text
law gateway_width_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FGw.ffi(s), Wr.err("gateway_width: malformed request")) == False{} : Bool}
  exs rows: List<&2, List<&2, Nat>>
  exs rest: String
  {(s, gw_req_fits(rows)) == (gw_spell_req(rows, rest), True{}) : String & Bool}

# LAW gateway_width_ffi_tags_example: anchor: the bytes Rust sends and reads: rows [1, 2] and
# [3] give widths [3, 2] and pads [2], [0]; no rows give no widths and no
# pads; one cell of width 5 gives [5] and an empty pad row; a short row
# [1] over [2, 4] gives [2, 4] and pads [1], [0]; empty cells [0, 0] over
# [0] give [0, 0] (a missing cell is 0 wide) and pads [0], [0]; an item
# after the last end mark and a short list are malformed; input after the
# table is left over
# EXCLUDES: a cell or pad offset both sides of the Bend entry agree on but
#   Rust does not, the widths and the pads swapped, a padded last column
law gateway_width_ffi_tags_example:
  {[FGw.ffi("5,2,3,0,4,0,"), FGw.ffi("0,"), FGw.ffi("2,6,0,"), FGw.ffi("5,2,0,3,5,0,"), FGw.ffi("5,1,1,0,1,0,"), FGw.ffi("1,5,"), FGw.ffi("2,1,"), FGw.ffi("0,x")] == ["2,3,2,4,3,0,1,0,", "0,0,", "1,5,1,0,", "2,2,4,4,2,0,1,0,", "2,0,0,4,1,0,1,0,", Wr.err("gateway_width: malformed request"), Wr.err("gateway_width: malformed request"), Wr.err("gateway_width: input left over")] : List<&2, String>}

# (G) The layout of a measured table, declared
# --------------------------------------------
# layout_widths and layout_pads state the layout with the model's own
# terms (Gw.cols, Gw.col.w, Gw.get.w): a missing cell counted 1 wide, or
# a column never narrower than 1, passes them (a mutation probe found
# both). The laws below state what makes the layout of a table as the
# entry reads it (each cell one glyph of its measured width; crates/
# eukhe-gateway/src/style.rs `layout`) right, without computing one: a
# row and a cell are named by their index (Base's List.get), a short
# row's missing cell is 0 wide. Every cell has a column at least as wide
# (layout_cell_fits) and every column is as wide as one of its cells
# (layout_column_reached): so there are as many columns as the longest
# row has cells, each as wide as its widest cell. Every row has a row of
# pads (layout_pad_rows), one pad per column but the last
# (layout_pads_but_last), and its cell and its pad fill the column's
# width (layout_pad_fills).

# LAW layout_cell_fits: every cell of a measured table has a column in the table's layout,
# at least as wide as the cell
# EXCLUDES: a dropped column (fewer columns than the longest row has
#   cells), a column narrower than one of its cells (a row left out of the
#   column's width, a width from another column, a cell measured by
#   another rule)
law layout_cell_fits:
  for +rows: List<&2, List<&2, Nat>>
  for +j: Nat
  for +r: List<&2, Nat>
  for +i: Nat
  for +c: Nat
  for row: {List.get(&2, List<&2, Nat>, rows, j) == Some{r} : Maybe<&2, List<&2, Nat>>}
  for cell: {List.get(&2, Nat, r, i) == Some{c} : Maybe<&2, Nat>}
  exs w: Nat
  {(List.get(&2, Nat, Gw.Lay.widths(Gw.layout(gw_table(rows))), i), Nat.is_le(c, w)) == (Some{w}, True{}) : Maybe<&2, Nat> & Bool}

# LAW layout_column_reached: every column of the layout of a measured table is exactly as
# wide as a cell in that column: some row has a cell there of the
# column's width
# EXCLUDES: a column wider than its widest cell (a column at least 1
#   wide, a missing cell counted wider than 0, a width summed with
#   anything), a column past the longest row, a column of no cell
law layout_column_reached:
  for +rows: List<&2, List<&2, Nat>>
  for +i: Nat
  for +w: Nat
  for col: {List.get(&2, Nat, Gw.Lay.widths(Gw.layout(gw_table(rows))), i) == Some{w} : Maybe<&2, Nat>}
  exs j: Nat
  exs r: List<&2, Nat>
  {(List.get(&2, List<&2, Nat>, rows, j), List.get(&2, Nat, r, i)) == (Some{r}, Some{w}) : Maybe<&2, List<&2, Nat>> & Maybe<&2, Nat>}

# LAW layout_pad_rows: the layout of a measured table has one row of pads per row of the
# table
# EXCLUDES: a row left without pads, pads for a row that is not there
law layout_pad_rows:
  for +rows: List<&2, List<&2, Nat>>
  {List.length(&2, List<&2, Nat>, Gw.Lay.pads(Gw.layout(gw_table(rows)))) == List.length(&2, List<&2, Nat>, rows) : Nat}

# LAW layout_pads_but_last: every row of pads of the layout of a measured table has one pad
# per column but the last
# EXCLUDES: a padded last column, a pad dropped from a short row
law layout_pads_but_last:
  for +rows: List<&2, List<&2, Nat>>
  for +j: Nat
  for +ps: List<&2, Nat>
  for got: {List.get(&2, List<&2, Nat>, Gw.Lay.pads(Gw.layout(gw_table(rows))), j) == Some{ps} : Maybe<&2, List<&2, Nat>>}
  {List.length(&2, Nat, ps) == Nat.sub(List.length(&2, Nat, Gw.Lay.widths(Gw.layout(gw_table(rows)))), 1n) : Nat}

# LAW layout_pad_fills: in the layout of a measured table, row j's pad i and the cell i of
# row j (0 wide when the row has none) together are exactly as wide as
# column i
# EXCLUDES: a pad by another measure than the cell's, a pad from another
#   column or row, a pad that forgets a missing cell, a misaligned column
law layout_pad_fills:
  for +rows: List<&2, List<&2, Nat>>
  for +j: Nat
  for +r: List<&2, Nat>
  for +ps: List<&2, Nat>
  for +i: Nat
  for +p: Nat
  for row: {List.get(&2, List<&2, Nat>, rows, j) == Some{r} : Maybe<&2, List<&2, Nat>>}
  for pads: {List.get(&2, List<&2, Nat>, Gw.Lay.pads(Gw.layout(gw_table(rows))), j) == Some{ps} : Maybe<&2, List<&2, Nat>>}
  for pad: {List.get(&2, Nat, ps, i) == Some{p} : Maybe<&2, Nat>}
  exs w: Nat
  {(List.get(&2, Nat, Gw.Lay.widths(Gw.layout(gw_table(rows))), i), Nat.add(Maybe.default(&2, Nat, List.get(&2, Nat, r, i), 0n), p)) == (Some{w}, w) : Maybe<&2, Nat> & Nat}
