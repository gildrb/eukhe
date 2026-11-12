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
# A law that states the layout with the model's own terms (Gw.cols,
# Gw.col.w, Gw.get.w) lets a missing cell counted 1 wide, or a column
# never narrower than 1, pass (a mutation probe found both). The laws
# below state what makes the layout of a table as the
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

# The entry from the requirement
# ------------------------------
# The spec of the whole entry, written from the requirement (the Signal
# gateway aligns a table by display width: each column as wide as its
# widest cell, each cell but the last column's padded to its column) and
# the wire's primitives only: no function of bend/gateway_width.bend,
# bend/ffi_gateway_width.bend or bend/wire_flat.bend. A measured row is
# the display width of each of its cells.

# the width of cell i of a measured row, 0 when the row has no cell i
def gw_sp_cell(row: List<&2, Nat>, i: Nat) -> Nat:
  match row:
    case Nil{}:
      0n
    case w <> rest:
      match i:
        case 0n:
          w
        case 1n+p:
          gw_sp_cell(rest, p)

# the width of column i: its widest cell
def gw_sp_colw(rows: List<&2, List<&2, Nat>>, +i: Nat) -> Nat:
  match rows:
    case Nil{}:
      0n
    case r <> rest:
      Nat.max(gw_sp_cell(r, i), gw_sp_colw(rest, i))

# the count of columns: the longest row
def gw_sp_cols(rows: List<&2, List<&2, Nat>>) -> Nat:
  match rows:
    case Nil{}:
      0n
    case r <> rest:
      Nat.max(List.length(&2, Nat, r), gw_sp_cols(rest))

# the widths of the k columns from column i
def gw_sp_widths(k: Nat, +rows: List<&2, List<&2, Nat>>, +i: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      gw_sp_colw(rows, i) <> gw_sp_widths(p, rows, 1n+i)

# the pads of row over the k columns from column i: the column's width
# less the cell's
def gw_sp_pads(k: Nat, +rows: List<&2, List<&2, Nat>>, +row: List<&2, Nat>, +i: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      Nat.sub(gw_sp_colw(rows, i), gw_sp_cell(row, i)) <> gw_sp_pads(p, rows, row, 1n+i)

# the pads of every row of rs over k columns of the table rows
def gw_sp_pads_all(rs: List<&2, List<&2, Nat>>, +k: Nat, +rows: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      gw_sp_pads(k, rows, r, 0n) <> gw_sp_pads_all(rest, k, rows)

# a list of lists as one list of Nats: each item as 1 + item, each inner
# list closed by 0 ([[4], [], [0, 7]] is [5, 0, 0, 1, 8, 0])
def gw_sp_marked(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      [0n]
    case x <> rest:
      {1n+x : Nat} <> gw_sp_marked(rest)

def gw_sp_flat(xss: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match xss:
    case Nil{}:
      Nil{}
    case xs <> rest:
      List.append(&2, Nat, gw_sp_marked(xs), gw_sp_flat(rest))

def gw_sp_rows.cons(row: List<&2, Nat>, m: Maybe<&2, List<&2, List<&2, Nat>>>) -> Maybe<&2, List<&2, List<&2, Nat>>>:
  match m:
    case None{}:
      None{}
    case Some{rows}:
      Some{row <> rows}

# the lists a flat list of Nats spells, read from the front, cur the items
# read since the last 0; none when items follow the last 0
def gw_sp_rows(ns: List<&2, Nat>, cur: List<&2, Nat>) -> Maybe<&2, List<&2, List<&2, Nat>>>:
  match ns:
    case Nil{}:
      match cur:
        case Nil{}:
          Some{Nil{}}
        case c <> t:
          None{}
    case n <> rest:
      match n:
        case 0n:
          gw_sp_rows.cons(cur, gw_sp_rows(rest, Nil{}))
        case 1n+x:
          gw_sp_rows(rest, List.append(&2, Nat, cur, [x]))

def gw_sp_read.of(m: Maybe<&2, List<&2, List<&2, Nat>>>, s: String) -> Wr.Dec<List<&2, List<&2, Nat>>>:
  match m:
    case Some{rows}:
      Wr.Got{rows, s}
    case None{}:
      Wr.Bad{}

def gw_sp_read.ns(r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<List<&2, List<&2, Nat>>>:
  match r:
    case Wr.Got{ns, s}:
      gw_sp_read.of(gw_sp_rows(ns, Nil{}), s)
    case Wr.Bad{}:
      Wr.Bad{}

# the measured rows s starts with (one list of Nats, flat), and what
# follows
def gw_sp_read(s: String) -> Wr.Dec<List<&2, List<&2, Nat>>>:
  gw_sp_read.ns(Wr.get_list(~Nat, ~Wr.get_nat, s))

# the reply to measured rows: the width of every column, then the pads
# of every row (flat)
def gw_sp_reply(+rows: List<&2, List<&2, Nat>>) -> String:
  +k = gw_sp_cols(rows)
  Wr.put_list(~Nat, ~Wr.put_nat, gw_sp_widths(k, rows, 0n), Wr.put_list(~Nat, ~Wr.put_nat, gw_sp_flat(gw_sp_pads_all(rows, Nat.sub(k, 1n), rows)), ""))

def gw_sp.end(whole: Bool, rows: List<&2, List<&2, Nat>>) -> String:
  match whole:
    case True{}:
      gw_sp_reply(rows)
    case False{}:
      Wr.err("gateway_width: input left over")

def gw_sp.run(r: Wr.Dec<List<&2, List<&2, Nat>>>) -> String:
  match r:
    case Wr.Got{rows, s}:
      gw_sp.end(Wr.end(s), rows)
    case Wr.Bad{}:
      Wr.err("gateway_width: malformed request")

# the entry's answer to the input s
def gw_spec(s: String) -> String:
  gw_sp.run(gw_sp_read(s))

# LAW gateway_width_ffi_exact (compiled core): on every input the table layout entry answers the
# spec's layout of the measured rows the input is exactly (every column's
# width, its widest cell; every row's pads, its column's width less its
# cell, in every column but the last), exactly "gateway_width: input left
# over" for rows followed by more input, and exactly "gateway_width:
# malformed request" for any other input
# EXCLUDES: a column width other than its widest cell, a pad of the last
#   column, a pad by another measure, a dropped or invented column or row,
#   a default for malformed input, a misread request, input left over
#   ignored, another error text
law gateway_width_ffi_exact:
  for +s: String
  {FGw.ffi(s) == gw_spec(s) : String}

# The table from the glyphs
# -------------------------
# The spec of the layout on a table of glyph widths, from the
# requirement and the measured-row helpers above only: no function of
# bend/gateway_width.bend. A cell is measured by display width (the sum
# of its glyph widths) or, by the old formatter, by its count of glyphs.

# the display width of a cell: the sum of its glyph widths
def gw_sp_sum(c: List<&2, Nat>) -> Nat:
  match c:
    case Nil{}:
      0n
    case w <> rest:
      Nat.add(w, gw_sp_sum(rest))

# a cell's width by the measure m: its display width, or its count of
# glyphs
def gw_sp_glyphs(m: Gw.Measure, c: List<&2, Nat>) -> Nat:
  match m:
    case Gw.Display{}:
      gw_sp_sum(c)
    case Gw.Chars{}:
      List.length(&2, Nat, c)

# a row measured by m: the width of each of its cells
def gw_sp_mrow(+m: Gw.Measure, row: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match row:
    case Nil{}:
      Nil{}
    case c <> rest:
      gw_sp_glyphs(m, c) <> gw_sp_mrow(m, rest)

# a table measured by m: each of its rows measured
def gw_sp_measure(+m: Gw.Measure, rows: List<&2, List<&2, List<&2, Nat>>>) -> List<&2, List<&2, Nat>>:
  match rows:
    case Nil{}:
      Nil{}
    case r <> rest:
      gw_sp_mrow(m, r) <> gw_sp_measure(m, rest)

# the layout of a measured table: the width of every column, and every
# row's pads in every column but the last
def gw_sp_layout(+rows: List<&2, List<&2, Nat>>) -> Gw.Lay:
  +k = gw_sp_cols(rows)
  Gw.Lay{gw_sp_widths(k, rows, 0n), gw_sp_pads_all(rows, Nat.sub(k, 1n), rows)}

# LAW layout_exact: the layout the renderer reads of any table of glyph widths is
# the spec's layout of the table measured by display width (a cell's
# width the sum of its glyph widths): every column's width its widest
# cell, every row's pads the column's width less its cell's, in every
# column but the last
# EXCLUDES: a cell measured by glyph count or by its first glyph (a CJK
#   cell [2, 2] measured 3 by `w + length(rest)`), a column width other
#   than its widest cell, a dropped or invented column, row or pad
law layout_exact:
  for +rows: List<&2, List<&2, List<&2, Nat>>>
  {Gw.layout(rows) == gw_sp_layout(gw_sp_measure(Gw.Display{}, rows)) : Gw.Lay}

# The formatted table
# -------------------
# Gw.table is the model of the formatter's lines (`push_table`). The laws
# below state it against the layout above and the measured-row helpers,
# without rendering a table a second time.

# LAW table_line_per_row: the formatted table has one line per row, by either measure
# EXCLUDES: an empty or truncated table (`table.go = Nil`), a row rendered
#   twice or dropped
law table_line_per_row:
  for +m: Gw.Measure
  for +rows: List<&2, List<&2, List<&2, Nat>>>
  {List.length(&2, List<&2, Nat>, Gw.table(m, rows)) == List.length(&2, List<&2, List<&2, Nat>>, rows) : Nat}

# a line of a table whose layout has the column widths ws, for a measured
# row: the width of every column but the last, then the row's own cell of
# the last column (0 wide when the row has none)
def gw_row_line(+ws: List<&2, Nat>, row: List<&2, Nat>) -> List<&2, Nat>:
  List.append(&2, Nat, List.take(&2, Nat, ws, Nat.sub(List.length(&2, Nat, ws), 1n)), [gw_sp_cell(row, Nat.sub(List.length(&2, Nat, ws), 1n))])

# LAW table_row_aligned: every line of the formatted table is the layout's column widths,
# all but the last, then the row's own cell of the last column, by its
# display width: for every table (pre, row, post), the line at row's place
# EXCLUDES: a line of another row, a padded last column, a cell padded to
#   another width than its column's in the layout, a line cut short or
#   long, a last cell measured by anything but the sum of its glyph widths
law table_row_aligned:
  for +pre: List<&2, List<&2, List<&2, Nat>>>
  for +row: List<&2, List<&2, Nat>>
  for +post: List<&2, List<&2, List<&2, Nat>>>
  {List.get(&2, List<&2, Nat>, Gw.table(Gw.Display{}, List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post)), List.length(&2, List<&2, List<&2, Nat>>, pre)) == Some{gw_row_line(Gw.Lay.widths(Gw.layout(List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post))), gw_sp_mrow(Gw.Display{}, row))} : Maybe<&2, List<&2, Nat>>}

# a cell with every glyph made 1 wide: as many glyphs
def gw_ones_cell(c: List<&2, Nat>) -> List<&2, Nat>:
  match c:
    case Nil{}:
      Nil{}
    case w <> rest:
      1n <> gw_ones_cell(rest)

def gw_ones_row(row: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match row:
    case Nil{}:
      Nil{}
    case c <> rest:
      gw_ones_cell(c) <> gw_ones_row(rest)

# a table with every glyph made 1 wide
def gw_ones(rows: List<&2, List<&2, List<&2, Nat>>>) -> List<&2, List<&2, List<&2, Nat>>>:
  match rows:
    case Nil{}:
      Nil{}
    case r <> rest:
      gw_ones_row(r) <> gw_ones(rest)

# LAW table_chars_counts_glyphs: the old formatter measured a cell by its count of glyphs: its
# table of any table is the display-width table of that table with every
# glyph made 1 wide
# EXCLUDES: the old formatter measuring by display width
#   (`cell.m(Chars, c) = cell.sum(c)`) or by anything but the count of
#   glyphs
law table_chars_counts_glyphs:
  for +rows: List<&2, List<&2, List<&2, Nat>>>
  {Gw.table(Gw.Chars{}, rows) == Gw.table(Gw.Display{}, gw_ones(rows)) : List<&2, List<&2, Nat>>}
