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
# The spec of the formatter on a table of glyph widths, from the
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

# a measured row rendered from column i: k columns, each the cell then
# the column's width less the cell's in spaces, then the next column's
# cell alone (the last column is not padded)
def gw_sp_line(k: Nat, +rows: List<&2, List<&2, Nat>>, +row: List<&2, Nat>, +i: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      [gw_sp_cell(row, i)]
    case 1n+p:
      Nat.add(gw_sp_cell(row, i), Nat.sub(gw_sp_colw(rows, i), gw_sp_cell(row, i))) <> gw_sp_line(p, rows, row, 1n+i)

# every row of rs rendered with k padded columns of the table rows
def gw_sp_lines(rs: List<&2, List<&2, Nat>>, +k: Nat, +rows: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      gw_sp_line(k, rows, r, 0n) <> gw_sp_lines(rest, k, rows)

# a measured table rendered: every row, every column padded but the last
def gw_sp_table(+rows: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  gw_sp_lines(rows, Nat.sub(gw_sp_cols(rows), 1n), rows)

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

# LAW table_exact: the formatted table of any table of glyph widths is the spec's
# rendering of the table measured by display width: every row, each cell
# but the last column's padded to its column's width
# EXCLUDES: a cell measured by anything but the sum of its glyph widths
#   (`w + length(rest)`), an empty or truncated table (`table.go = Nil`),
#   a padded last column, a pad to another column's width
law table_exact:
  for +rows: List<&2, List<&2, List<&2, Nat>>>
  {Gw.table(Gw.Display{}, rows) == gw_sp_table(gw_sp_measure(Gw.Display{}, rows)) : List<&2, List<&2, Nat>>}

# LAW table_chars_exact: the old formatter's table (a cell measured by its count of
# glyphs) is the spec's rendering of the table measured by glyph count
# EXCLUDES: the old formatter measuring by display width
#   (`cell.m(Chars, c) = cell.sum(c)`), an empty or truncated table, a
#   padded last column
law table_chars_exact:
  for +rows: List<&2, List<&2, List<&2, Nat>>>
  {Gw.table(Gw.Chars{}, rows) == gw_sp_table(gw_sp_measure(Gw.Chars{}, rows)) : List<&2, List<&2, Nat>>}
