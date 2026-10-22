# The Signal table formatter of eukhe-gateway (`push_table` in
# crates/eukhe-gateway/src/style.rs), as a model of widths. A cell is the
# list of its glyph widths (a grapheme cluster: 0 for a combining mark
# alone, 1 for ASCII, 2 for a wide CJK character or an emoji); a row is a
# list of cells, a table a list of rows (the delimiter row is not a row).
#
# A rendered row is the list of its column widths: every column but the
# last is the cell padded with spaces to the column width, the last column
# is the cell alone (the Rust code does not pad it). A missing cell has
# width 0. LAWS.bend section gateway_width states the laws.

import Base

# How the formatter measures a cell: by display width (the sum of the
# glyph widths), or by its count of glyphs (the old formatter).
type Measure is Data:
  Display{}
  Chars{}

def cell.sum(c: List<&2, Nat>) -> Nat:
  match c:
    case Nil{}:
      0n
    case w <> rest:
      Nat.add(w, cell.sum(rest))

def cell.m(m: Measure, c: List<&2, Nat>) -> Nat:
  match m:
    case Display{}:
      cell.sum(c)
    case Chars{}:
      List.length(&2, Nat, c)

# The width of cell i of a row, 0 when the row has no cell i.
def get.w(row: List<&2, List<&2, Nat>>, +m: Measure, i: Nat) -> Nat:
  match row:
    case Nil{}:
      0n
    case c <> rest:
      match i:
        case 0n:
          cell.m(m, c)
        case 1n+p:
          get.w(rest, m, p)

# The width of column i: its widest cell.
def col.w(rows: List<&2, List<&2, List<&2, Nat>>>, +m: Measure, +i: Nat) -> Nat:
  match rows:
    case Nil{}:
      0n
    case r <> rest:
      Nat.max(get.w(r, m, i), col.w(rest, m, i))

# The widths of the k columns from column i.
def widths(k: Nat, +m: Measure, +rows: List<&2, List<&2, List<&2, Nat>>>, +i: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      col.w(rows, m, i) <> widths(p, m, rows, 1n+i)

# A cell of width c padded to the column width w (`w - c` spaces).
def pad(+c: Nat, w: Nat) -> Nat:
  Nat.add(c, Nat.sub(w, c))

# A rendered row from column i: k padded columns, then the last column.
def line(k: Nat, +m: Measure, +rows: List<&2, List<&2, List<&2, Nat>>>, +row: List<&2, List<&2, Nat>>, +i: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      [get.w(row, m, i)]
    case 1n+p:
      pad(get.w(row, m, i), col.w(rows, m, i)) <> line(p, m, rows, row, 1n+i)

# The count of columns: the longest row.
def cols(rows: List<&2, List<&2, List<&2, Nat>>>) -> Nat:
  match rows:
    case Nil{}:
      0n
    case r <> rest:
      Nat.max(List.length(&2, List<&2, Nat>, r), cols(rest))

def table.go(rs: List<&2, List<&2, List<&2, Nat>>>, +k: Nat, +m: Measure, +rows: List<&2, List<&2, List<&2, Nat>>>) -> List<&2, List<&2, Nat>>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      line(k, m, rows, r, 0n) <> table.go(rest, k, m, rows)

# The rendered table: every row, with cols - 1 padded columns.
def table(+m: Measure, +rows: List<&2, List<&2, List<&2, Nat>>>) -> List<&2, List<&2, Nat>>:
  table.go(rows, Nat.sub(cols(rows), 1n), m, rows)

# Every glyph of the cell, row, table is 1 wide (ASCII text).
def Ones.cell(c: List<&2, Nat>) -> Data:
  match c:
    case Nil{}:
      Unit
    case w <> rest:
      Sigma<&2, &2, {w == 1n : Nat}, x => Ones.cell(rest)>

def Ones.row(row: List<&2, List<&2, Nat>>) -> Data:
  match row:
    case Nil{}:
      Unit
    case c <> rest:
      Sigma<&2, &2, Ones.cell(c), x => Ones.row(rest)>

def Ones.rows(rows: List<&2, List<&2, List<&2, Nat>>>) -> Data:
  match rows:
    case Nil{}:
      Unit
    case r <> rest:
      Sigma<&2, &2, Ones.row(r), x => Ones.rows(rest)>
