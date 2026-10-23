# eukhe: the proof of LAW ascii_unchanged

import Base
import ../../bend/gateway_width.bend as Gw
import ../../LAWS.bend as Laws

# ASCII
# -----

def gw.cell_ascii(c: List<&2, Nat>, ones: Gw.Ones.cell(c)) -> {Gw.cell.sum(c) == List.length(&2, Nat, c) : Nat}:
  match c:
    case Nil{}:
      {==}
    case w <> rest:
      (one, more) = ones
      %Equal.sym(Nat, w, 1n, one) : {Nat.add(_, Gw.cell.sum(rest)) == 1n+List.length(&2, Nat, rest) : Nat}
      %gw.cell_ascii(rest, more) : {1n+Gw.cell.sum(rest) == 1n+_ : Nat}
      {==}

def gw.get_ascii(row: List<&2, List<&2, Nat>>, i: Nat, ones: Gw.Ones.row(row)) -> {Gw.get.w(row, Gw.Display{}, i) == Gw.get.w(row, Gw.Chars{}, i) : Nat}:
  match row:
    case Nil{}:
      {==}
    case c <> rest:
      match i:
        case 0n:
          (oc, orest) = ones
          gw.cell_ascii(c, oc)
        case 1n+p:
          (oc, orest) = ones
          gw.get_ascii(rest, p, orest)

def gw.col_ascii(rows: List<&2, List<&2, List<&2, Nat>>>, +i: Nat, ones: Gw.Ones.rows(rows)) -> {Gw.col.w(rows, Gw.Display{}, i) == Gw.col.w(rows, Gw.Chars{}, i) : Nat}:
  match rows:
    case Nil{}:
      {==}
    case r <> rest:
      (or, orest) = ones
      %gw.get_ascii(r, i, or) : {Nat.max(Gw.get.w(r, Gw.Display{}, i), Gw.col.w(rest, Gw.Display{}, i)) == Nat.max(_, Gw.col.w(rest, Gw.Chars{}, i)) : Nat}
      %gw.col_ascii(rest, i, orest) : {Nat.max(Gw.get.w(r, Gw.Display{}, i), Gw.col.w(rest, Gw.Display{}, i)) == Nat.max(Gw.get.w(r, Gw.Display{}, i), _) : Nat}
      {==}

def gw.line_ascii(+k: Nat, +rows: List<&2, List<&2, List<&2, Nat>>>, +row: List<&2, List<&2, Nat>>, +i: Nat, +orows: Gw.Ones.rows(rows), +orow: Gw.Ones.row(row)) -> {Gw.line(k, Gw.Display{}, rows, row, i) == Gw.line(k, Gw.Chars{}, rows, row, i) : List<&2, Nat>}:
  match k:
    case 0n:
      %gw.get_ascii(row, i, orow) : {[Gw.get.w(row, Gw.Display{}, i)] == [_] : List<&2, Nat>}
      {==}
    case 1n+p:
      %gw.get_ascii(row, i, orow) : {Gw.line(1n+p, Gw.Display{}, rows, row, i) == Gw.pad(_, Gw.col.w(rows, Gw.Chars{}, i)) <> Gw.line(p, Gw.Chars{}, rows, row, 1n+i) : List<&2, Nat>}
      %gw.col_ascii(rows, i, orows) : {Gw.line(1n+p, Gw.Display{}, rows, row, i) == Gw.pad(Gw.get.w(row, Gw.Display{}, i), _) <> Gw.line(p, Gw.Chars{}, rows, row, 1n+i) : List<&2, Nat>}
      %gw.line_ascii(p, rows, row, 1n+i, orows, orow) : {Gw.line(1n+p, Gw.Display{}, rows, row, i) == Gw.pad(Gw.get.w(row, Gw.Display{}, i), Gw.col.w(rows, Gw.Display{}, i)) <> _ : List<&2, Nat>}
      {==}

def gw.table_ascii(rs: List<&2, List<&2, List<&2, Nat>>>, +k: Nat, +rows: List<&2, List<&2, List<&2, Nat>>>, ors: Gw.Ones.rows(rs), +orows: Gw.Ones.rows(rows)) -> {Gw.table.go(rs, k, Gw.Display{}, rows) == Gw.table.go(rs, k, Gw.Chars{}, rows) : List<&2, List<&2, Nat>>}:
  match rs:
    case Nil{}:
      {==}
    case r <> rest:
      (or, orest) = ors
      %gw.line_ascii(k, rows, r, 0n, orows, or) : {Gw.line(k, Gw.Display{}, rows, r, 0n) <> Gw.table.go(rest, k, Gw.Display{}, rows) == _ <> Gw.table.go(rest, k, Gw.Chars{}, rows) : List<&2, List<&2, Nat>>}
      %gw.table_ascii(rest, k, rows, orest, orows) : {Gw.line(k, Gw.Display{}, rows, r, 0n) <> Gw.table.go(rest, k, Gw.Display{}, rows) == Gw.line(k, Gw.Display{}, rows, r, 0n) <> _ : List<&2, List<&2, Nat>>}
      {==}

def ascii_unchanged(+rows: List<&2, List<&2, List<&2, Nat>>>, +ones: Gw.Ones.rows(rows)) -> {Gw.table(Gw.Display{}, rows) == Gw.table(Gw.Chars{}, rows) : List<&2, List<&2, Nat>>}:
  gw.table_ascii(rows, Nat.sub(Gw.cols(rows), 1n), rows, ones, ones)

def Laws.ascii_unchanged(rows, ones):
  ascii_unchanged(rows, ones)
