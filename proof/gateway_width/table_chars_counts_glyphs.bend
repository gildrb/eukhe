# eukhe: the proof of LAW table_chars_counts_glyphs
# A cell's count of glyphs is the display width of its glyphs made 1 wide
# (tcg.cell); so each cell, column width, count of columns, line and the
# table agree (one lemma per def of the model).

import Base
import ../../bend/gateway_width.bend as Gw
import ../../laws/gateway_width.bend as GatewayWidth

def tcg.cell(c: List<&2, Nat>) -> {List.length(&2, Nat, c) == Gw.cell.sum(GatewayWidth.gw_ones_cell(c)) : Nat}:
  match c:
    case Nil{}:
      {==}
    case w <> +rest:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Nat, rest), Gw.cell.sum(GatewayWidth.gw_ones_cell(rest)), tcg.cell(rest))

def tcg.get(row: List<&2, List<&2, Nat>>, i: Nat) -> {Gw.get.w(row, Gw.Chars{}, i) == Gw.get.w(GatewayWidth.gw_ones_row(row), Gw.Display{}, i) : Nat}:
  match row:
    case Nil{}:
      {==}
    case c <> rest:
      match i:
        case 0n:
          tcg.cell(c)
        case 1n+p:
          tcg.get(rest, p)

def tcg.col(rows: List<&2, List<&2, List<&2, Nat>>>, +i: Nat) -> {Gw.col.w(rows, Gw.Chars{}, i) == Gw.col.w(GatewayWidth.gw_ones(rows), Gw.Display{}, i) : Nat}:
  match rows:
    case Nil{}:
      {==}
    case +r <> +rest:
      %tcg.get(r, i) : {Nat.max(Gw.get.w(r, Gw.Chars{}, i), Gw.col.w(rest, Gw.Chars{}, i)) == Nat.max(_, Gw.col.w(GatewayWidth.gw_ones(rest), Gw.Display{}, i)) : Nat}
      %tcg.col(rest, i) : {Nat.max(Gw.get.w(r, Gw.Chars{}, i), Gw.col.w(rest, Gw.Chars{}, i)) == Nat.max(Gw.get.w(r, Gw.Chars{}, i), _) : Nat}
      {==}

def tcg.len(row: List<&2, List<&2, Nat>>) -> {List.length(&2, List<&2, Nat>, row) == List.length(&2, List<&2, Nat>, GatewayWidth.gw_ones_row(row)) : Nat}:
  match row:
    case Nil{}:
      {==}
    case c <> +rest:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, List<&2, Nat>, rest), List.length(&2, List<&2, Nat>, GatewayWidth.gw_ones_row(rest)), tcg.len(rest))

def tcg.cols(rows: List<&2, List<&2, List<&2, Nat>>>) -> {Gw.cols(rows) == Gw.cols(GatewayWidth.gw_ones(rows)) : Nat}:
  match rows:
    case Nil{}:
      {==}
    case +r <> +rest:
      %tcg.len(r) : {Nat.max(List.length(&2, List<&2, Nat>, r), Gw.cols(rest)) == Nat.max(_, Gw.cols(GatewayWidth.gw_ones(rest))) : Nat}
      %tcg.cols(rest) : {Nat.max(List.length(&2, List<&2, Nat>, r), Gw.cols(rest)) == Nat.max(List.length(&2, List<&2, Nat>, r), _) : Nat}
      {==}

def tcg.line(k: Nat, +rows: List<&2, List<&2, List<&2, Nat>>>, +row: List<&2, List<&2, Nat>>, +i: Nat) -> {Gw.line(k, Gw.Chars{}, rows, row, i) == Gw.line(k, Gw.Display{}, GatewayWidth.gw_ones(rows), GatewayWidth.gw_ones_row(row), i) : List<&2, Nat>}:
  match k:
    case 0n:
      %tcg.get(row, i) : {[Gw.get.w(row, Gw.Chars{}, i)] == [_] : List<&2, Nat>}
      {==}
    case 1n+p:
      %tcg.get(row, i) : {Gw.line(1n+p, Gw.Chars{}, rows, row, i) == Gw.pad(_, Gw.col.w(GatewayWidth.gw_ones(rows), Gw.Display{}, i)) <> Gw.line(p, Gw.Display{}, GatewayWidth.gw_ones(rows), GatewayWidth.gw_ones_row(row), 1n+i) : List<&2, Nat>}
      %tcg.col(rows, i) : {Gw.line(1n+p, Gw.Chars{}, rows, row, i) == Gw.pad(Gw.get.w(row, Gw.Chars{}, i), _) <> Gw.line(p, Gw.Display{}, GatewayWidth.gw_ones(rows), GatewayWidth.gw_ones_row(row), 1n+i) : List<&2, Nat>}
      %tcg.line(p, rows, row, 1n+i) : {Gw.line(1n+p, Gw.Chars{}, rows, row, i) == Gw.pad(Gw.get.w(row, Gw.Chars{}, i), Gw.col.w(rows, Gw.Chars{}, i)) <> _ : List<&2, Nat>}
      {==}

def tcg.go(rs: List<&2, List<&2, List<&2, Nat>>>, +k: Nat, +rows: List<&2, List<&2, List<&2, Nat>>>) -> {Gw.table.go(rs, k, Gw.Chars{}, rows) == Gw.table.go(GatewayWidth.gw_ones(rs), k, Gw.Display{}, GatewayWidth.gw_ones(rows)) : List<&2, List<&2, Nat>>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +rest:
      %tcg.line(k, rows, r, 0n) : {Gw.line(k, Gw.Chars{}, rows, r, 0n) <> Gw.table.go(rest, k, Gw.Chars{}, rows) == _ <> Gw.table.go(GatewayWidth.gw_ones(rest), k, Gw.Display{}, GatewayWidth.gw_ones(rows)) : List<&2, List<&2, Nat>>}
      %tcg.go(rest, k, rows) : {Gw.line(k, Gw.Chars{}, rows, r, 0n) <> Gw.table.go(rest, k, Gw.Chars{}, rows) == Gw.line(k, Gw.Chars{}, rows, r, 0n) <> _ : List<&2, List<&2, Nat>>}
      {==}

def tcg.table(+rows: List<&2, List<&2, List<&2, Nat>>>) -> {Gw.table(Gw.Chars{}, rows) == Gw.table(Gw.Display{}, GatewayWidth.gw_ones(rows)) : List<&2, List<&2, Nat>>}:
  %tcg.cols(rows) : {Gw.table(Gw.Chars{}, rows) == Gw.table.go(GatewayWidth.gw_ones(rows), Nat.sub(_, 1n), Gw.Display{}, GatewayWidth.gw_ones(rows)) : List<&2, List<&2, Nat>>}
  tcg.go(rows, Nat.sub(Gw.cols(rows), 1n), rows)

def GatewayWidth.table_chars_counts_glyphs(rows):
  tcg.table(rows)
