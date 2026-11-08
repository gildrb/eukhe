# eukhe: lemmas the proofs of area gateway_width share

import Base
import ../../bend/gateway_width.bend as Gw
import ../../laws/gateway_width.bend as GatewayWidth

def gw.sub_zero(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# The table from the glyphs
# -------------------------
# The model's measure of a cell, its column widths, its count of columns
# and its rendered rows are the spec's on the table measured.

def gw.sp_sum(c: List<&2, Nat>) -> {Gw.cell.sum(c) == GatewayWidth.gw_sp_sum(c) : Nat}:
  match c:
    case Nil{}:
      {==}
    case +w <> +rest:
      %gw.sp_sum(rest) : {Nat.add(w, Gw.cell.sum(rest)) == Nat.add(w, _) : Nat}
      {==}

def gw.sp_glyphs(m: Gw.Measure, +c: List<&2, Nat>) -> {Gw.cell.m(m, c) == GatewayWidth.gw_sp_glyphs(m, c) : Nat}:
  match m:
    case Gw.Display{}:
      gw.sp_sum(c)
    case Gw.Chars{}:
      {==}

def gw.sp_get(row: List<&2, List<&2, Nat>>, +m: Gw.Measure, i: Nat) -> {Gw.get.w(row, m, i) == GatewayWidth.gw_sp_cell(GatewayWidth.gw_sp_mrow(m, row), i) : Nat}:
  match row:
    case Nil{}:
      {==}
    case +c <> +rest:
      match i:
        case 0n:
          gw.sp_glyphs(m, c)
        case 1n+p:
          gw.sp_get(rest, m, p)

def gw.sp_colw(rows: List<&2, List<&2, List<&2, Nat>>>, +m: Gw.Measure, +i: Nat) -> {Gw.col.w(rows, m, i) == GatewayWidth.gw_sp_colw(GatewayWidth.gw_sp_measure(m, rows), i) : Nat}:
  match rows:
    case Nil{}:
      {==}
    case +r <> +rest:
      %gw.sp_get(r, m, i) : {Nat.max(Gw.get.w(r, m, i), Gw.col.w(rest, m, i)) == Nat.max(_, GatewayWidth.gw_sp_colw(GatewayWidth.gw_sp_measure(m, rest), i)) : Nat}
      %gw.sp_colw(rest, m, i) : {Nat.max(Gw.get.w(r, m, i), Gw.col.w(rest, m, i)) == Nat.max(Gw.get.w(r, m, i), _) : Nat}
      {==}

def gw.sp_len(row: List<&2, List<&2, Nat>>, +m: Gw.Measure) -> {List.length(&2, List<&2, Nat>, row) == List.length(&2, Nat, GatewayWidth.gw_sp_mrow(m, row)) : Nat}:
  match row:
    case Nil{}:
      {==}
    case c <> +rest:
      %gw.sp_len(rest, m) : {1n+List.length(&2, List<&2, Nat>, rest) == 1n+_ : Nat}
      {==}

def gw.sp_cols(rows: List<&2, List<&2, List<&2, Nat>>>, +m: Gw.Measure) -> {Gw.cols(rows) == GatewayWidth.gw_sp_cols(GatewayWidth.gw_sp_measure(m, rows)) : Nat}:
  match rows:
    case Nil{}:
      {==}
    case +r <> +rest:
      %gw.sp_len(r, m) : {Nat.max(List.length(&2, List<&2, Nat>, r), Gw.cols(rest)) == Nat.max(_, GatewayWidth.gw_sp_cols(GatewayWidth.gw_sp_measure(m, rest))) : Nat}
      %gw.sp_cols(rest, m) : {Nat.max(List.length(&2, List<&2, Nat>, r), Gw.cols(rest)) == Nat.max(List.length(&2, List<&2, Nat>, r), _) : Nat}
      {==}

def gw.sp_widths(k: Nat, +m: Gw.Measure, +rows: List<&2, List<&2, List<&2, Nat>>>, +i: Nat) -> {Gw.widths(k, m, rows, i) == GatewayWidth.gw_sp_widths(k, GatewayWidth.gw_sp_measure(m, rows), i) : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %gw.sp_colw(rows, m, i) : {Gw.widths(1n+p, m, rows, i) == _ <> GatewayWidth.gw_sp_widths(p, GatewayWidth.gw_sp_measure(m, rows), 1n+i) : List<&2, Nat>}
      %gw.sp_widths(p, m, rows, 1n+i) : {Gw.widths(1n+p, m, rows, i) == Gw.col.w(rows, m, i) <> _ : List<&2, Nat>}
      {==}

def gw.sp_line(k: Nat, +m: Gw.Measure, +rows: List<&2, List<&2, List<&2, Nat>>>, +row: List<&2, List<&2, Nat>>, +i: Nat) -> {Gw.line(k, m, rows, row, i) == GatewayWidth.gw_sp_line(k, GatewayWidth.gw_sp_measure(m, rows), GatewayWidth.gw_sp_mrow(m, row), i) : List<&2, Nat>}:
  match k:
    case 0n:
      %gw.sp_get(row, m, i) : {Gw.line(0n, m, rows, row, i) == [_] : List<&2, Nat>}
      {==}
    case 1n+p:
      %gw.sp_get(row, m, i) : {Gw.line(1n+p, m, rows, row, i) == Nat.add(_, Nat.sub(GatewayWidth.gw_sp_colw(GatewayWidth.gw_sp_measure(m, rows), i), _)) <> GatewayWidth.gw_sp_line(p, GatewayWidth.gw_sp_measure(m, rows), GatewayWidth.gw_sp_mrow(m, row), 1n+i) : List<&2, Nat>}
      %gw.sp_colw(rows, m, i) : {Gw.line(1n+p, m, rows, row, i) == Nat.add(Gw.get.w(row, m, i), Nat.sub(_, Gw.get.w(row, m, i))) <> GatewayWidth.gw_sp_line(p, GatewayWidth.gw_sp_measure(m, rows), GatewayWidth.gw_sp_mrow(m, row), 1n+i) : List<&2, Nat>}
      %gw.sp_line(p, m, rows, row, 1n+i) : {Gw.line(1n+p, m, rows, row, i) == Nat.add(Gw.get.w(row, m, i), Nat.sub(Gw.col.w(rows, m, i), Gw.get.w(row, m, i))) <> _ : List<&2, Nat>}
      {==}

def gw.sp_lines(rs: List<&2, List<&2, List<&2, Nat>>>, +k: Nat, +m: Gw.Measure, +rows: List<&2, List<&2, List<&2, Nat>>>) -> {Gw.table.go(rs, k, m, rows) == GatewayWidth.gw_sp_lines(GatewayWidth.gw_sp_measure(m, rs), k, GatewayWidth.gw_sp_measure(m, rows)) : List<&2, List<&2, Nat>>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +rest:
      %gw.sp_line(k, m, rows, r, 0n) : {Gw.table.go(r <> rest, k, m, rows) == _ <> GatewayWidth.gw_sp_lines(GatewayWidth.gw_sp_measure(m, rest), k, GatewayWidth.gw_sp_measure(m, rows)) : List<&2, List<&2, Nat>>}
      %gw.sp_lines(rest, k, m, rows) : {Gw.table.go(r <> rest, k, m, rows) == Gw.line(k, m, rows, r, 0n) <> _ : List<&2, List<&2, Nat>>}
      {==}

def gw.sp_table(+m: Gw.Measure, +rows: List<&2, List<&2, List<&2, Nat>>>) -> {Gw.table(m, rows) == GatewayWidth.gw_sp_table(GatewayWidth.gw_sp_measure(m, rows)) : List<&2, List<&2, Nat>>}:
  %gw.sp_cols(rows, m) : {Gw.table(m, rows) == GatewayWidth.gw_sp_lines(GatewayWidth.gw_sp_measure(m, rows), Nat.sub(_, 1n), GatewayWidth.gw_sp_measure(m, rows)) : List<&2, List<&2, Nat>>}
  gw.sp_lines(rows, Nat.sub(Gw.cols(rows), 1n), m, rows)
