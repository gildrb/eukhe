# eukhe: the proof of LAW table_row_aligned
# The table's line at row's place is row's line (tra.at), which is the
# widths of every column but the last, then row's last cell
# (table_aligned); those widths are the layout's widths less the last
# (tra.cut, tra.len), and the cell's display width is the measured row's
# cell (LA.gw.sp_get).

import Base
import ../../bend/gateway_width.bend as Gw
import ../../laws/gateway_width.bend as GatewayWidth
import ./base.bend as LA
import ./table_aligned.bend as PTableAligned

# the line at row's place is row's line
def tra.at(pre: List<&2, List<&2, List<&2, Nat>>>, +row: List<&2, List<&2, Nat>>, +post: List<&2, List<&2, List<&2, Nat>>>, +k: Nat, +m: Gw.Measure, +rows: List<&2, List<&2, List<&2, Nat>>>) -> {List.get(&2, List<&2, Nat>, Gw.table.go(List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post), k, m, rows), List.length(&2, List<&2, List<&2, Nat>>, pre)) == Some{Gw.line(k, m, rows, row, 0n)} : Maybe<&2, List<&2, Nat>>}:
  match pre:
    case Nil{}:
      {==}
    case r <> +rest:
      tra.at(rest, row, post, k, m, rows)

# as many widths as columns asked
def tra.len(k: Nat, +m: Gw.Measure, +rows: List<&2, List<&2, List<&2, Nat>>>, +i: Nat) -> {List.length(&2, Nat, Gw.widths(k, m, rows, i)) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n++p:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Nat, Gw.widths(p, m, rows, 1n+i)), p, tra.len(p, m, rows, 1n+i))

# the first p of 1 + p widths are the p widths
def tra.take(p: Nat, +m: Gw.Measure, +rows: List<&2, List<&2, List<&2, Nat>>>, +i: Nat) -> {List.take(&2, Nat, Gw.widths(1n+p, m, rows, i), p) == Gw.widths(p, m, rows, i) : List<&2, Nat>}:
  match p:
    case 0n:
      {==}
    case 1n++q:
      %tra.take(q, m, rows, 1n+i) : {Gw.col.w(rows, m, i) <> List.take(&2, Nat, Gw.widths(1n+q, m, rows, 1n+i), q) == Gw.col.w(rows, m, i) <> _ : List<&2, Nat>}
      {==}

# the widths of K columns less the last are the widths of K - 1 columns
def tra.cut(K: Nat, +m: Gw.Measure, +rows: List<&2, List<&2, List<&2, Nat>>>, +i: Nat) -> {List.take(&2, Nat, Gw.widths(K, m, rows, i), Nat.sub(K, 1n)) == Gw.widths(Nat.sub(K, 1n), m, rows, i) : List<&2, Nat>}:
  match K:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, LA.gw.sub_zero(p)) : {List.take(&2, Nat, Gw.widths(1n+p, m, rows, i), _) == Gw.widths(_, m, rows, i) : List<&2, Nat>}
      tra.take(p, m, rows, i)

def tra.go(+pre: List<&2, List<&2, List<&2, Nat>>>, +row: List<&2, List<&2, Nat>>, +post: List<&2, List<&2, List<&2, Nat>>>) -> {List.get(&2, List<&2, Nat>, Gw.table(Gw.Display{}, List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post)), List.length(&2, List<&2, List<&2, Nat>>, pre)) == Some{GatewayWidth.gw_row_line(Gw.Lay.widths(Gw.layout(List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post))), GatewayWidth.gw_sp_mrow(Gw.Display{}, row))} : Maybe<&2, List<&2, Nat>>}:
  +T = List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post)
  +K = Gw.cols(T)
  +k = Nat.sub(K, 1n)
  +ws = Gw.widths(K, Gw.Display{}, T, 0n)
  %Equal.sym(Nat, List.length(&2, Nat, ws), K, tra.len(K, Gw.Display{}, T, 0n)) : {List.get(&2, List<&2, Nat>, Gw.table(Gw.Display{}, T), List.length(&2, List<&2, List<&2, Nat>>, pre)) == Some{List.append(&2, Nat, List.take(&2, Nat, ws, Nat.sub(_, 1n)), [GatewayWidth.gw_sp_cell(GatewayWidth.gw_sp_mrow(Gw.Display{}, row), Nat.sub(_, 1n))])} : Maybe<&2, List<&2, Nat>>}
  %Equal.sym(List<&2, Nat>, List.take(&2, Nat, ws, k), Gw.widths(k, Gw.Display{}, T, 0n), tra.cut(K, Gw.Display{}, T, 0n)) : {List.get(&2, List<&2, Nat>, Gw.table(Gw.Display{}, T), List.length(&2, List<&2, List<&2, Nat>>, pre)) == Some{List.append(&2, Nat, _, [GatewayWidth.gw_sp_cell(GatewayWidth.gw_sp_mrow(Gw.Display{}, row), k)])} : Maybe<&2, List<&2, Nat>>}
  %LA.gw.sp_get(row, Gw.Display{}, k) : {List.get(&2, List<&2, Nat>, Gw.table(Gw.Display{}, T), List.length(&2, List<&2, List<&2, Nat>>, pre)) == Some{List.append(&2, Nat, Gw.widths(k, Gw.Display{}, T, 0n), [_])} : Maybe<&2, List<&2, Nat>>}
  %PTableAligned.table_aligned(pre, row, post) : {List.get(&2, List<&2, Nat>, Gw.table(Gw.Display{}, T), List.length(&2, List<&2, List<&2, Nat>>, pre)) == Some{_} : Maybe<&2, List<&2, Nat>>}
  tra.at(pre, row, post, k, Gw.Display{}, T)

def GatewayWidth.table_row_aligned(pre, row, post):
  tra.go(pre, row, post)
