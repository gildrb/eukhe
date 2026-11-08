# eukhe: the proof of LAW layout_cell_fits
#
# PROOF: a cell at i of row j puts i below the row's length (lcf.cell_lt),
# which is at most the count of columns (lcf.cols); so the layout has
# the width of column i (gw.wget), its widest cell, at least the cell's
# display width (gw.colw_ge), which is its width (gw.cell_some).

import Base
import ../../bend/gateway_width.bend as Gw
import ../../laws/gateway_width.bend as GatewayWidth
import ../base/nat.bend as LNat
import ./base.bend as LA

# a cell at i: i is below the row's length
def lcf.cell_lt(r: List<&2, Nat>, i: Nat, -c: Nat, e: {List.get(&2, Nat, r, i) == Some{c} : Maybe<&2, Nat>}) -> {Nat.is_lt(i, List.length(&2, Nat, r)) == True{} : Bool}:
  match r:
    case Nil{}:
      LA.gw.none_some(Nat, c, {Nat.is_lt(i, 0n) == True{} : Bool}, e)
    case w <> rest:
      match i:
        case 0n:
          {==}
        case 1n+p:
          lcf.cell_lt(rest, p, c, e)

# row j has at most as many cells as the table has columns
def lcf.cols(rows: List<&2, List<&2, Nat>>, j: Nat, +r: List<&2, Nat>, e: {List.get(&2, List<&2, Nat>, rows, j) == Some{r} : Maybe<&2, List<&2, Nat>>}) -> {Nat.is_le(List.length(&2, Nat, r), Gw.cols(GatewayWidth.gw_table(rows))) == True{} : Bool}:
  match rows:
    case Nil{}:
      LA.gw.none_some(List<&2, Nat>, r, {Nat.is_le(List.length(&2, Nat, r), 0n) == True{} : Bool}, e)
    case +r0 <> +rest:
      match j:
        case 0n:
          %LA.gw.some_inj(List<&2, Nat>, r0, r, e) : {Nat.is_le(List.length(&2, Nat, _), Nat.max(List.length(&2, List<&2, Nat>, GatewayWidth.gw_cells(r0)), Gw.cols(GatewayWidth.gw_table(rest)))) == True{} : Bool}
          %LA.gw.len_cells(r0) : {Nat.is_le(_, Nat.max(List.length(&2, List<&2, Nat>, GatewayWidth.gw_cells(r0)), Gw.cols(GatewayWidth.gw_table(rest)))) == True{} : Bool}
          LA.gw.le_max_l(List.length(&2, List<&2, Nat>, GatewayWidth.gw_cells(r0)), Gw.cols(GatewayWidth.gw_table(rest)))
        case 1n+p:
          LNat.wn_le_trans(List.length(&2, Nat, r), Gw.cols(GatewayWidth.gw_table(rest)), Nat.max(List.length(&2, List<&2, Nat>, GatewayWidth.gw_cells(r0)), Gw.cols(GatewayWidth.gw_table(rest))), lcf.cols(rest, p, r, e), LA.gw.le_max_r(List.length(&2, List<&2, Nat>, GatewayWidth.gw_cells(r0)), Gw.cols(GatewayWidth.gw_table(rest))))

# the layout's width i is column i's, and the cell fits it
def lcf.pair(+rows: List<&2, List<&2, Nat>>, +r: List<&2, Nat>, +i: Nat, -c: Nat, ew: {List.get(&2, Nat, Gw.widths(Gw.cols(GatewayWidth.gw_table(rows)), Gw.Display{}, GatewayWidth.gw_table(rows), 0n), i) == Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, Nat.add(i, 0n))} : Maybe<&2, Nat>}, ec: {Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, i) == c : Nat}, hle: {Nat.is_le(Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, i), Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)) == True{} : Bool}) -> {(List.get(&2, Nat, Gw.widths(Gw.cols(GatewayWidth.gw_table(rows)), Gw.Display{}, GatewayWidth.gw_table(rows), 0n), i), Nat.is_le(c, Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i))) == (Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)}, True{}) : Maybe<&2, Nat> & Bool}:
  %Equal.sym(Maybe<&2, Nat>, List.get(&2, Nat, Gw.widths(Gw.cols(GatewayWidth.gw_table(rows)), Gw.Display{}, GatewayWidth.gw_table(rows), 0n), i), Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, Nat.add(i, 0n))}, ew) : {(_, Nat.is_le(c, Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i))) == (Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)}, True{}) : Maybe<&2, Nat> & Bool}
  %ec : {(Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, Nat.add(i, 0n))}, Nat.is_le(_, Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i))) == (Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)}, True{}) : Maybe<&2, Nat> & Bool}
  %Equal.sym(Bool, Nat.is_le(Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, i), Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)), True{}, hle) : {(Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, Nat.add(i, 0n))}, _) == (Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)}, True{}) : Maybe<&2, Nat> & Bool}
  %LNat.wn_add_zero_r(i) : {(Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, Nat.add(i, 0n))}, True{}) == (Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, _)}, True{}) : Maybe<&2, Nat> & Bool}
  {==}

def GatewayWidth.layout_cell_fits(rows, j, r, i, c, row, cell):
  +row2 = row
  +cell2 = cell
  +hlt = LA.gw.lt_le(i, List.length(&2, Nat, r), Gw.cols(GatewayWidth.gw_table(rows)), lcf.cell_lt(r, i, c, cell2), lcf.cols(rows, j, r, row2))
  (Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i), lcf.pair(rows, r, i, c, LA.gw.wget(Gw.cols(GatewayWidth.gw_table(rows)), GatewayWidth.gw_table(rows), 0n, i, hlt), LA.gw.cell_some(r, i, c, cell2), LA.gw.colw_ge(rows, j, r, i, row2)))
