# eukhe: the proof of LAW layout_pad_fills
#
# PROOF: row j's pads are its cells' pads over the widths (gw.pall_row);
# its pad i, below the count of columns but one (lpf.at_lt), is column
# i's width less the cell's display width (lpf.at_val), the layout's
# width i is column i's (gw.wget), at least the cell (gw.colw_ge), so the
# cell and the pad add up to it (gw.add_sub); the cell's display width is
# its width, 0 when missing (lpf.cell_w).

import Base
import ../../bend/gateway_width.bend as Gw
import ../../laws/gateway_width.bend as GatewayWidth
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

# i < k: i < 1 + k
def lpf.lt_succ(i: Nat, k: Nat, h: {Nat.is_lt(i, k) == True{} : Bool}) -> {Nat.is_lt(i, 1n+k) == True{} : Bool}:
  match i k:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LLogicLogic.wn_absurd({Nat.is_lt(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      lpf.lt_succ(p, q, h)

# a measured cell's display width is its width, 0 when missing
def lpf.cell_w(r: List<&2, Nat>, i: Nat) -> {Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, i) == Maybe.default(&2, Nat, List.get(&2, Nat, r, i), 0n) : Nat}:
  match r:
    case Nil{}:
      {==}
    case w <> rest:
      match i:
        case 0n:
          LNat.wn_add_zero_r(w)
        case 1n+p:
          lpf.cell_w(rest, p)

# pad i of a row from column i0, over the widths of k columns after it:
# column i0 + i's width less the row's cell there
def lpf.at_val(k: Nat, +t: List<&2, List<&2, List<&2, Nat>>>, +row: List<&2, List<&2, Nat>>, +i0: Nat, i: Nat, -p: Nat, e: {List.get(&2, Nat, Gw.pads.at(Gw.widths(k, Gw.Display{}, t, 1n+i0), Gw.col.w(t, Gw.Display{}, i0), row, i0), i) == Some{p} : Maybe<&2, Nat>}) -> {Nat.sub(Gw.col.w(t, Gw.Display{}, Nat.add(i, i0)), Gw.get.w(row, Gw.Display{}, Nat.add(i, i0))) == p : Nat}:
  match k i:
    case 0n 0n:
      LA.gw.none_some(Nat, p, {Nat.sub(Gw.col.w(t, Gw.Display{}, i0), Gw.get.w(row, Gw.Display{}, i0)) == p : Nat}, e)
    case 0n 1n+m:
      LA.gw.none_some(Nat, p, {Nat.sub(Gw.col.w(t, Gw.Display{}, Nat.add(1n+m, i0)), Gw.get.w(row, Gw.Display{}, Nat.add(1n+m, i0))) == p : Nat}, e)
    case 1n+q 0n:
      LA.gw.some_inj(Nat, Nat.sub(Gw.col.w(t, Gw.Display{}, i0), Gw.get.w(row, Gw.Display{}, i0)), p, e)
    case 1n+q 1n++m:
      %LNat.wn_add_succ_r(m, i0) : {Nat.sub(Gw.col.w(t, Gw.Display{}, _), Gw.get.w(row, Gw.Display{}, _)) == p : Nat}
      lpf.at_val(q, t, row, 1n+i0, m, p, e)

# a pad at i of a row over k more columns: i is below k
def lpf.at_lt(k: Nat, +t: List<&2, List<&2, List<&2, Nat>>>, +row: List<&2, List<&2, Nat>>, +i0: Nat, i: Nat, -p: Nat, e: {List.get(&2, Nat, Gw.pads.at(Gw.widths(k, Gw.Display{}, t, 1n+i0), Gw.col.w(t, Gw.Display{}, i0), row, i0), i) == Some{p} : Maybe<&2, Nat>}) -> {Nat.is_lt(i, k) == True{} : Bool}:
  match k i:
    case 0n 0n:
      LA.gw.none_some(Nat, p, {Nat.is_lt(0n, 0n) == True{} : Bool}, e)
    case 0n 1n+m:
      LA.gw.none_some(Nat, p, {Nat.is_lt(1n+m, 0n) == True{} : Bool}, e)
    case 1n+q 0n:
      {==}
    case 1n+q 1n+m:
      lpf.at_lt(q, t, row, 1n+i0, m, p, e)

# the law's claim for the widths ws, row r, column i and pad p
def lpf.Fill(+ws: List<&2, Nat>, +r: List<&2, Nat>, +i: Nat, +p: Nat) -> Type:
  &w: Nat -> {(List.get(&2, Nat, ws, i), Nat.add(Maybe.default(&2, Nat, List.get(&2, Nat, r, i), 0n), p)) == (Some{w}, w) : Maybe<&2, Nat> & Nat}

# width i is column i's; the cell and its pad add up to it
def lpf.pair(-ws: List<&2, Nat>, +rows: List<&2, List<&2, Nat>>, +r: List<&2, Nat>, +i: Nat, -p: Nat, ew: {List.get(&2, Nat, ws, i) == Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, Nat.add(i, 0n))} : Maybe<&2, Nat>}, hv: {Nat.sub(Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, Nat.add(i, 0n)), Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, Nat.add(i, 0n))) == p : Nat}, hle: {Nat.is_le(Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, i), Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)) == True{} : Bool}) -> {(List.get(&2, Nat, ws, i), Nat.add(Maybe.default(&2, Nat, List.get(&2, Nat, r, i), 0n), p)) == (Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)}, Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)) : Maybe<&2, Nat> & Nat}:
  %lpf.cell_w(r, i) : {(List.get(&2, Nat, ws, i), Nat.add(_, p)) == (Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)}, Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)) : Maybe<&2, Nat> & Nat}
  %hv : {(List.get(&2, Nat, ws, i), Nat.add(Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, i), _)) == (Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)}, Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)) : Maybe<&2, Nat> & Nat}
  %Equal.sym(Maybe<&2, Nat>, List.get(&2, Nat, ws, i), Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, Nat.add(i, 0n))}, ew) : {(_, Nat.add(Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, i), Nat.sub(Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, Nat.add(i, 0n)), Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, Nat.add(i, 0n))))) == (Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)}, Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)) : Maybe<&2, Nat> & Nat}
  %Equal.sym(Nat, Nat.add(i, 0n), i, LNat.wn_add_zero_r(i)) : {(Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, _)}, Nat.add(Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, i), Nat.sub(Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, _), Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, _)))) == (Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)}, Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)) : Maybe<&2, Nat> & Nat}
  %Equal.sym(Nat, Nat.add(Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, i), Nat.sub(Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i), Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, i))), Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i), LA.gw.add_sub(Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, i), Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i), hle)) : {(Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)}, _) == (Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)}, Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)) : Maybe<&2, Nat> & Nat}
  {==}

# over a layout of K columns
def lpf.go(K: Nat, +rows: List<&2, List<&2, Nat>>, +r: List<&2, Nat>, +i: Nat, +p: Nat, e: {List.get(&2, Nat, Gw.pads.row(Gw.widths(K, Gw.Display{}, GatewayWidth.gw_table(rows), 0n), GatewayWidth.gw_cells(r)), i) == Some{p} : Maybe<&2, Nat>}, hle: {Nat.is_le(Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, i), Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)) == True{} : Bool}) -> lpf.Fill(Gw.widths(K, Gw.Display{}, GatewayWidth.gw_table(rows), 0n), r, i, p):
  match K:
    case 0n:
      LA.gw.none_some(Nat, p, lpf.Fill(Nil{}, r, i, p), e)
    case 1n++k:
      +e2 = e
      +hl = lpf.lt_succ(i, k, lpf.at_lt(k, GatewayWidth.gw_table(rows), GatewayWidth.gw_cells(r), 0n, i, p, e2))
      (Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i), lpf.pair(Gw.widths(1n+k, Gw.Display{}, GatewayWidth.gw_table(rows), 0n), rows, r, i, p, LA.gw.wget(1n+k, GatewayWidth.gw_table(rows), 0n, i, hl), lpf.at_val(k, GatewayWidth.gw_table(rows), GatewayWidth.gw_cells(r), 0n, i, p, e2), hle))

# the layout's row j of pads is ps: its pad i is row j's cells' pad i
def lpf.pad_in(+rows: List<&2, List<&2, Nat>>, j: Nat, +r: List<&2, Nat>, -ps: List<&2, Nat>, -i: Nat, -p: Nat, row: {List.get(&2, List<&2, Nat>, rows, j) == Some{r} : Maybe<&2, List<&2, Nat>>}, pads: {List.get(&2, List<&2, Nat>, Gw.pads.all(GatewayWidth.gw_table(rows), Gw.widths(Gw.cols(GatewayWidth.gw_table(rows)), Gw.Display{}, GatewayWidth.gw_table(rows), 0n)), j) == Some{ps} : Maybe<&2, List<&2, Nat>>}, pad: {List.get(&2, Nat, ps, i) == Some{p} : Maybe<&2, Nat>}) -> {List.get(&2, Nat, Gw.pads.row(Gw.widths(Gw.cols(GatewayWidth.gw_table(rows)), Gw.Display{}, GatewayWidth.gw_table(rows), 0n), GatewayWidth.gw_cells(r)), i) == Some{p} : Maybe<&2, Nat>}:
  +ws = Gw.widths(Gw.cols(GatewayWidth.gw_table(rows)), Gw.Display{}, GatewayWidth.gw_table(rows), 0n)
  %Equal.sym(List<&2, Nat>, Gw.pads.row(ws, GatewayWidth.gw_cells(r)), ps, LA.gw.some_inj(List<&2, Nat>, Gw.pads.row(ws, GatewayWidth.gw_cells(r)), ps, Equal.trans(Maybe<&2, List<&2, Nat>>, Some{Gw.pads.row(ws, GatewayWidth.gw_cells(r))}, List.get(&2, List<&2, Nat>, Gw.pads.all(GatewayWidth.gw_table(rows), ws), j), Some{ps}, Equal.sym(Maybe<&2, List<&2, Nat>>, List.get(&2, List<&2, Nat>, Gw.pads.all(GatewayWidth.gw_table(rows), ws), j), Some{Gw.pads.row(ws, GatewayWidth.gw_cells(r))}, LA.gw.pall_row(rows, ws, j, r, row)), pads))) : {List.get(&2, Nat, _, i) == Some{p} : Maybe<&2, Nat>}
  pad

def GatewayWidth.layout_pad_fills(rows, j, r, ps, i, p, row, pads, pad):
  +row2 = row
  lpf.go(Gw.cols(GatewayWidth.gw_table(rows)), rows, r, i, p, lpf.pad_in(rows, j, r, ps, i, p, row2, pads, pad), LA.gw.colw_ge(rows, j, r, i, row2))
