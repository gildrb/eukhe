# eukhe: the proof of LAW layout_pads_but_last
#
# PROOF: a row of pads of the layout is the pads of a row over the
# widths (lpb.all_len), one per width after the first (lpb.at_len), so
# one per column but the last (lpb.row_len).

import Base
import ../../bend/gateway_width.bend as Gw
import ../../laws/gateway_width.bend as GatewayWidth
import ./base.bend as LA

# the pads from column i: one per width in rest
def lpb.at_len(rest: List<&2, Nat>, +w: Nat, +row: List<&2, List<&2, Nat>>, +i: Nat) -> {List.length(&2, Nat, Gw.pads.at(rest, w, row, i)) == List.length(&2, Nat, rest) : Nat}:
  match rest:
    case Nil{}:
      {==}
    case v <> more:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Nat, Gw.pads.at(more, v, row, 1n+i)), List.length(&2, Nat, more), lpb.at_len(more, v, row, 1n+i))

# a row's pads: one per width but the first
def lpb.row_len(ws: List<&2, Nat>, +row: List<&2, List<&2, Nat>>) -> {List.length(&2, Nat, Gw.pads.row(ws, row)) == Nat.sub(List.length(&2, Nat, ws), 1n) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case w <> +rest:
      Equal.trans(Nat, List.length(&2, Nat, Gw.pads.at(rest, w, row, 0n)), List.length(&2, Nat, rest), Nat.sub(List.length(&2, Nat, rest), 0n), lpb.at_len(rest, w, row, 0n), Equal.sym(Nat, Nat.sub(List.length(&2, Nat, rest), 0n), List.length(&2, Nat, rest), LA.gw.sub_zero(List.length(&2, Nat, rest))))

# every row of pads is a row's pads over the widths
def lpb.all_len(rs: List<&2, List<&2, List<&2, Nat>>>, +ws: List<&2, Nat>, -ps: List<&2, Nat>, j: Nat, e: {List.get(&2, List<&2, Nat>, Gw.pads.all(rs, ws), j) == Some{ps} : Maybe<&2, List<&2, Nat>>}) -> {List.length(&2, Nat, ps) == Nat.sub(List.length(&2, Nat, ws), 1n) : Nat}:
  match rs:
    case Nil{}:
      LA.gw.none_some(List<&2, Nat>, ps, {List.length(&2, Nat, ps) == Nat.sub(List.length(&2, Nat, ws), 1n) : Nat}, e)
    case r <> rest:
      match j:
        case 0n:
          %LA.gw.some_inj(List<&2, Nat>, Gw.pads.row(ws, r), ps, e) : {List.length(&2, Nat, _) == Nat.sub(List.length(&2, Nat, ws), 1n) : Nat}
          lpb.row_len(ws, r)
        case 1n+p:
          lpb.all_len(rest, ws, ps, p, e)

def GatewayWidth.layout_pads_but_last(rows, j, ps, got):
  lpb.all_len(GatewayWidth.gw_table(rows), Gw.widths(Gw.cols(GatewayWidth.gw_table(rows)), Gw.Display{}, GatewayWidth.gw_table(rows), 0n), ps, j, got)
