# eukhe: the proof of LAW layout_pads

import Base
import ../../bend/gateway_width.bend as Gw
import ../../laws/gateway_width.bend as GatewayWidth
import ./base.bend as LA

# The layout
# ----------
# The layout's widths are the model's widths of every column; its pads
# read them column by column (`gw.pads_at`), so each pad is the column's
# width less the cell's.

# the pads from column i, given the width of column i and the K after it
def gw.pads_at(K: Nat, +rows: List<&2, List<&2, List<&2, Nat>>>, +row: List<&2, List<&2, Nat>>, +i: Nat) -> {Gw.pads.at(Gw.widths(K, Gw.Display{}, rows, 1n+i), Gw.col.w(rows, Gw.Display{}, i), row, i) == GatewayWidth.gw_pads(K, rows, row, i) : List<&2, Nat>}:
  match K:
    case 0n:
      {==}
    case 1n+p:
      %gw.pads_at(p, rows, row, 1n+i) : {Gw.pads.at(Gw.widths(1n+p, Gw.Display{}, rows, 1n+i), Gw.col.w(rows, Gw.Display{}, i), row, i) == Nat.sub(Gw.col.w(rows, Gw.Display{}, i), Gw.get.w(row, Gw.Display{}, i)) <> _ : List<&2, Nat>}
      {==}

def gw.pads_row(K: Nat, +rows: List<&2, List<&2, List<&2, Nat>>>, +row: List<&2, List<&2, Nat>>) -> {Gw.pads.row(Gw.widths(K, Gw.Display{}, rows, 0n), row) == GatewayWidth.gw_pads(Nat.sub(K, 1n), rows, row, 0n) : List<&2, Nat>}:
  match K:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, LA.gw.sub_zero(p)) : {Gw.pads.row(Gw.widths(1n+p, Gw.Display{}, rows, 0n), row) == GatewayWidth.gw_pads(_, rows, row, 0n) : List<&2, Nat>}
      gw.pads_at(p, rows, row, 0n)

def gw.pads_all(rs: List<&2, List<&2, List<&2, Nat>>>, +K: Nat, +rows: List<&2, List<&2, List<&2, Nat>>>) -> {Gw.pads.all(rs, Gw.widths(K, Gw.Display{}, rows, 0n)) == GatewayWidth.gw_pads_all(rs, Nat.sub(K, 1n), rows) : List<&2, List<&2, Nat>>}:
  match rs:
    case Nil{}:
      {==}
    case r <> rest:
      %gw.pads_row(K, rows, r) : {Gw.pads.all(r <> rest, Gw.widths(K, Gw.Display{}, rows, 0n)) == _ <> GatewayWidth.gw_pads_all(rest, Nat.sub(K, 1n), rows) : List<&2, List<&2, Nat>>}
      %gw.pads_all(rest, K, rows) : {Gw.pads.row(Gw.widths(K, Gw.Display{}, rows, 0n), r) <> Gw.pads.all(rest, Gw.widths(K, Gw.Display{}, rows, 0n)) == Gw.pads.row(Gw.widths(K, Gw.Display{}, rows, 0n), r) <> _ : List<&2, List<&2, Nat>>}
      {==}

def GatewayWidth.layout_pads(rows):
  gw.pads_all(rows, Gw.cols(rows), rows)
