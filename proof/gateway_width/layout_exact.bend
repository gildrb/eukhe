# eukhe: the proof of LAW layout_exact
# The layout's widths are the model's widths of every column (the spec's
# on the table measured by display width); its pads are the model's pads
# counted column by column (LPads.gwp.all), which are the spec's on the
# table measured.

import Base
import ../../bend/gateway_width.bend as Gw
import ../../laws/gateway_width.bend as GatewayWidth
import ./base.bend as LA
import ./base/pads.bend as LPads

def gw.sp_pads(k: Nat, +rows: List<&2, List<&2, List<&2, Nat>>>, +row: List<&2, List<&2, Nat>>, +i: Nat) -> {LPads.gwp.pads(k, rows, row, i) == GatewayWidth.gw_sp_pads(k, GatewayWidth.gw_sp_measure(Gw.Display{}, rows), GatewayWidth.gw_sp_mrow(Gw.Display{}, row), i) : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %LA.gw.sp_colw(rows, Gw.Display{}, i) : {LPads.gwp.pads(1n+p, rows, row, i) == Nat.sub(_, GatewayWidth.gw_sp_cell(GatewayWidth.gw_sp_mrow(Gw.Display{}, row), i)) <> GatewayWidth.gw_sp_pads(p, GatewayWidth.gw_sp_measure(Gw.Display{}, rows), GatewayWidth.gw_sp_mrow(Gw.Display{}, row), 1n+i) : List<&2, Nat>}
      %LA.gw.sp_get(row, Gw.Display{}, i) : {LPads.gwp.pads(1n+p, rows, row, i) == Nat.sub(Gw.col.w(rows, Gw.Display{}, i), _) <> GatewayWidth.gw_sp_pads(p, GatewayWidth.gw_sp_measure(Gw.Display{}, rows), GatewayWidth.gw_sp_mrow(Gw.Display{}, row), 1n+i) : List<&2, Nat>}
      %gw.sp_pads(p, rows, row, 1n+i) : {LPads.gwp.pads(1n+p, rows, row, i) == Nat.sub(Gw.col.w(rows, Gw.Display{}, i), Gw.get.w(row, Gw.Display{}, i)) <> _ : List<&2, Nat>}
      {==}

def gw.sp_pads_all(rs: List<&2, List<&2, List<&2, Nat>>>, +k: Nat, +rows: List<&2, List<&2, List<&2, Nat>>>) -> {LPads.gwp.pads_all(rs, k, rows) == GatewayWidth.gw_sp_pads_all(GatewayWidth.gw_sp_measure(Gw.Display{}, rs), k, GatewayWidth.gw_sp_measure(Gw.Display{}, rows)) : List<&2, List<&2, Nat>>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +rest:
      %gw.sp_pads(k, rows, r, 0n) : {LPads.gwp.pads_all(r <> rest, k, rows) == _ <> GatewayWidth.gw_sp_pads_all(GatewayWidth.gw_sp_measure(Gw.Display{}, rest), k, GatewayWidth.gw_sp_measure(Gw.Display{}, rows)) : List<&2, List<&2, Nat>>}
      %gw.sp_pads_all(rest, k, rows) : {LPads.gwp.pads_all(r <> rest, k, rows) == LPads.gwp.pads(k, rows, r, 0n) <> _ : List<&2, List<&2, Nat>>}
      {==}

def GatewayWidth.layout_exact(rows):
  %LA.gw.sp_cols(rows, Gw.Display{}) : {Gw.layout(rows) == Gw.Lay{GatewayWidth.gw_sp_widths(_, GatewayWidth.gw_sp_measure(Gw.Display{}, rows), 0n), GatewayWidth.gw_sp_pads_all(GatewayWidth.gw_sp_measure(Gw.Display{}, rows), Nat.sub(_, 1n), GatewayWidth.gw_sp_measure(Gw.Display{}, rows))} : Gw.Lay}
  %LA.gw.sp_widths(Gw.cols(rows), Gw.Display{}, rows, 0n) : {Gw.layout(rows) == Gw.Lay{_, GatewayWidth.gw_sp_pads_all(GatewayWidth.gw_sp_measure(Gw.Display{}, rows), Nat.sub(Gw.cols(rows), 1n), GatewayWidth.gw_sp_measure(Gw.Display{}, rows))} : Gw.Lay}
  %gw.sp_pads_all(rows, Nat.sub(Gw.cols(rows), 1n), rows) : {Gw.layout(rows) == Gw.Lay{Gw.widths(Gw.cols(rows), Gw.Display{}, rows, 0n), _} : Gw.Lay}
  %LPads.gwp.all(rows, Gw.cols(rows), rows) : {Gw.layout(rows) == Gw.Lay{Gw.widths(Gw.cols(rows), Gw.Display{}, rows, 0n), _} : Gw.Lay}
  {==}
