# eukhe: the proof of LAW layout_pad_rows
#
# PROOF: the layout's pads have one row per row of the measured table,
# whatever the widths (lpr.count, by induction on the rows).

import Base
import ../../bend/gateway_width.bend as Gw
import ../../laws/gateway_width.bend as GatewayWidth

def lpr.count(rows: List<&2, List<&2, Nat>>, +ws: List<&2, Nat>) -> {List.length(&2, List<&2, Nat>, Gw.pads.all(GatewayWidth.gw_table(rows), ws)) == List.length(&2, List<&2, Nat>, rows) : Nat}:
  match rows:
    case Nil{}:
      {==}
    case r <> rest:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, List<&2, Nat>, Gw.pads.all(GatewayWidth.gw_table(rest), ws)), List.length(&2, List<&2, Nat>, rest), lpr.count(rest, ws))

def GatewayWidth.layout_pad_rows(rows):
  lpr.count(rows, Gw.widths(Gw.cols(GatewayWidth.gw_table(rows)), Gw.Display{}, GatewayWidth.gw_table(rows), 0n))
