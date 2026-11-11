# eukhe: the proof of LAW table_line_per_row: the table renders one line per
# row it walks

import Base
import ../../bend/gateway_width.bend as Gw
import ../../laws/gateway_width.bend as GatewayWidth

def tlr.go(rs: List<&2, List<&2, List<&2, Nat>>>, +k: Nat, +m: Gw.Measure, +rows: List<&2, List<&2, List<&2, Nat>>>) -> {List.length(&2, List<&2, Nat>, Gw.table.go(rs, k, m, rows)) == List.length(&2, List<&2, List<&2, Nat>>, rs) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case r <> +rest:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, List<&2, Nat>, Gw.table.go(rest, k, m, rows)), List.length(&2, List<&2, List<&2, Nat>>, rest), tlr.go(rest, k, m, rows))

def GatewayWidth.table_line_per_row(m, rows):
  tlr.go(rows, Nat.sub(Gw.cols(rows), 1n), m, rows)
