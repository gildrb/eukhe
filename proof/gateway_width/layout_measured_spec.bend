# eukhe: the proof of LAW layout_measured_spec
#
# PROOF: on a measured table a cell's display width is its measured width
# (lm.cell: a one-glyph cell sums to its glyph), so a column's width is
# the spec's (lm.colw), the count of columns too (lm.cols: a measured row
# has one cell per width) and the widths (lm.widths, by the count); the
# pads are layout_pads' gw_pads_all, which is the spec's row by row
# (lm.rpads, lm.pall).

import Base
import ../../bend/gateway_width.bend as Gw
import ../../laws/gateway_width.bend as GatewayWidth
import ../base/nat.bend as LNat
import ./layout_pads.bend as PLayoutPads

# a measured cell's display width is its width
def lm.cell(r: List<&2, Nat>, i: Nat) -> {Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, i) == GatewayWidth.gw_cell(r, i) : Nat}:
  match r:
    case Nil{}:
      {==}
    case w <> rest:
      match i:
        case 0n:
          LNat.wn_add_zero_r(w)
        case 1n+p:
          lm.cell(rest, p)

# a column's width is the spec's
def lm.colw(rows: List<&2, List<&2, Nat>>, +i: Nat) -> {Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i) == GatewayWidth.gw_colw(rows, i) : Nat}:
  match rows:
    case Nil{}:
      {==}
    case +r <> +rest:
      %lm.cell(r, i) : {Gw.col.w(GatewayWidth.gw_table(r <> rest), Gw.Display{}, i) == Nat.max(_, GatewayWidth.gw_colw(rest, i)) : Nat}
      %lm.colw(rest, i) : {Gw.col.w(GatewayWidth.gw_table(r <> rest), Gw.Display{}, i) == Nat.max(Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, i), _) : Nat}
      {==}

# a measured row has one cell per width
def lm.len(r: List<&2, Nat>) -> {List.length(&2, List<&2, Nat>, GatewayWidth.gw_cells(r)) == List.length(&2, Nat, r) : Nat}:
  match r:
    case Nil{}:
      {==}
    case w <> rest:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, List<&2, Nat>, GatewayWidth.gw_cells(rest)), List.length(&2, Nat, rest), lm.len(rest))

# the count of columns is the spec's
def lm.cols(rows: List<&2, List<&2, Nat>>) -> {Gw.cols(GatewayWidth.gw_table(rows)) == GatewayWidth.gw_cols(rows) : Nat}:
  match rows:
    case Nil{}:
      {==}
    case +r <> +rest:
      %lm.len(r) : {Gw.cols(GatewayWidth.gw_table(r <> rest)) == Nat.max(_, GatewayWidth.gw_cols(rest)) : Nat}
      %lm.cols(rest) : {Gw.cols(GatewayWidth.gw_table(r <> rest)) == Nat.max(List.length(&2, List<&2, Nat>, GatewayWidth.gw_cells(r)), _) : Nat}
      {==}

# the widths of k columns are the spec's
def lm.widths(k: Nat, +rows: List<&2, List<&2, Nat>>, +i: Nat) -> {Gw.widths(k, Gw.Display{}, GatewayWidth.gw_table(rows), i) == GatewayWidth.gw_widths_spec(k, rows, i) : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %lm.colw(rows, i) : {Gw.widths(1n+p, Gw.Display{}, GatewayWidth.gw_table(rows), i) == _ <> GatewayWidth.gw_widths_spec(p, rows, 1n+i) : List<&2, Nat>}
      %lm.widths(p, rows, 1n+i) : {Gw.widths(1n+p, Gw.Display{}, GatewayWidth.gw_table(rows), i) == Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i) <> _ : List<&2, Nat>}
      {==}

# a row's pads are the spec's
def lm.rpads(k: Nat, +rows: List<&2, List<&2, Nat>>, +r: List<&2, Nat>, +i: Nat) -> {GatewayWidth.gw_pads(k, GatewayWidth.gw_table(rows), GatewayWidth.gw_cells(r), i) == GatewayWidth.gw_row_pads(k, rows, r, i) : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %lm.colw(rows, i) : {GatewayWidth.gw_pads(1n+p, GatewayWidth.gw_table(rows), GatewayWidth.gw_cells(r), i) == Nat.sub(_, GatewayWidth.gw_cell(r, i)) <> GatewayWidth.gw_row_pads(p, rows, r, 1n+i) : List<&2, Nat>}
      %lm.cell(r, i) : {GatewayWidth.gw_pads(1n+p, GatewayWidth.gw_table(rows), GatewayWidth.gw_cells(r), i) == Nat.sub(Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i), _) <> GatewayWidth.gw_row_pads(p, rows, r, 1n+i) : List<&2, Nat>}
      %lm.rpads(p, rows, r, 1n+i) : {GatewayWidth.gw_pads(1n+p, GatewayWidth.gw_table(rows), GatewayWidth.gw_cells(r), i) == Nat.sub(Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i), Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, i)) <> _ : List<&2, Nat>}
      {==}

# every row's pads are the spec's
def lm.pall(rs: List<&2, List<&2, Nat>>, +k: Nat, +rows: List<&2, List<&2, Nat>>) -> {GatewayWidth.gw_pads_all(GatewayWidth.gw_table(rs), k, GatewayWidth.gw_table(rows)) == GatewayWidth.gw_pads_spec(rs, k, rows) : List<&2, List<&2, Nat>>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +rest:
      %lm.rpads(k, rows, r, 0n) : {GatewayWidth.gw_pads_all(GatewayWidth.gw_table(r <> rest), k, GatewayWidth.gw_table(rows)) == _ <> GatewayWidth.gw_pads_spec(rest, k, rows) : List<&2, List<&2, Nat>>}
      %lm.pall(rest, k, rows) : {GatewayWidth.gw_pads_all(GatewayWidth.gw_table(r <> rest), k, GatewayWidth.gw_table(rows)) == GatewayWidth.gw_pads(k, GatewayWidth.gw_table(rows), GatewayWidth.gw_cells(r), 0n) <> _ : List<&2, List<&2, Nat>>}
      {==}

# a layout is its widths and its pads
def lm.lay(-w: List<&2, Nat>, -p: List<&2, List<&2, Nat>>, -w2: List<&2, Nat>, -p2: List<&2, List<&2, Nat>>, ew: {w == w2 : List<&2, Nat>}, ep: {p == p2 : List<&2, List<&2, Nat>>}) -> {Gw.Lay{w, p} == Gw.Lay{w2, p2} : Gw.Lay}:
  %ew : {Gw.Lay{w, p} == Gw.Lay{_, p2} : Gw.Lay}
  %ep : {Gw.Lay{w, p} == Gw.Lay{w, _} : Gw.Lay}
  {==}

def GatewayWidth.layout_measured_spec(rows):
  +t = GatewayWidth.gw_table(rows)
  +k = GatewayWidth.gw_cols(rows)
  +ec = lm.cols(rows)
  +ws = Gw.widths(Gw.cols(t), Gw.Display{}, t, 0n)
  lm.lay(ws, Gw.pads.all(t, ws), GatewayWidth.gw_widths_spec(k, rows, 0n), GatewayWidth.gw_pads_spec(rows, Nat.sub(k, 1n), rows),
    Equal.trans(List<&2, Nat>, ws, Gw.widths(k, Gw.Display{}, t, 0n), GatewayWidth.gw_widths_spec(k, rows, 0n),
      Equal.cong(Nat, List<&2, Nat>, n => Gw.widths(n, Gw.Display{}, t, 0n), Gw.cols(t), k, ec),
      lm.widths(k, rows, 0n)),
    Equal.trans(List<&2, List<&2, Nat>>, Gw.pads.all(t, ws), GatewayWidth.gw_pads_all(t, Nat.sub(k, 1n), t), GatewayWidth.gw_pads_spec(rows, Nat.sub(k, 1n), rows),
      Equal.trans(List<&2, List<&2, Nat>>, Gw.pads.all(t, ws), GatewayWidth.gw_pads_all(t, Nat.sub(Gw.cols(t), 1n), t), GatewayWidth.gw_pads_all(t, Nat.sub(k, 1n), t),
        GatewayWidth.layout_pads(t),
        Equal.cong(Nat, List<&2, List<&2, Nat>>, n => GatewayWidth.gw_pads_all(t, Nat.sub(n, 1n), t), Gw.cols(t), k, ec)),
      lm.pall(rows, Nat.sub(k, 1n), rows)))
