# eukhe: lemmas of area gateway_width: the layout's pads, column by column.
# The layout's pads walk its list of widths (Gw.pads.at); gwp.pads counts
# the columns instead and asks each column's width again. The two agree
# (gwp.all): the step the proofs of layout_exact and
# gateway_width_ffi_exact take from the model's pads to the spec's.

import Base
import ../../../bend/gateway_width.bend as Gw
import ../base.bend as LA

# the pads of row from column i over k columns: the width of the column
# less the display width of the row's cell (0 when it has none)
def gwp.pads(k: Nat, +rows: List<&2, List<&2, List<&2, Nat>>>, +row: List<&2, List<&2, Nat>>, +i: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      Nat.sub(Gw.col.w(rows, Gw.Display{}, i), Gw.get.w(row, Gw.Display{}, i)) <> gwp.pads(p, rows, row, 1n+i)

# the pads of every row of rs over k columns of the table rows
def gwp.pads_all(rs: List<&2, List<&2, List<&2, Nat>>>, +k: Nat, +rows: List<&2, List<&2, List<&2, Nat>>>) -> List<&2, List<&2, Nat>>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      gwp.pads(k, rows, r, 0n) <> gwp.pads_all(rest, k, rows)

# the pads from column i, given the width of column i and the K after it
def gwp.at(K: Nat, +rows: List<&2, List<&2, List<&2, Nat>>>, +row: List<&2, List<&2, Nat>>, +i: Nat) -> {Gw.pads.at(Gw.widths(K, Gw.Display{}, rows, 1n+i), Gw.col.w(rows, Gw.Display{}, i), row, i) == gwp.pads(K, rows, row, i) : List<&2, Nat>}:
  match K:
    case 0n:
      {==}
    case 1n+p:
      %gwp.at(p, rows, row, 1n+i) : {Gw.pads.at(Gw.widths(1n+p, Gw.Display{}, rows, 1n+i), Gw.col.w(rows, Gw.Display{}, i), row, i) == Nat.sub(Gw.col.w(rows, Gw.Display{}, i), Gw.get.w(row, Gw.Display{}, i)) <> _ : List<&2, Nat>}
      {==}

def gwp.row(K: Nat, +rows: List<&2, List<&2, List<&2, Nat>>>, +row: List<&2, List<&2, Nat>>) -> {Gw.pads.row(Gw.widths(K, Gw.Display{}, rows, 0n), row) == gwp.pads(Nat.sub(K, 1n), rows, row, 0n) : List<&2, Nat>}:
  match K:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, LA.gw.sub_zero(p)) : {Gw.pads.row(Gw.widths(1n+p, Gw.Display{}, rows, 0n), row) == gwp.pads(_, rows, row, 0n) : List<&2, Nat>}
      gwp.at(p, rows, row, 0n)

# the layout's pads over the widths of K columns are the counted pads
def gwp.all(rs: List<&2, List<&2, List<&2, Nat>>>, +K: Nat, +rows: List<&2, List<&2, List<&2, Nat>>>) -> {Gw.pads.all(rs, Gw.widths(K, Gw.Display{}, rows, 0n)) == gwp.pads_all(rs, Nat.sub(K, 1n), rows) : List<&2, List<&2, Nat>>}:
  match rs:
    case Nil{}:
      {==}
    case r <> rest:
      %gwp.row(K, rows, r) : {Gw.pads.all(r <> rest, Gw.widths(K, Gw.Display{}, rows, 0n)) == _ <> gwp.pads_all(rest, Nat.sub(K, 1n), rows) : List<&2, List<&2, Nat>>}
      %gwp.all(rest, K, rows) : {Gw.pads.row(Gw.widths(K, Gw.Display{}, rows, 0n), r) <> Gw.pads.all(rest, Gw.widths(K, Gw.Display{}, rows, 0n)) == Gw.pads.row(Gw.widths(K, Gw.Display{}, rows, 0n), r) <> _ : List<&2, List<&2, Nat>>}
      {==}
