# LAWS: the Signal gateway aligns a table by display width. Each law is an
# open claim about the model in bend/gateway_width.bend (the formatter
# `push_table` of crates/eukhe-gateway/src/style.rs); PROOF.bend proves
# them (as GatewayWidth.<law>) with the lemmas of
# bend/proof_gateway_width.bend.

import Base
import ../bend/gateway_width.bend as Gw

# LAW: every row of a formatted table has the same display width per
# column: each row of the table (pre, row, post) renders as the widths of
# the columns, then its own last cell (the last column is not padded)
law table_aligned:
  for +pre: List<&2, List<&2, List<&2, Nat>>>
  for +row: List<&2, List<&2, Nat>>
  for +post: List<&2, List<&2, List<&2, Nat>>>
  {Gw.line(Nat.sub(Gw.cols(List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post)), 1n), Gw.Display{}, List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post), row, 0n) == List.append(&2, Nat, Gw.widths(Nat.sub(Gw.cols(List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post)), 1n), Gw.Display{}, List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post), 0n), [Gw.get.w(row, Gw.Display{}, Nat.sub(Gw.cols(List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post)), 1n))]) : List<&2, Nat>}

# LAW: an ASCII table (every glyph 1 wide) renders as the old formatter
# rendered it, which counted the characters of a cell
law ascii_unchanged:
  for +rows: List<&2, List<&2, List<&2, Nat>>>
  for +ones: Gw.Ones.rows(rows)
  {Gw.table(Gw.Display{}, rows) == Gw.table(Gw.Chars{}, rows) : List<&2, List<&2, Nat>>}
