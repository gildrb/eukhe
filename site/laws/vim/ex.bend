# eukhe.com's Neovim: the laws of the command line
# ================================================
#
# The terms are in base.bend; LAWS.bend lists the requirements.

import Base
import ../../vim/types.bend as T
import ../../vim/vim.bend as V
import ./base.bend as Laws

# Laws
# ----

# LAW colon: ":" opens the command line with the cursor right after the colon (R1).
law colon:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.colon(Laws.Spec.normal(fs, rows, cols, evs), Laws.Spec.rows(rows, evs)) == True{} : Bool}

# LAW ex_line: ":5<CR>" goes to line 5, or the last line when there are fewer (R4).
law ex_line:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.ex_line(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}
