# eukhe.com's Neovim: the laws of the mouse (R5)
# ==============================================
#
# The terms are in base.bend; LAWS.bend lists the requirements.

import Base
import ../../vim/types.bend as T
import ../../vim/vim.bend as V
import ./base.bend as Laws

# Laws
# ----

# LAW click: a click on text cell (r, c), right of the gutter, puts the
# cursor on line top + r (the last line when below the text) and column
# left + c - gutter (the line's last character when past its end).
law click:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  for +r: Nat
  for +c: Nat
  {Laws.Claim.click(fs, Laws.Spec.normal(fs, rows, cols, evs), Laws.Spec.rows(rows, evs), Laws.Spec.cols(cols, evs), r, c) == True{} : Bool}
