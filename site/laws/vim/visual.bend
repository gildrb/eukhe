# eukhe.com's Neovim: the laws of yanking (R9)
# =============================================
#
# The terms are in base.bend; LAWS.bend lists the requirements.

import Base
import ../../vim/types.bend as T
import ../../vim/vim.bend as V
import ./base.bend as Laws

# Laws
# ----

# LAW yank_line: after any events and an Esc, Y on a file copies the
# cursor's line and its line break (R9).
law yank_line:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.yank_line(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW yank_char: after any events and an Esc, v then y on a file copies the
# character under the cursor, or on an empty line its line break (R9).
law yank_char:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.yank_char(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}
