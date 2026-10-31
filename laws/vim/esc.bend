# eukhe.com's Neovim: the laws of Esc
# ===================================
#
# The terms are in base.bend; LAWS.bend lists the requirements.

import Base
import ../../vim/types.bend as T
import ../../vim/vim.bend as V
import ./base.bend as Laws

# Laws
# ----

# LAW esc_closes: after any events and an Esc, no float is open (A3).
law esc_closes:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.F.float(V.Vim.frame(Laws.Spec.normal(fs, rows, cols, evs))) == None{} : Maybe<&2, T.Float>}

# LAW oil_close: after any events, Esc then Ctrl-c shows a file.
law oil_close:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Spec.is_file(Laws.F.tgt(V.Vim.frame(Laws.Spec.press(Laws.Spec.normal(fs, rows, cols, evs), "<C-c>")))) == True{} : Bool}

# LAW esc_keeps: Esc never changes what the window shows.
law esc_keeps:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Spec.same_tgt(Laws.F.tgt(V.Vim.frame(Laws.Spec.run(fs, rows, cols, evs))), Laws.F.tgt(V.Vim.frame(Laws.Spec.normal(fs, rows, cols, evs)))) == True{} : Bool}

# LAW esc_idle: in normal mode Esc moves neither the cursor nor the view (R8).
law esc_idle:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.esc_idle(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}
