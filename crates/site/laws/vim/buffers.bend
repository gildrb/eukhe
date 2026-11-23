# eukhe.com's Neovim: the laws of buffers (R8)
# ============================================
#
# The terms are in base.bend; LAWS.bend lists the requirements.

import Base
import ../../vim/types.bend as T
import ../../vim/vim.bend as V
import ./base.bend as Laws

# Laws
# ----

# LAW real_buffer: after any events, the window shows a file of fs, a
# folder of their paths, or the root.
law real_buffer:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Spec.real(fs, Laws.F.tgt(V.Vim.frame(Laws.Spec.run(fs, rows, cols, evs)))) == True{} : Bool}

# LAW start_file: the start shows the first file.
law start_file:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  {Laws.F.tgt(V.Vim.frame(V.Vim.init(fs, rows, cols))) == T.File{0n} : T.Tgt}
