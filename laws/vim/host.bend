# eukhe.com's Neovim: the laws of the host (R7)
# =============================================
#
# The terms are in base.bend; LAWS.bend lists the requirements.

import Base
import ../../vim/types.bend as T
import ../../vim/vim.bend as V
import ./base.bend as Laws

# Laws
# ----

# LAW honest: after any events, the next one makes the host copy only the
# install command and open only a URL written in a file.
law honest:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  for e: T.Ev
  {Laws.Spec.honest(fs, Laws.Spec.act(V.Vim.step(Laws.Spec.run(fs, rows, cols, evs), e))) == True{} : Bool}

# LAW urls: after any events, the next one opens only a web address
# (http:// or https://) written in a file (R7).
law urls:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  for e: T.Ev
  {Laws.Spec.url_ok(fs, Laws.Spec.act(V.Vim.step(Laws.Spec.run(fs, rows, cols, evs), e))) == True{} : Bool}
