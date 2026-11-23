# eukhe.com's Neovim: the proof of LAW honest
# ===========================================
#
# The next step's act is good (proof/host/act.bend): yy copies only the
# install command, gx opens only a run of a line of a file.

import Base
import ../../../vim/types.bend as T
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/host.bend as HostLaws
import ../../base.bend as L
import ./act.bend as A

def Honest.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>, +e: T.Ev) -> {Laws.Spec.honest(fs, Laws.Spec.act(Vim.Vim.step(Laws.Spec.run(fs, rows, cols, evs), e))) == True{} : Bool}:
  +a = Laws.Spec.act(Vim.Vim.step(Laws.Spec.run(fs, rows, cols, evs), e))
  L.And.l(Laws.Spec.honest(fs, a), Laws.Spec.url_ok(fs, a), A.Host.law(fs, rows, cols, evs, e))

def HostLaws.honest(fs, rows, cols, evs, e):
  Honest.law(fs, rows, cols, evs, e)
