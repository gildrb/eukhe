# eukhe.com's Neovim: the proof of LAW urls
# =========================================
#
# The next step's act is good (proof/host/act.bend): gx opens only a
# target that starts "http(s)://" and is a run of a line of a file.

import Base
import ../../../vim/types.bend as T
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/host.bend as HostLaws
import ../../base.bend as L
import ./act.bend as A

def Urls.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>, +e: T.Ev) -> {Laws.Spec.url_ok(fs, Laws.Spec.act(Vim.Vim.step(Laws.Spec.run(fs, rows, cols, evs), e))) == True{} : Bool}:
  +a = Laws.Spec.act(Vim.Vim.step(Laws.Spec.run(fs, rows, cols, evs), e))
  L.And.r(Laws.Spec.honest(fs, a), Laws.Spec.url_ok(fs, a), A.Host.law(fs, rows, cols, evs, e))

def HostLaws.urls(fs, rows, cols, evs, e):
  Urls.law(fs, rows, cols, evs, e)
