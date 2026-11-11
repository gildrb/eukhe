# eukhe.com's Neovim: the proof of LAW real_buffer
# ================================================
#
# The editor after evs is Vim.final of some x (Reach.run), whose window
# shows a target B.Tgt.real holds of over x's files (Real.of); those are
# the files the start made of fs (Reach.files), over which B.Tgt.real is
# Spec.real (Real.spec).

import Base
import ../../../vim/types.bend as T
import ../../../vim/buf.bend as B
import ../../../vim/st.bend as S
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/buffers.bend as BuffersLaws
import ../../base/reach.bend as Re
import ./real.bend as Rb

def RealBuffer.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Spec.real(fs, Laws.F.tgt(Vim.Vim.frame(Laws.Spec.run(fs, rows, cols, evs)))) == True{} : Bool}:
  +x = Re.Reach.pre(evs, Vim.Vim.start(fs, rows, cols))
  +t = S.Win.tgt(S.St.win(Vim.Vim.final(x)))
  %Equal.sym(T.St, Laws.Spec.run(fs, rows, cols, evs), Vim.Vim.final(x), Re.Reach.run(fs, rows, cols, evs)) : {Laws.Spec.real(fs, Laws.F.tgt(Vim.Vim.frame(_))) == True{} : Bool}
  %Rb.Real.spec(fs, t) : {_ == True{} : Bool}
  %Re.Reach.files(evs, Vim.Vim.start(fs, rows, cols)) : {B.Tgt.real(_, t) == True{} : Bool}
  Rb.Real.of(x)

def BuffersLaws.real_buffer(fs, rows, cols, evs):
  RealBuffer.law(fs, rows, cols, evs)
