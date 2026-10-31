# eukhe.com's Neovim: the proof of LAW col_j
# ==========================================
#
# On the editor after any events and an Esc (Idle.mk of it), j is
# Win.go_line to the next line at the column its want gives there
# (GL.cur); the column before is the one that want gives on its own line
# (Ready.aim). VCol.tail turns that into the claim.

import Base
import ../../../vim/types.bend as T
import ../../../vim/buf.bend as B
import ../../../vim/move.bend as M
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/motion.bend as MotionLaws
import ../../base/final.bend as Fi
import ./base.bend as Mo
import ./col_base.bend as Cb

def ColJ.core(+fs: List<&2, T.Buf>, +s: T.St, +hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, hr: {B.Tgt.real(S.St.files(s), S.Win.tgt(S.St.win(s))) == True{} : Bool}, +fin: Fi.Final(Mo.Idle.mk(s)), aim: Mo.Aim(Mo.Idle.mk(s)))
  -> {Laws.Claim.vcol_j(fs, Mo.Idle.mk(s)) == True{} : Bool}:
  +z = Mo.Idle.mk(s)
  +ls = C.St.lines(z)
  +l0 = C.St.line(z)
  +l = Nat.add(l0, 1n)
  +w = S.Win.want(S.St.win(z))
  +st = C.Win.go_line(z, l)
  +y = Vim.Vim.keep(z, st)
  +t = Vim.Vim.fit(y)
  +ft = Fi.Final.of_fit(y)
  +e_c = Equal.trans(Nat, Laws.Spec.at_col(Vim.Vim.frame(z)), C.St.col(z), M.Move.aim(ls, l0, w), Mo.AtCol(z, fin), aim)
  %Equal.sym(T.St, Laws.Spec.press(z, "j"), t, Cb.VCol.press(z, "j", st, {==}, hr, {==})) : {Laws.Claim.vcol(fs, z, _) == True{} : Bool}
  Cb.VCol.tail(fs, z, y, ls, l0, l, w, e_c, Mo.AtLine(z, fin), Mo.Lines.spec(fs, z, hf), Mo.GL.cur(z, l), Cb.VCol.gl_lines(z, l), Mo.Lines.spec(fs, t, hf), Mo.AtLine(t, ft), Mo.AtCol(t, ft))

def ColJ.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.vcol_j(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  %Equal.sym(T.St, n, Mo.Idle.mk(n), Mo.Ready.eta(fs, rows, cols, evs)) : {Laws.Claim.vcol_j(fs, _) == True{} : Bool}
  ColJ.core(fs, n, Mo.Ready.files(fs, rows, cols, evs), Mo.Ready.real(fs, rows, cols, evs), Mo.Ready.fin(fs, rows, cols, evs), Mo.Ready.aim(fs, rows, cols, evs))

def MotionLaws.col_j(fs, rows, cols, evs):
  ColJ.law(fs, rows, cols, evs)
