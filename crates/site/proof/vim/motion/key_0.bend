# eukhe.com's Neovim: the proof of LAW key_0
# ==========================================
#
# On the editor after any events and an Esc (Idle.mk of it), 0 is Win.go
# to column 0 of the cursor's line, which is on the text: Vim.fit settles
# it there on the same target (VCol.press, Go.cur).

import Base
import ../../../vim/types.bend as T
import ../../../vim/buf.bend as B
import ../../../vim/move.bend as M
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/motion.bend as MotionLaws
import ../../base.bend as L
import ../../base/final.bend as Fi
import ../buffers/real.bend as Rl
import ./base.bend as Mo
import ./col_base.bend as Vc

def Zero.core(+fs: List<&2, T.Buf>, +s: T.St, hr: {B.Tgt.real(S.St.files(s), S.Win.tgt(S.St.win(s))) == True{} : Bool}, +fin: Fi.Final(Mo.Idle.mk(s)))
  -> {Laws.Claim.zero(Mo.Idle.mk(s)) == True{} : Bool}:
  +z = Mo.Idle.mk(s)
  +ls = C.St.lines(z)
  +line = C.St.line(z)
  +p = {T.Pos{line, 0n} : T.Pos}
  +st = C.Win.go(z, p, False{})
  +y = Vim.Vim.keep(z, st)
  +t = Vim.Vim.fit(y)
  +fy = Fi.Final.of_fit(y)
  +lz = Laws.Spec.at_line(Vim.Vim.frame(z))
  %Equal.sym(T.St, Laws.Spec.press(z, "0"), t, Vc.VCol.press(z, "0", st, {==}, hr, {==})) : {Laws.Spec.moved(z, _, lz, 0n) == True{} : Bool}
  +ecur = Equal.trans(T.Pos, S.Win.cur(S.St.win(t)), Mo.Cl3(ls, p), p, Mo.Go.cur(z, p), Mo.Cl3.on(ls, p, Mo.Clamp.on(ls, line, 0n, Mo.Fin.line_le(z, fin), L.Nat.le_zero(M.Move.last_col(ls, line)))))
  +eline = Equal.cong(T.Pos, Nat, q => S.Pos.line(q), S.Win.cur(S.St.win(t)), p, ecur)
  +ecol = Equal.cong(T.Pos, Nat, q => S.Pos.col(q), S.Win.cur(S.St.win(t)), p, ecur)
  +hl = Equal.trans(Nat, Laws.Spec.at_line(Vim.Vim.frame(t)), C.St.line(t), lz, Mo.AtLine(t, fy), Equal.trans(Nat, C.St.line(t), line, lz, eline, Equal.sym(Nat, lz, line, Mo.AtLine(z, fin))))
  +hc = Equal.trans(Nat, Laws.Spec.at_col(Vim.Vim.frame(t)), C.St.col(t), 0n, Mo.AtCol(t, fy), ecol)
  Mo.MV.of(fs, z, t, lz, 0n, Rl.Real.fit(y), hl, hc)

def Zero.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.zero(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  %Equal.sym(T.St, n, Mo.Idle.mk(n), Mo.Ready.eta(fs, rows, cols, evs)) : {Laws.Claim.zero(_) == True{} : Bool}
  Zero.core(fs, n, Mo.Ready.real(fs, rows, cols, evs), Mo.Ready.fin(fs, rows, cols, evs))

def MotionLaws.key_0(fs, rows, cols, evs):
  Zero.law(fs, rows, cols, evs)
