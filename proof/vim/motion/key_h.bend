# eukhe.com's Neovim: the proof of LAW key_h
# ==========================================
#
# On the editor after any events and an Esc (Idle.mk of it), h is Win.go
# to column - 1 of the cursor's line, which is on the text: Vim.fit
# settles it there on the same target (VCol.press, Go.cur).

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

def H.core(+fs: List<&2, T.Buf>, +s: T.St, hr: {B.Tgt.real(S.St.files(s), S.Win.tgt(S.St.win(s))) == True{} : Bool}, +fin: Fi.Final(Mo.Idle.mk(s)))
  -> {Laws.Claim.h(Mo.Idle.mk(s)) == True{} : Bool}:
  +z = Mo.Idle.mk(s)
  +ls = C.St.lines(z)
  +line = C.St.line(z)
  +col = C.St.col(z)
  +c = Nat.sub(col, 1n)
  +p = {T.Pos{line, c} : T.Pos}
  +st = C.Win.go(z, p, False{})
  +y = Vim.Vim.keep(z, st)
  +t = Vim.Vim.fit(y)
  +fy = Fi.Final.of_fit(y)
  +lz = Laws.Spec.at_line(Vim.Vim.frame(z))
  +cz = Nat.sub(Laws.Spec.at_col(Vim.Vim.frame(z)), 1n)
  %Equal.sym(T.St, Laws.Spec.press(z, "h"), t, Vc.VCol.press(z, "h", st, {==}, hr, {==})) : {Laws.Spec.moved(z, _, lz, cz) == True{} : Bool}
  +hc0 = L.Nat.le_trans(c, col, M.Move.last_col(ls, line), L.Nat.sub_le(col, 1n), Mo.Fin.col_le(z, fin))
  +ecur = Equal.trans(T.Pos, S.Win.cur(S.St.win(t)), Mo.Cl3(ls, p), p, Mo.Go.cur(z, p), Mo.Cl3.on(ls, p, Mo.Clamp.on(ls, line, c, Mo.Fin.line_le(z, fin), hc0)))
  +eline = Equal.cong(T.Pos, Nat, q => S.Pos.line(q), S.Win.cur(S.St.win(t)), p, ecur)
  +ecol = Equal.cong(T.Pos, Nat, q => S.Pos.col(q), S.Win.cur(S.St.win(t)), p, ecur)
  +hl = Equal.trans(Nat, Laws.Spec.at_line(Vim.Vim.frame(t)), C.St.line(t), lz, Mo.AtLine(t, fy), Equal.trans(Nat, C.St.line(t), line, lz, eline, Equal.sym(Nat, lz, line, Mo.AtLine(z, fin))))
  +ecz = Equal.cong(Nat, Nat, x => Nat.sub(x, 1n), col, Laws.Spec.at_col(Vim.Vim.frame(z)), Equal.sym(Nat, Laws.Spec.at_col(Vim.Vim.frame(z)), col, Mo.AtCol(z, fin)))
  +hc = Equal.trans(Nat, Laws.Spec.at_col(Vim.Vim.frame(t)), C.St.col(t), cz, Mo.AtCol(t, fy), Equal.trans(Nat, C.St.col(t), c, cz, ecol, ecz))
  Mo.MV.of(fs, z, t, lz, cz, Rl.Real.fit(y), hl, hc)

def H.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.h(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  %Equal.sym(T.St, n, Mo.Idle.mk(n), Mo.Ready.eta(fs, rows, cols, evs)) : {Laws.Claim.h(_) == True{} : Bool}
  H.core(fs, n, Mo.Ready.real(fs, rows, cols, evs), Mo.Ready.fin(fs, rows, cols, evs))

def MotionLaws.key_h(fs, rows, cols, evs):
  H.law(fs, rows, cols, evs)
