# eukhe.com's Neovim: the proof of LAW key_k
# ==========================================
#
# On the editor after any events and an Esc (Idle.mk of it), k is
# Win.go_line to line - 1, which is on the text: Vim.fit settles it there
# on the same target (VCol.press, GL.cur).

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

def K.core(+fs: List<&2, T.Buf>, +s: T.St, hr: {B.Tgt.real(S.St.files(s), S.Win.tgt(S.St.win(s))) == True{} : Bool}, +fin: Fi.Final(Mo.Idle.mk(s)))
  -> {Laws.Claim.k(Mo.Idle.mk(s)) == True{} : Bool}:
  +z = Mo.Idle.mk(s)
  +ls = C.St.lines(z)
  +last = M.Move.last_line(ls)
  +line = C.St.line(z)
  +l = Nat.sub(line, 1n)
  +m = Nat.min(l, last)
  +w = S.Win.want(S.St.win(z))
  +a = M.Move.aim(ls, m, w)
  +p = {T.Pos{m, a} : T.Pos}
  +st = C.Win.go_line(z, l)
  +y = Vim.Vim.keep(z, st)
  +t = Vim.Vim.fit(y)
  +target = Nat.sub(Laws.Spec.at_line(Vim.Vim.frame(z)), 1n)
  %Equal.sym(T.St, Laws.Spec.press(z, "k"), t, Vc.VCol.press(z, "k", st, {==}, hr, {==})) : {Laws.Spec.moved_line(z, _, target) == True{} : Bool}
  +c1 = Mo.AtLine(t, Fi.Final.of_fit(y))
  +c2b = Equal.cong(T.Pos, Nat, q => S.Pos.line(q), S.Win.cur(S.St.win(t)), Mo.Cl3(ls, p), Mo.GL.cur(z, l))
  +c2c = Equal.cong(T.Pos, Nat, q => S.Pos.line(q), Mo.Cl3(ls, p), p, Mo.Cl3.on(ls, p, Mo.Clamp.on(ls, m, a, L.Nat.min_le_r(l, last), Mo.Aim.le(ls, m, w))))
  +c2 = Equal.trans(Nat, C.St.line(t), S.Pos.line(Mo.Cl3(ls, p)), m, c2b, c2c)
  +c3 = Mo.Min.eq_l(l, last, L.Nat.le_trans(l, line, last, L.Nat.sub_le(line, 1n), Mo.Fin.line_le(z, fin)))
  +c4 = Equal.cong(Nat, Nat, x => Nat.sub(x, 1n), line, Laws.Spec.at_line(Vim.Vim.frame(z)), Equal.sym(Nat, Laws.Spec.at_line(Vim.Vim.frame(z)), line, Mo.AtLine(z, fin)))
  +chain = Equal.trans(Nat, Laws.Spec.at_line(Vim.Vim.frame(t)), C.St.line(t), target, c1, Equal.trans(Nat, C.St.line(t), m, target, c2, Equal.trans(Nat, m, l, target, c3, c4)))
  Mo.ML.of(fs, z, t, target, Rl.Real.fit(y), chain)

def K.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.k(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  %Equal.sym(T.St, n, Mo.Idle.mk(n), Mo.Ready.eta(fs, rows, cols, evs)) : {Laws.Claim.k(_) == True{} : Bool}
  K.core(fs, n, Mo.Ready.real(fs, rows, cols, evs), Mo.Ready.fin(fs, rows, cols, evs))

def MotionLaws.key_k(fs, rows, cols, evs):
  K.law(fs, rows, cols, evs)
