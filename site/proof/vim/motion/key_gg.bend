# eukhe.com's Neovim: the proof of LAW key_gg
# ===========================================
#
# On the editor after any events and an Esc (Idle.mk of it), the first g
# waits (PendG, count 0) and Vim.fit keeps the target; the second jumps
# and goes to line 0 (Win.go_line), settled on the same target
# (VCol.press twice, GLJ.cur).

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

def GG.core(+fs: List<&2, T.Buf>, +s: T.St, +hr: {B.Tgt.real(S.St.files(s), S.Win.tgt(S.St.win(s))) == True{} : Bool})
  -> {Laws.Claim.gg(Mo.Idle.mk(s)) == True{} : Bool}:
  +z = Mo.Idle.mk(s)
  +st1 = S.St.set_count(S.St.set_pend(z, T.PendG{}), 0n)
  +y1 = Vim.Vim.keep(z, st1)
  +z1 = Vim.Vim.fit(y1)
  %Equal.sym(T.St, Laws.Spec.press(z, "g"), z1, Vc.VCol.press(z, "g", st1, {==}, hr, {==})) : {Laws.Spec.moved_line(z, Laws.Spec.press(_, "g"), 0n) == True{} : Bool}
  +ls = C.St.lines(z1)
  +last = M.Move.last_line(ls)
  +w = S.Win.want(S.St.win(z1))
  +a = M.Move.aim(ls, 0n, w)
  +p = {T.Pos{0n, a} : T.Pos}
  +st = C.Win.go_line(C.Win.jump(S.St.set_count(S.St.set_pend(z1, T.NoPend{}), 0n)), 0n)
  +y = Vim.Vim.keep(z1, st)
  +t = Vim.Vim.fit(y)
  %Equal.sym(T.St, Laws.Spec.press(z1, "g"), t, Vc.VCol.press(z1, "g", st, {==}, hr, {==})) : {Laws.Spec.moved_line(z, _, 0n) == True{} : Bool}
  +c1 = Mo.AtLine(t, Fi.Final.of_fit(y))
  +c2b = Equal.cong(T.Pos, Nat, q => S.Pos.line(q), S.Win.cur(S.St.win(t)), Mo.Cl3(ls, p), Mo.GLJ.cur(z1, 0n))
  +c2c = Equal.cong(T.Pos, Nat, q => S.Pos.line(q), Mo.Cl3(ls, p), p, Mo.Cl3.on(ls, p, Mo.Clamp.on(ls, 0n, a, L.Nat.le_zero(last), Mo.Aim.le(ls, 0n, w))))
  +c2 = Equal.trans(Nat, C.St.line(t), S.Pos.line(Mo.Cl3(ls, p)), 0n, c2b, c2c)
  +chain = Equal.trans(Nat, Laws.Spec.at_line(Vim.Vim.frame(t)), C.St.line(t), 0n, c1, c2)
  +ht = Equal.trans(T.Tgt, S.Win.tgt(S.St.win(t)), S.Win.tgt(S.St.win(z1)), S.Win.tgt(S.St.win(z)), Rl.Real.fit(y), Rl.Real.fit(y1))
  Mo.ML.of(fs, z, t, 0n, ht, chain)

def GG.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.gg(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  %Equal.sym(T.St, n, Mo.Idle.mk(n), Mo.Ready.eta(fs, rows, cols, evs)) : {Laws.Claim.gg(_) == True{} : Bool}
  GG.core(fs, n, Mo.Ready.real(fs, rows, cols, evs))

def MotionLaws.key_gg(fs, rows, cols, evs):
  GG.law(fs, rows, cols, evs)
