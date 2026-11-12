# eukhe.com's Neovim: the proof of LAW key_G
# ==========================================
#
# On the editor after any events and an Esc (Idle.mk of it), G (no
# count) jumps and goes to the last line: Win.go_line to it, settled by
# Vim.fit on the same target (VCol.press, GLJ.cur).

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

def BigG.core(+fs: List<&2, T.Buf>, +s: T.St, hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, hr: {B.Tgt.real(S.St.files(s), S.Win.tgt(S.St.win(s))) == True{} : Bool}, +fin: Fi.Final(Mo.Idle.mk(s)))
  -> {Laws.Claim.G(fs, Mo.Idle.mk(s)) == True{} : Bool}:
  +z = Mo.Idle.mk(s)
  +ls = C.St.lines(z)
  +last = M.Move.last_line(ls)
  +m = Nat.min(last, last)
  +w = S.Win.want(S.St.win(z))
  +a = M.Move.aim(ls, m, w)
  +p = {T.Pos{m, a} : T.Pos}
  +st = C.Win.go_line(C.Win.jump(S.St.set_count(S.St.set_pend(z, T.NoPend{}), 0n)), last)
  +y = Vim.Vim.keep(z, st)
  +t = Vim.Vim.fit(y)
  +target = Laws.Spec.last(Laws.Spec.count(Laws.Spec.lines(fs, z)))
  %Equal.sym(T.St, Laws.Spec.press(z, "G"), t, Vc.VCol.press(z, "G", st, {==}, hr, {==})) : {Laws.Spec.moved_line(z, _, target) == True{} : Bool}
  +c1 = Mo.AtLine(t, Fi.Final.of_fit(y))
  +c2b = Equal.cong(T.Pos, Nat, q => S.Pos.line(q), S.Win.cur(S.St.win(t)), Mo.Cl3(ls, p), Mo.GLJ.cur(z, last))
  +c2c = Equal.cong(T.Pos, Nat, q => S.Pos.line(q), Mo.Cl3(ls, p), p, Mo.Cl3.on(ls, p, Mo.Clamp.on(ls, m, a, L.Nat.min_le_r(last, last), Mo.Aim.le(ls, m, w))))
  +c2 = Equal.trans(Nat, C.St.line(t), S.Pos.line(Mo.Cl3(ls, p)), m, c2b, c2c)
  +c3 = Mo.Min.eq_l(last, last, L.Nat.le_refl(last))
  +c4a = Equal.cong(List<&2, String>, Nat, x => Laws.Spec.last(Laws.Spec.count(x)), ls, Laws.Spec.lines(fs, z), Equal.sym(List<&2, String>, Laws.Spec.lines(fs, z), ls, Mo.Lines.spec(fs, z, hf)))
  +c4 = Equal.trans(Nat, last, Laws.Spec.last(Laws.Spec.count(ls)), target, Equal.sym(Nat, Laws.Spec.last(Laws.Spec.count(ls)), last, Mo.LastLine.eq(ls)), c4a)
  +chain = Equal.trans(Nat, Laws.Spec.at_line(Vim.Vim.frame(t)), C.St.line(t), target, c1, Equal.trans(Nat, C.St.line(t), m, target, c2, Equal.trans(Nat, m, last, target, c3, c4)))
  Mo.ML.of(fs, z, t, target, Rl.Real.fit(y), chain)

def BigG.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.G(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  %Equal.sym(T.St, n, Mo.Idle.mk(n), Mo.Ready.eta(fs, rows, cols, evs)) : {Laws.Claim.G(fs, _) == True{} : Bool}
  BigG.core(fs, n, Mo.Ready.files(fs, rows, cols, evs), Mo.Ready.real(fs, rows, cols, evs), Mo.Ready.fin(fs, rows, cols, evs))

def MotionLaws.key_G(fs, rows, cols, evs):
  BigG.law(fs, rows, cols, evs)
