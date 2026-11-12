# eukhe.com's Neovim: the proof of LAW key_j
# ==========================================
#
# On the editor after any events and an Esc (Idle.mk of it), j is
# Win.go_line to the next line: Vim.final settles it on the same target
# (Final.real) with the cursor on min(line + 1, last) (GL.cur, Cl3.on).

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
import ../screen/base.bend as Sb
import ../buffers/real.bend as Rl
import ./base.bend as Mo
import ./col_base.bend as Vc

# the target the claim names, read from the editor
def J.target(+fs: List<&2, T.Buf>, +s: T.St, hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, fin: Fi.Final(Mo.Idle.mk(s)))
  -> {Laws.Spec.min(1n+Laws.Spec.at_line(Vim.Vim.frame(Mo.Idle.mk(s))), Laws.Spec.last(Laws.Spec.count(Laws.Spec.lines(fs, Mo.Idle.mk(s))))) == Nat.min(Nat.add(C.St.line(s), 1n), M.Move.last_line(C.St.lines(Mo.Idle.mk(s)))) : Nat}:
  +z = Mo.Idle.mk(s)
  +ls = C.St.lines(z)
  +last = M.Move.last_line(ls)
  +line = C.St.line(s)
  %Equal.sym(Nat, Nat.add(S.Win.top(S.St.win(z)), Nat.sub(line, S.Win.top(S.St.win(z)))), line, Mo.AtLine(z, fin)) : {Laws.Spec.min(1n+_, Laws.Spec.last(Laws.Spec.count(Laws.Spec.lines(fs, z)))) == Nat.min(Nat.add(line, 1n), last) : Nat}
  %Equal.sym(List<&2, String>, Laws.Spec.lines(fs, z), ls, Mo.Lines.spec(fs, z, hf)) : {Laws.Spec.min(1n+line, Laws.Spec.last(Laws.Spec.count(_))) == Nat.min(Nat.add(line, 1n), last) : Nat}
  %Equal.sym(Nat, Laws.Spec.last(Laws.Spec.count(ls)), last, Mo.LastLine.eq(ls)) : {Laws.Spec.min(1n+line, _) == Nat.min(Nat.add(line, 1n), last) : Nat}
  %Equal.sym(Nat, Laws.Spec.min(1n+line, last), Nat.min(1n+line, last), Sb.Spec.min_eq(1n+line, last)) : {_ == Nat.min(Nat.add(line, 1n), last) : Nat}
  %Equal.sym(Nat, Nat.add(line, 1n), 1n+line, Mo.Plus1(line)) : {Nat.min(1n+line, last) == Nat.min(_, last) : Nat}
  {==}

def J.core(+fs: List<&2, T.Buf>, +s: T.St, hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, hr: {B.Tgt.real(S.St.files(s), S.Win.tgt(S.St.win(s))) == True{} : Bool}, +fin: Fi.Final(Mo.Idle.mk(s)))
  -> {Laws.Claim.j(fs, Mo.Idle.mk(s)) == True{} : Bool}:
  +z = Mo.Idle.mk(s)
  +ls = C.St.lines(z)
  +last = M.Move.last_line(ls)
  +l = Nat.add(C.St.line(z), 1n)
  +m = Nat.min(l, last)
  +w = S.Win.want(S.St.win(z))
  +a = M.Move.aim(ls, m, w)
  +p = {T.Pos{m, a} : T.Pos}
  +st = C.Win.go_line(z, l)
  +y = Vim.Vim.keep(z, st)
  +t = Vim.Vim.fit(y)
  +target = Laws.Spec.min(1n+Laws.Spec.at_line(Vim.Vim.frame(z)), Laws.Spec.last(Laws.Spec.count(Laws.Spec.lines(fs, z))))
  %Equal.sym(T.St, Laws.Spec.press(z, "j"), t, Vc.VCol.press(z, "j", st, {==}, hr, {==})) : {Laws.Spec.moved_line(z, _, target) == True{} : Bool}
  +c1 = Mo.AtLine(t, Fi.Final.of_fit(y))
  +c2b = Equal.cong(T.Pos, Nat, q => S.Pos.line(q), S.Win.cur(S.St.win(t)), Mo.Cl3(ls, p), Mo.GL.cur(z, l))
  +c2c = Equal.cong(T.Pos, Nat, q => S.Pos.line(q), Mo.Cl3(ls, p), p, Mo.Cl3.on(ls, p, Mo.Clamp.on(ls, m, a, L.Nat.min_le_r(l, last), Mo.Aim.le(ls, m, w))))
  +c2 = Equal.trans(Nat, C.St.line(t), S.Pos.line(Mo.Cl3(ls, p)), m, c2b, c2c)
  +c3 = Equal.sym(Nat, target, m, J.target(fs, s, hf, fin))
  +chain = Equal.trans(Nat, Laws.Spec.at_line(Vim.Vim.frame(t)), C.St.line(t), target, c1, Equal.trans(Nat, C.St.line(t), m, target, c2, c3))
  Mo.ML.of(fs, z, t, target, Rl.Real.fit(y), chain)

def J.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.j(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  %Equal.sym(T.St, n, Mo.Idle.mk(n), Mo.Ready.eta(fs, rows, cols, evs)) : {Laws.Claim.j(fs, _) == True{} : Bool}
  J.core(fs, n, Mo.Ready.files(fs, rows, cols, evs), Mo.Ready.real(fs, rows, cols, evs), Mo.Ready.fin(fs, rows, cols, evs))

def MotionLaws.key_j(fs, rows, cols, evs):
  J.law(fs, rows, cols, evs)
