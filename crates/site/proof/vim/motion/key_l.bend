# eukhe.com's Neovim: the proof of LAW key_l
# ==========================================
#
# On the editor after any events and an Esc (Idle.mk of it), l is Win.go
# to column + 1 of the cursor's line, pulled back onto the line's last
# character (Clamp.line): Vim.fit settles it there on the same target
# (VCol.press, Go.cur).

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

# the column the claim names, read from the editor
def Ell.target(+fs: List<&2, T.Buf>, +s: T.St, hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, +fin: Fi.Final(Mo.Idle.mk(s)))
  -> {Laws.Spec.min(1n+Laws.Spec.at_col(Vim.Vim.frame(Mo.Idle.mk(s))), Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(Laws.Spec.lines(fs, Mo.Idle.mk(s)), Laws.Spec.at_line(Vim.Vim.frame(Mo.Idle.mk(s))))))) == Nat.min(Nat.add(C.St.col(s), 1n), M.Move.last_col(C.St.lines(Mo.Idle.mk(s)), C.St.line(s))) : Nat}:
  +z = Mo.Idle.mk(s)
  +ls = C.St.lines(z)
  +line = C.St.line(s)
  +col = C.St.col(s)
  +lc = M.Move.last_col(ls, line)
  +x = Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(Laws.Spec.lines(fs, z), Laws.Spec.at_line(Vim.Vim.frame(z)))))
  %Equal.sym(Nat, x, lc, Mo.Col.target(fs, s, hf, fin)) : {Laws.Spec.min(1n+Laws.Spec.at_col(Vim.Vim.frame(z)), _) == Nat.min(Nat.add(col, 1n), lc) : Nat}
  %Equal.sym(Nat, Laws.Spec.at_col(Vim.Vim.frame(z)), col, Mo.AtCol(z, fin)) : {Laws.Spec.min(1n+_, lc) == Nat.min(Nat.add(col, 1n), lc) : Nat}
  %Equal.sym(Nat, Laws.Spec.min(1n+col, lc), Nat.min(1n+col, lc), Sb.Spec.min_eq(1n+col, lc)) : {_ == Nat.min(Nat.add(col, 1n), lc) : Nat}
  %Equal.sym(Nat, Nat.add(col, 1n), 1n+col, Mo.Plus1(col)) : {Nat.min(1n+col, lc) == Nat.min(_, lc) : Nat}
  {==}

def Ell.core(+fs: List<&2, T.Buf>, +s: T.St, hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, hr: {B.Tgt.real(S.St.files(s), S.Win.tgt(S.St.win(s))) == True{} : Bool}, +fin: Fi.Final(Mo.Idle.mk(s)))
  -> {Laws.Claim.l(fs, Mo.Idle.mk(s)) == True{} : Bool}:
  +z = Mo.Idle.mk(s)
  +ls = C.St.lines(z)
  +line = C.St.line(z)
  +col = C.St.col(z)
  +lc = M.Move.last_col(ls, line)
  +c = Nat.min(Nat.add(col, 1n), lc)
  +p = {T.Pos{line, Nat.add(col, 1n)} : T.Pos}
  +q = {T.Pos{line, c} : T.Pos}
  +st = C.Win.go(z, p, False{})
  +y = Vim.Vim.keep(z, st)
  +t = Vim.Vim.fit(y)
  +fy = Fi.Final.of_fit(y)
  +fl = Mo.Fin.line_le(z, fin)
  +lz = Laws.Spec.at_line(Vim.Vim.frame(z))
  +cz = Laws.Spec.min(1n+Laws.Spec.at_col(Vim.Vim.frame(z)), Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(Laws.Spec.lines(fs, z), lz))))
  %Equal.sym(T.St, Laws.Spec.press(z, "l"), t, Vc.VCol.press(z, "l", st, {==}, hr, {==})) : {Laws.Spec.moved(z, _, lz, cz) == True{} : Bool}
  +h2 = Mo.Clamp.on(ls, line, c, fl, L.Nat.min_le_r(Nat.add(col, 1n), lc))
  +ecur = Equal.trans(T.Pos, S.Win.cur(S.St.win(t)), Mo.Cl3(ls, p), q, Mo.Go.cur(z, p), Mo.Cl3.step(ls, p, q, Mo.Clamp.line(ls, line, Nat.add(col, 1n), fl), h2))
  +eline = Equal.cong(T.Pos, Nat, r => S.Pos.line(r), S.Win.cur(S.St.win(t)), q, ecur)
  +ecol = Equal.cong(T.Pos, Nat, r => S.Pos.col(r), S.Win.cur(S.St.win(t)), q, ecur)
  +hl = Equal.trans(Nat, Laws.Spec.at_line(Vim.Vim.frame(t)), C.St.line(t), lz, Mo.AtLine(t, fy), Equal.trans(Nat, C.St.line(t), line, lz, eline, Equal.sym(Nat, lz, line, Mo.AtLine(z, fin))))
  +hc = Equal.trans(Nat, Laws.Spec.at_col(Vim.Vim.frame(t)), C.St.col(t), cz, Mo.AtCol(t, fy), Equal.trans(Nat, C.St.col(t), c, cz, ecol, Equal.sym(Nat, cz, c, Ell.target(fs, s, hf, fin))))
  Mo.MV.of(fs, z, t, lz, cz, Rl.Real.fit(y), hl, hc)

def Ell.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.l(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  %Equal.sym(T.St, n, Mo.Idle.mk(n), Mo.Ready.eta(fs, rows, cols, evs)) : {Laws.Claim.l(fs, _) == True{} : Bool}
  Ell.core(fs, n, Mo.Ready.files(fs, rows, cols, evs), Mo.Ready.real(fs, rows, cols, evs), Mo.Ready.fin(fs, rows, cols, evs))

def MotionLaws.key_l(fs, rows, cols, evs):
  Ell.law(fs, rows, cols, evs)
