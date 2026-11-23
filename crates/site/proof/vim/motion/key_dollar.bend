# eukhe.com's Neovim: the proof of LAW key_dollar
# ===============================================
#
# On the editor after any events and an Esc (Idle.mk of it), $ (no
# count) is Key.dollar on the cursor's line: the line's last column,
# settled by Vim.fit on the same target (VCol.press, Dol.cur).

import Base
import ../../../vim/types.bend as T
import ../../../vim/buf.bend as B
import ../../../vim/move.bend as M
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../vim/keys.bend as K
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/motion.bend as MotionLaws
import ../../base.bend as L
import ../../base/final.bend as Fi
import ../buffers/real.bend as Rl
import ./base.bend as Mo
import ./col_base.bend as Vc

def Dollar.core(+fs: List<&2, T.Buf>, +s: T.St, hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, hr: {B.Tgt.real(S.St.files(s), S.Win.tgt(S.St.win(s))) == True{} : Bool}, +fin: Fi.Final(Mo.Idle.mk(s)))
  -> {Laws.Claim.dollar(fs, Mo.Idle.mk(s)) == True{} : Bool}:
  +z = Mo.Idle.mk(s)
  +ls = C.St.lines(z)
  +last = M.Move.last_line(ls)
  +line = C.St.line(z)
  +l0 = Nat.add(line, 0n)
  +m0 = Nat.min(l0, last)
  +lc = M.Move.last_col(ls, line)
  +q = {T.Pos{line, lc} : T.Pos}
  +st = K.Key.dollar(z, l0)
  +y = Vim.Vim.keep(z, st)
  +t = Vim.Vim.fit(y)
  +fy = Fi.Final.of_fit(y)
  +fl = Mo.Fin.line_le(z, fin)
  +lz = Laws.Spec.at_line(Vim.Vim.frame(z))
  +cz = Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(Laws.Spec.lines(fs, z), lz)))
  %Equal.sym(T.St, Laws.Spec.press(z, "$"), t, Vc.VCol.press(z, "$", st, {==}, hr, {==})) : {Laws.Spec.moved(z, _, lz, cz) == True{} : Bool}
  +em = Equal.trans(Nat, m0, Nat.min(line, last), line, Equal.cong(Nat, Nat, x => Nat.min(x, last), l0, line, L.Nat.zero_r(line)), Mo.Min.eq_l(line, last, fl))
  +e1 = Equal.cong(Nat, T.Pos, x => Mo.Cl2(ls, T.Pos{x, M.Move.last_col(ls, x)}), m0, line, em)
  +e2 = Mo.Cl2.on(ls, q, Mo.Clamp.on(ls, line, lc, fl, L.Nat.le_refl(lc)))
  +ecur = Equal.trans(T.Pos, S.Win.cur(S.St.win(t)), Mo.Cl2(ls, T.Pos{m0, M.Move.last_col(ls, m0)}), q, Mo.Dol.cur(z, l0), Equal.trans(T.Pos, Mo.Cl2(ls, T.Pos{m0, M.Move.last_col(ls, m0)}), Mo.Cl2(ls, q), q, e1, e2))
  +eline = Equal.cong(T.Pos, Nat, r => S.Pos.line(r), S.Win.cur(S.St.win(t)), q, ecur)
  +ecol = Equal.cong(T.Pos, Nat, r => S.Pos.col(r), S.Win.cur(S.St.win(t)), q, ecur)
  +hl = Equal.trans(Nat, Laws.Spec.at_line(Vim.Vim.frame(t)), C.St.line(t), lz, Mo.AtLine(t, fy), Equal.trans(Nat, C.St.line(t), line, lz, eline, Equal.sym(Nat, lz, line, Mo.AtLine(z, fin))))
  +hc = Equal.trans(Nat, Laws.Spec.at_col(Vim.Vim.frame(t)), C.St.col(t), cz, Mo.AtCol(t, fy), Equal.trans(Nat, C.St.col(t), lc, cz, ecol, Equal.sym(Nat, cz, lc, Mo.Col.target(fs, s, hf, fin))))
  Mo.MV.of(fs, z, t, lz, cz, Rl.Real.fit(y), hl, hc)

def Dollar.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.dollar(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  %Equal.sym(T.St, n, Mo.Idle.mk(n), Mo.Ready.eta(fs, rows, cols, evs)) : {Laws.Claim.dollar(fs, _) == True{} : Bool}
  Dollar.core(fs, n, Mo.Ready.files(fs, rows, cols, evs), Mo.Ready.real(fs, rows, cols, evs), Mo.Ready.fin(fs, rows, cols, evs))

def MotionLaws.key_dollar(fs, rows, cols, evs):
  Dollar.law(fs, rows, cols, evs)
