# eukhe.com's Neovim: the proof of LAW col_gg
# ===========================================
#
# On the editor after any events and an Esc (z = Idle.mk of it), the
# first g only waits: Vim.final settles it at Vim.fit (Final.real) as x1,
# with z's cursor (G1.cur, the cursor on the text) and lines. The second
# g is a jump, then Win.go_line to the first line at the column x1's want
# gives there (GLJ.cur); x1's column is the one that want gives on its
# own line (Aim.fit). VCol.tail turns that into the claim.

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

# the first g, settled: x1
def ColGG.x1(+z: T.St) -> T.St:
  Vim.Vim.fit(Vim.Vim.keep(z, S.St.set_count(S.St.set_pend(z, T.PendG{}), 0n)))

# x1 has z's cursor
def ColGG.cur(+s: T.St, fin: Fi.Final(Mo.Idle.mk(s))) -> {S.Win.cur(S.St.win(ColGG.x1(Mo.Idle.mk(s)))) == S.Win.cur(S.St.win(Mo.Idle.mk(s))) : T.Pos}:
  (f3, r1) = fin
  (f12, r2) = r1
  (fl, r3) = r2
  (fc, r4) = r3
  +z = Mo.Idle.mk(s)
  +p = S.Win.cur(S.St.win(z))
  Equal.trans(T.Pos, S.Win.cur(S.St.win(ColGG.x1(z))), M.Move.clamp(C.St.lines(z), p), p, Mo.G1.cur(z), Cb.VCol.clamp_self(C.St.lines(z), p, fl, fc))

# gg from x1: a jump, then Win.go_line to the first line
def ColGG.core(+fs: List<&2, T.Buf>, +s: T.St, +hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, hr: {B.Tgt.real(S.St.files(s), S.Win.tgt(S.St.win(s))) == True{} : Bool}, +fin: Fi.Final(Mo.Idle.mk(s)))
  -> {Laws.Claim.vcol(fs, Mo.Idle.mk(s), Laws.Spec.press(ColGG.x1(Mo.Idle.mk(s)), "g")) == True{} : Bool}:
  +z = Mo.Idle.mk(s)
  +x1 = ColGG.x1(z)
  +ls = C.St.lines(x1)
  +l0 = C.St.line(x1)
  +w = S.Win.want(S.St.win(x1))
  +st = C.Win.go_line(C.Win.jump(S.St.set_count(S.St.set_pend(x1, T.NoPend{}), 0n)), 0n)
  +y = Vim.Vim.keep(x1, st)
  +t = Vim.Vim.fit(y)
  +ft = Fi.Final.of_fit(y)
  +ecx = ColGG.cur(s, fin)
  +elx = Cb.VCol.g1_lines(z)
  +eline = Equal.cong(T.Pos, Nat, q => S.Pos.line(q), S.Win.cur(S.St.win(x1)), S.Win.cur(S.St.win(z)), ecx)
  +ecol = Equal.cong(T.Pos, Nat, q => S.Pos.col(q), S.Win.cur(S.St.win(x1)), S.Win.cur(S.St.win(z)), ecx)
  +aimx = Mo.Aim.fit(Vim.Vim.keep(z, S.St.set_count(S.St.set_pend(z, T.PendG{}), 0n)))
  +e_c = Equal.trans(Nat, Laws.Spec.at_col(Vim.Vim.frame(z)), C.St.col(z), M.Move.aim(ls, l0, w), Mo.AtCol(z, fin), Equal.trans(Nat, C.St.col(z), C.St.col(x1), M.Move.aim(ls, l0, w), Equal.sym(Nat, C.St.col(x1), C.St.col(z), ecol), aimx))
  +e_l0 = Equal.trans(Nat, Laws.Spec.at_line(Vim.Vim.frame(z)), C.St.line(z), l0, Mo.AtLine(z, fin), Equal.sym(Nat, l0, C.St.line(z), eline))
  +e_ls1 = Equal.trans(List<&2, String>, Laws.Spec.lines(fs, z), C.St.lines(z), ls, Mo.Lines.spec(fs, z, hf), Equal.sym(List<&2, String>, ls, C.St.lines(z), elx))
  %Equal.sym(T.St, Laws.Spec.press(x1, "g"), t, Cb.VCol.press(x1, "g", st, {==}, hr, {==})) : {Laws.Claim.vcol(fs, z, _) == True{} : Bool}
  Cb.VCol.tail(fs, z, y, ls, l0, 0n, w, e_c, e_l0, e_ls1, Mo.GLJ.cur(x1, 0n), Cb.VCol.glj_lines(x1, 0n), Mo.Lines.spec(fs, t, hf), Mo.AtLine(t, ft), Mo.AtCol(t, ft))

# the first g only waits: it settles at x1
def ColGG.at(+fs: List<&2, T.Buf>, +s: T.St, +hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, +hr: {B.Tgt.real(S.St.files(s), S.Win.tgt(S.St.win(s))) == True{} : Bool}, +fin: Fi.Final(Mo.Idle.mk(s)))
  -> {Laws.Claim.vcol_gg(fs, Mo.Idle.mk(s)) == True{} : Bool}:
  +z = Mo.Idle.mk(s)
  +st1 = S.St.set_count(S.St.set_pend(z, T.PendG{}), 0n)
  %Equal.sym(T.St, Laws.Spec.press(z, "g"), ColGG.x1(z), Cb.VCol.press(z, "g", st1, {==}, hr, {==})) : {Laws.Claim.vcol(fs, z, Laws.Spec.press(_, "g")) == True{} : Bool}
  ColGG.core(fs, s, hf, hr, fin)

def ColGG.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.vcol_gg(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  %Equal.sym(T.St, n, Mo.Idle.mk(n), Mo.Ready.eta(fs, rows, cols, evs)) : {Laws.Claim.vcol_gg(fs, _) == True{} : Bool}
  ColGG.at(fs, n, Mo.Ready.files(fs, rows, cols, evs), Mo.Ready.real(fs, rows, cols, evs), Mo.Ready.fin(fs, rows, cols, evs))

def MotionLaws.col_gg(fs, rows, cols, evs):
  ColGG.law(fs, rows, cols, evs)
