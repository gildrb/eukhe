# eukhe.com's Neovim: the proof of LAW edges
# ==========================================
#
# The scrollbar is drawn in the last column (View.bar), the command line
# is cut to the screen or shows a typed command's end (Scr.cmd), and the
# cursorline is on exactly when no picker is open (Scr.cl): for every
# settled editor, so after any events.

import Base
import ../../../vim/types.bend as T
import ../../../vim/buf.bend as B
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/screen.bend as ScreenLaws
import ../../base/final.bend as Fi
import ../../base/reach.bend as Re
import ./base.bend as Sc
import ./parts.bend as Pa
import ./frame.bend as Fr

def Edges.of(+s: T.St, +fin: Fi.Final(s)) -> {Laws.Spec.edges(s, S.St.cols(s)) == True{} : Bool}:
  +f = Vim.Vim.frame(s)
  +cols = S.St.cols(s)
  +n = B.Lines.len(C.St.lines(s))
  Sc.And3(Nat.is_eq(Laws.Spec.bar_col(Laws.F.bar(f)), Nat.sub(cols, 1n)), Nat.is_le(Laws.Spec.cells(Laws.F.cmd(f)), cols), Bool.not(Bool.xor(Laws.F.cl(f), Laws.Spec.is_none(Laws.F.float(f)))),
    Pa.Bar.col(n, C.St.h(s), S.Win.top(S.St.win(s)), Nat.sub(cols, 1n)), Fr.Cmd.ok(s, fin), Fr.Line.ok(s))

def Edges.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Spec.edges(Laws.Spec.run(fs, rows, cols, evs), Laws.Spec.cols(cols, evs)) == True{} : Bool}:
  +s = Laws.Spec.run(fs, rows, cols, evs)
  %Re.Reach.cols_run(fs, rows, cols, evs) : {Laws.Spec.edges(s, _) == True{} : Bool}
  Edges.of(s, Re.Reach.final(fs, rows, cols, evs))

def ScreenLaws.edges(fs, rows, cols, evs):
  Edges.law(fs, rows, cols, evs)
