# eukhe.com's Neovim: the proof of LAW fits
# =========================================
#
# The editor after any events is settled (Reach.final) on the screen the
# events asked for (Reach.rows_run, Reach.cols_run); each part of its frame
# fits that screen (proof/screen/parts.bend, frame.bend).

import Base
import ../../../vim/types.bend as T
import ../../../vim/buf.bend as B
import ../../../vim/view.bend as V
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../vim/screen.bend as R
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/screen.bend as ScreenLaws
import ../../base/final.bend as Fi
import ../../base/reach.bend as Re
import ./base.bend as Sc
import ./parts.bend as Pa
import ./frame.bend as Fr

# a settled editor's screen fits rows(s) x cols(s)
def Fits.of(+s: T.St, +fin: Fi.Final(s)) -> {Laws.Spec.fits(s, S.St.rows(s), S.St.cols(s)) == True{} : Bool}:
  +f = Vim.Vim.frame(s)
  +rows = S.St.rows(s)
  +cols = S.St.cols(s)
  +h = Nat.sub(rows, 2n)
  +g = Laws.F.gutter(f)
  +w = S.St.win(s)
  +n = B.Lines.len(C.St.lines(s))
  +o = S.St.opts(s)
  Sc.And7(Nat.is_lt(g, cols), Nat.is_eq(Laws.Spec.count(Laws.F.nums(f)), h), Laws.Spec.all_cells(Laws.F.nums(f), g), Nat.is_eq(Laws.Spec.cells(Laws.F.status(f)), cols), Laws.Spec.spans_in(Laws.F.hits(f), h, g, cols), Laws.Spec.bar_ok(Laws.F.bar(f), h), Laws.Spec.float_ok(Laws.F.float(f), rows, cols),
    Fr.Gut.ok(s, fin),
    Pa.Nums.ok_count(C.St.h(s), o, S.Win.top(w), C.St.line(s), Nat.sub(n, 1n), V.View.numw(o, n), C.St.on_file(s), C.St.g(s)),
    Pa.Nums.ok_cells(C.St.h(s), o, S.Win.top(w), C.St.line(s), Nat.sub(n, 1n), V.View.numw(o, n), C.St.on_file(s), C.St.g(s)),
    Fr.Status.ok(s),
    Pa.Hits.ok(s, R.Scr.lit(s, S.St.mode(s)), Fr.Gut.le_cols(s, fin)),
    Pa.Bar.ok(n, C.St.h(s), S.Win.top(w), Nat.sub(cols, 1n)),
    Fr.Float.ok(s, fin))

def Fits.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Spec.fits(Laws.Spec.run(fs, rows, cols, evs), Laws.Spec.rows(rows, evs), Laws.Spec.cols(cols, evs)) == True{} : Bool}:
  +s = Laws.Spec.run(fs, rows, cols, evs)
  %Re.Reach.rows_run(fs, rows, cols, evs) : {Laws.Spec.fits(s, _, Laws.Spec.cols(cols, evs)) == True{} : Bool}
  %Re.Reach.cols_run(fs, rows, cols, evs) : {Laws.Spec.fits(s, S.St.rows(s), _) == True{} : Bool}
  Fits.of(s, Re.Reach.final(fs, rows, cols, evs))

def ScreenLaws.fits(fs, rows, cols, evs):
  Fits.law(fs, rows, cols, evs)
