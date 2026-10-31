# eukhe.com's Neovim: the proof of LAW cmdline_cursor
# ===================================================
#
# In normal mode the cursor is on a text row, never on the command line
# (the window is settled); while typing, the command line shows the end
# of what is typed (Scr.typed, at most cols - 1 cells, never empty) and
# the cursor right after it; a picker has a float. For every settled
# editor, so after any events.

import Base
import ../../vim/types.bend as T
import ../../vim/text.bend as X
import ../../vim/move.bend as M
import ../../vim/view.bend as V
import ../../vim/st.bend as S
import ../../vim/core.bend as C
import ../../vim/screen.bend as R
import ../../vim/vim.bend as Vim
import ../../LAWS.bend as Laws
import ../base.bend as L
import ../base/final.bend as Fi
import ../base/text.bend as Tx
import ../base/reach.bend as Re
import ./base.bend as Sc
import ./parts.bend as Pa
import ./frame.bend as Fr

# p is False: p implies anything
def Implies.no(p: Bool, -q: Bool, hp: {p == False{} : Bool}) -> {Laws.Spec.implies(p, q) == True{} : Bool}:
  match p:
    case True{}:
      L.Bool.true_false({Laws.Spec.implies(True{}, q) == True{} : Bool}, hp)
    case False{}:
      {==}

# a settled window: the cursor's row is above the command line
def Cmdline.row(+s: T.St, fin: Fi.Final(s)) -> {Nat.is_eq(Nat.sub(C.St.line(s), S.Win.top(S.St.win(s))), Nat.sub(S.St.rows(s), 1n)) == False{} : Bool}:
  (f3, r1) = fin
  (f12, r2) = r1
  (fl, r3) = r2
  (fc, r4) = r3
  (bt, bl) = r4
  (bth, btl) = bt
  +rows = S.St.rows(s)
  +h = Nat.sub(rows, 2n)
  +row = Nat.sub(C.St.line(s), S.Win.top(S.St.win(s)))
  +lt = Sc.Win.row_lt(C.St.line(s), V.View.so_in(h), M.Move.last_line(C.St.lines(s)), h, S.Win.top(S.St.win(s)), bth, L.Nat.sub_mono(3n, rows, 2n, f3))
  +le = L.Nat.sub_anti(rows, 1n, 2n, {==})
  L.Nat.lt_ne(row, Nat.sub(rows, 1n), L.Nat.le_lt(row, Nat.sub(rows, 1n), L.Nat.le_trans(1n+row, h, Nat.sub(rows, 1n), L.Nat.lt_le(row, h, lt), le)))

def Cmdline.of(+s: T.St, +fin: Fi.Final(s)) -> {Laws.Spec.on_cmdline(s, S.St.rows(s), S.St.cols(s)) == True{} : Bool}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match mode:
        case T.Normal{}:
          +s0 = {T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Normal{}, count, pend, find, hl, opts, rows, cols, msg, stat} : T.St}
          +f = Vim.Vim.frame(s0)
          Implies.no(Bool.and(Laws.Spec.is_none(Laws.F.float(f)), Nat.is_eq(Laws.F.row(f), Nat.sub(rows, 1n))), Bool.and(Nat.is_eq(Laws.F.col(f), Laws.Spec.cells(Laws.F.cmd(f))), Bool.and(Nat.is_lt(Laws.F.col(f), cols), Bool.not(String.is_empty(Laws.F.cmd(f))))), Cmdline.row(s0, fin))
        case T.Typing{+kind, +text}:
          +s0 = {T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Typing{kind, text}, count, pend, find, hl, opts, rows, cols, msg, stat} : T.St}
          +f = Vim.Vim.frame(s0)
          +line = R.Scr.prefix(kind) ++ text
          +t = R.Scr.typed(line, cols)
          +p = Bool.and(Laws.Spec.is_none(Laws.F.float(f)), Nat.is_eq(Laws.F.row(f), Nat.sub(rows, 1n)))
          +c12 = Fr.Fr.cols(s0, fin)
          +hk = L.Nat.sub_mono(2n, cols, 1n, L.Nat.le_trans(2n, 12n, cols, {==}, c12))
          L.Or.r(Bool.not(p), Bool.and(Nat.is_eq(Laws.F.col(f), Laws.Spec.cells(Laws.F.cmd(f))), Bool.and(Nat.is_lt(Laws.F.col(f), cols), Bool.not(String.is_empty(Laws.F.cmd(f))))),
            Sc.And3(Nat.is_eq(X.Text.cells(t), Laws.Spec.cells(t)), Nat.is_lt(X.Text.cells(t), cols), Bool.not(String.is_empty(t)),
              Pa.Eq.of(X.Text.cells(t), Laws.Spec.cells(t), Tx.Cells.eq(t)), Pa.Typed.lt(line, cols, Fr.Fr.cols1(s0, fin)), L.Not.of(String.is_empty(t), Pa.Typed.some(line, cols, Pa.Prefix.cells(kind, text), hk))))
        case T.Picking{+kind, +q, +its, +n, +sel, +top, +pv, +levels}:
          {==}

def Cmdline.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Spec.on_cmdline(Laws.Spec.run(fs, rows, cols, evs), Laws.Spec.rows(rows, evs), Laws.Spec.cols(cols, evs)) == True{} : Bool}:
  +s = Laws.Spec.run(fs, rows, cols, evs)
  %Re.Reach.rows_run(fs, rows, cols, evs) : {Laws.Spec.on_cmdline(s, _, Laws.Spec.cols(cols, evs)) == True{} : Bool}
  %Re.Reach.cols_run(fs, rows, cols, evs) : {Laws.Spec.on_cmdline(s, S.St.rows(s), _) == True{} : Bool}
  Cmdline.of(s, Re.Reach.final(fs, rows, cols, evs))

def Laws.cmdline_cursor(fs, rows, cols, evs):
  Cmdline.law(fs, rows, cols, evs)
