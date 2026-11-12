# eukhe.com's Neovim: the proof of LAW cursor_ok
# ==============================================
#
# In normal mode the cursor is on the text (Screen.on_text); while typing
# it is on the command line, on screen (Typed.lt); in a picker Scr.inside
# keeps it in the float, which Float.fit keeps at least one cell tall and
# wide (CursorIn.pick). For every settled editor on the files the start
# made of fs, so after any events.

import Base
import ../../../vim/types.bend as T
import ../../../vim/buf.bend as B
import ../../../vim/st.bend as S
import ../../../vim/pick.bend as P
import ../../../vim/screen.bend as R
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/screen.bend as ScreenLaws
import ../../base.bend as L
import ../../base/final.bend as Fi
import ../../base/reach.bend as Re
import ./base.bend as Sc
import ./parts.bend as Pa
import ./frame.bend as Fr

def CursorOk.of(+fs: List<&2, T.Buf>, +s: T.St, +fin: Fi.Final(s), hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}) -> {Laws.Spec.cursor_ok(fs, s, S.St.rows(s), S.St.cols(s)) == True{} : Bool}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match mode:
        case T.Normal{}:
          +s0 = {T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Normal{}, count, pend, find, hl, opts, rows, cols, msg, stat} : T.St}
          +f = Vim.Vim.frame(s0)
          L.Or.r(Bool.and(Nat.is_eq(Laws.F.row(f), Nat.sub(rows, 1n)), Nat.is_lt(Laws.F.col(f), cols)), Laws.Spec.on_text(fs, s0, rows, cols), Sc.Screen.on_text(fs, s0, fin, hf, {==}))
        case T.Typing{+kind, +text}:
          +s0 = {T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Typing{kind, text}, count, pend, find, hl, opts, rows, cols, msg, stat} : T.St}
          +f = Vim.Vim.frame(s0)
          +line = R.Scr.prefix(kind) ++ text
          L.Or.l(Bool.and(Nat.is_eq(Laws.F.row(f), Nat.sub(rows, 1n)), Nat.is_lt(Laws.F.col(f), cols)), Laws.Spec.on_text(fs, s0, rows, cols),
            L.And.intro(Nat.is_eq(Nat.sub(rows, 1n), Nat.sub(rows, 1n)), Nat.is_lt(Laws.F.col(f), cols), L.Nat.eq_refl(Nat.sub(rows, 1n)), Pa.Typed.lt(line, cols, Fr.Fr.cols1(s0, fin))))
        case T.Picking{+kind, +q, +its, +n, +sel, +top, +pv, +levels}:
          +m = {T.Picking{kind, q, its, n, sel, top, pv, levels} : T.Mode}
          +s0 = {T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, m, count, pend, find, hl, opts, rows, cols, msg, stat} : T.St}
          +f = Vim.Vim.frame(s0)
          Pa.CursorIn.pick(fs, s0, Laws.F.tgt(f), Laws.F.top(f), Laws.F.left(f), Laws.F.gutter(f), Laws.F.nums(f), R.Scr.cell(s0, m), Laws.F.char(f), Laws.F.cmd(f), Laws.F.hits(f), Laws.F.bar(f), Laws.F.cl(f), Laws.F.status(f), P.Pick.draw(s0, kind, q, its, n, sel, pv), rows, cols, Fr.Fr.rows1(s0, fin), Fr.Fr.cols1(s0, fin))

def CursorOk.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Spec.cursor_ok(fs, Laws.Spec.run(fs, rows, cols, evs), Laws.Spec.rows(rows, evs), Laws.Spec.cols(cols, evs)) == True{} : Bool}:
  +s = Laws.Spec.run(fs, rows, cols, evs)
  %Re.Reach.rows_run(fs, rows, cols, evs) : {Laws.Spec.cursor_ok(fs, s, _, Laws.Spec.cols(cols, evs)) == True{} : Bool}
  %Re.Reach.cols_run(fs, rows, cols, evs) : {Laws.Spec.cursor_ok(fs, s, S.St.rows(s), _) == True{} : Bool}
  CursorOk.of(fs, s, Re.Reach.final(fs, rows, cols, evs), Re.Reach.files_run(fs, rows, cols, evs))

def ScreenLaws.cursor_ok(fs, rows, cols, evs):
  CursorOk.law(fs, rows, cols, evs)
