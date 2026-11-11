# eukhe.com's Neovim: the proof of LAW scrolloff_any
# ==================================================
#
# After any events: in normal mode the window is settled and 'scrolloff'
# holds (Screen.scrolled); while typing the cursor is on the command line,
# below the text rows; a picker has a float. Nothing is claimed for those.

import Base
import ../../../vim/types.bend as T
import ../../../vim/buf.bend as B
import ../../../vim/st.bend as S
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/screen.bend as ScreenLaws
import ../../base.bend as L
import ../../base/final.bend as Fi
import ../../base/reach.bend as Re
import ./base.bend as Sc

def Any.of(+fs: List<&2, T.Buf>, +s: T.St, +fin: Fi.Final(s), hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}) -> {Laws.Spec.scrolled_any(fs, s, S.St.rows(s)) == True{} : Bool}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match mode:
        case T.Normal{}:
          +s0 = {T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Normal{}, count, pend, find, hl, opts, rows, cols, msg, stat} : T.St}
          +f = Vim.Vim.frame(s0)
          +p = Bool.and(Laws.Spec.is_none(Laws.F.float(f)), Nat.is_lt(Laws.F.row(f), Nat.sub(rows, 2n)))
          L.Or.r(Bool.not(p), Laws.Spec.scrolled(fs, s0, rows), Sc.Screen.scrolled(fs, s0, fin, hf, {==}))
        case T.Typing{+kind, +text}:
          +s0 = {T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Typing{kind, text}, count, pend, find, hl, opts, rows, cols, msg, stat} : T.St}
          +f = Vim.Vim.frame(s0)
          +p = Bool.and(Laws.Spec.is_none(Laws.F.float(f)), Nat.is_lt(Laws.F.row(f), Nat.sub(rows, 2n)))
          L.Or.l(Bool.not(p), Laws.Spec.scrolled(fs, s0, rows), L.Not.of(p, L.Nat.le_not_lt(Nat.sub(rows, 1n), Nat.sub(rows, 2n), L.Nat.sub_anti(rows, 1n, 2n, {==}))))
        case T.Picking{+kind, +q, +its, +n, +sel, +top, +pv, +levels}:
          {==}

def Any.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Spec.scrolled_any(fs, Laws.Spec.run(fs, rows, cols, evs), Laws.Spec.rows(rows, evs)) == True{} : Bool}:
  +s = Laws.Spec.run(fs, rows, cols, evs)
  %Re.Reach.rows_run(fs, rows, cols, evs) : {Laws.Spec.scrolled_any(fs, s, _) == True{} : Bool}
  Any.of(fs, s, Re.Reach.final(fs, rows, cols, evs), Re.Reach.files_run(fs, rows, cols, evs))

def ScreenLaws.scrolloff_any(fs, rows, cols, evs):
  Any.law(fs, rows, cols, evs)
