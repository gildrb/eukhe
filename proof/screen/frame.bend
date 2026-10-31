# eukhe.com's Neovim: the frame of a settled editor, by mode
# ==========================================================
#
# What Vim.frame shows of an editor s with Final(s), case by case on its
# mode (normal, typing a command, a picker): the gutter left of the last
# column, the statusline cols cells, the float fitted, the command line
# within the screen, the cursorline exactly when no float is open.

import Base
import ../../vim/types.bend as T
import ../../vim/text.bend as X
import ../../vim/buf.bend as B
import ../../vim/view.bend as V
import ../../vim/st.bend as S
import ../../vim/core.bend as C
import ../../vim/pick.bend as P
import ../../vim/screen.bend as R
import ../../vim/vim.bend as Vim
import ../../LAWS.bend as Laws
import ../base.bend as L
import ../base/final.bend as Fi
import ../base/text.bend as Tx
import ./base.bend as Sc
import ./parts.bend as Pa

# the screen of a settled editor: at least 3 rows, at least 12 columns
def Fr.rows(+s: T.St, fin: Fi.Final(s)) -> L.LE(3n, S.St.rows(s)):
  (f3, r1) = fin
  f3

def Fr.cols(+s: T.St, fin: Fi.Final(s)) -> L.LE(12n, S.St.cols(s)):
  (f3, r1) = fin
  (f12, r2) = r1
  f12

def Fr.cols1(+s: T.St, fin: Fi.Final(s)) -> L.LE(1n, S.St.cols(s)):
  L.Nat.le_trans(1n, 12n, S.St.cols(s), {==}, Fr.cols(s, fin))

def Fr.rows1(+s: T.St, fin: Fi.Final(s)) -> L.LE(1n, S.St.rows(s)):
  L.Nat.le_trans(1n, 3n, S.St.rows(s), {==}, Fr.rows(s, fin))

# the gutter: left of the last column
def Gut.ok(+s: T.St, fin: Fi.Final(s)) -> L.LT(C.St.g(s), S.St.cols(s)):
  Sc.Nat.le_pred_lt(C.St.g(s), S.St.cols(s), Sc.Gut.le(S.St.opts(s), B.Lines.len(C.St.lines(s)), C.St.on_file(s), S.St.cols(s)), Fr.cols1(s, fin))

def Gut.le_cols(+s: T.St, fin: Fi.Final(s)) -> L.LE(C.St.g(s), S.St.cols(s)):
  L.Nat.lt_to_le(C.St.g(s), S.St.cols(s), Gut.ok(s, fin))

# the statusline: cols cells, in every mode
def Status.ok(+s: T.St) -> {Nat.is_eq(Laws.Spec.cells(Laws.F.status(Vim.Vim.frame(s))), S.St.cols(s)) == True{} : Bool}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match mode:
        case T.Normal{}:
          +s0 = {T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Normal{}, count, pend, find, hl, opts, rows, cols, msg, stat} : T.St}
          Pa.Eq.of(Laws.Spec.cells(Laws.F.status(Vim.Vim.frame(s0))), cols, Pa.Status.cells(B.Tgt.name(files, S.Win.tgt(win)), "", R.Scr.ruler(s0), cols))
        case T.Typing{+kind, +text}:
          +s0 = {T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Typing{kind, text}, count, pend, find, hl, opts, rows, cols, msg, stat} : T.St}
          Pa.Eq.of(Laws.Spec.cells(Laws.F.status(Vim.Vim.frame(s0))), cols, Pa.Status.cells(B.Tgt.name(files, S.Win.tgt(win)), "", R.Scr.ruler(s0), cols))
        case T.Picking{+kind, +q, +its, +n, +sel, +top, +pv, +levels}:
          +s0 = {T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Picking{kind, q, its, n, sel, top, pv, levels}, count, pend, find, hl, opts, rows, cols, msg, stat} : T.St}
          +fff = P.Pick.is_fff(kind)
          +bytes = X.Text.bytes(q, X.Text.len(q))
          Pa.Eq.of(Laws.Spec.cells(Laws.F.status(Vim.Vim.frame(s0))), cols, Pa.Status.cells(Bool.pick(String, fff, "fffile search", "term:////1:/bin/sh"), Bool.pick(String, fff, "", "[-]"), "1:" ++ Nat.show(Nat.add(Bool.pick(Nat, fff, 6n, 3n), bytes)), cols))

# the float: none, or a picker's, fitted to the screen
def Float.ok(+s: T.St, +fin: Fi.Final(s)) -> {Laws.Spec.float_ok(Laws.F.float(Vim.Vim.frame(s)), S.St.rows(s), S.St.cols(s)) == True{} : Bool}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match mode:
        case T.Normal{}:
          {==}
        case T.Typing{+kind, +text}:
          {==}
        case T.Picking{+kind, +q, +its, +n, +sel, +top, +pv, +levels}:
          +s0 = {T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Picking{kind, q, its, n, sel, top, pv, levels}, count, pend, find, hl, opts, rows, cols, msg, stat} : T.St}
          Pa.FloatFit.ok(P.Pick.draw(s0, kind, q, its, n, sel, pv), rows, cols, Fr.rows1(s0, fin), Fr.cols1(s0, fin))

# the command line: within the screen
def Cmd.ok(+s: T.St, fin: Fi.Final(s)) -> {Nat.is_le(Laws.Spec.cells(Laws.F.cmd(Vim.Vim.frame(s))), S.St.cols(s)) == True{} : Bool}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match mode:
        case T.Normal{}:
          +s0 = {T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Normal{}, count, pend, find, hl, opts, rows, cols, msg, stat} : T.St}
          Tx.Cut.cells(R.Scr.msg(s0), cols)
        case T.Typing{+kind, +text}:
          +line = R.Scr.prefix(kind) ++ text
          L.Nat.le_trans(Laws.Spec.cells(R.Scr.typed(line, cols)), Nat.sub(cols, 1n), cols, Pa.Typed.le(line, cols), L.Nat.sub_le(cols, 1n))
        case T.Picking{+kind, +q, +its, +n, +sel, +top, +pv, +levels}:
          +s0 = {T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Picking{kind, q, its, n, sel, top, pv, levels}, count, pend, find, hl, opts, rows, cols, msg, stat} : T.St}
          Tx.Cut.cells(R.Scr.msg(s0), cols)

# the cursorline: shown exactly when no float is open
def Line.ok(+s: T.St) -> {Bool.not(Bool.xor(Laws.F.cl(Vim.Vim.frame(s)), Laws.Spec.is_none(Laws.F.float(Vim.Vim.frame(s))))) == True{} : Bool}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match mode:
        case T.Normal{}:
          {==}
        case T.Typing{+kind, +text}:
          {==}
        case T.Picking{+kind, +q, +its, +n, +sel, +top, +pv, +levels}:
          {==}
