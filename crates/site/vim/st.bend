# eukhe.com's Neovim: the editor's fields
# ======================================
#
# St's fields (types.bend), one by one, and the window's and a position's.

import Base
import ./types.bend as T

# St's fields
# -----------

def St.files(s: T.St) -> List<&2, T.Buf>:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      files

def St.folded(s: T.St) -> List<&2, List<&2, String>>:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      folded

def St.dirs(s: T.St) -> List<&2, T.Listing>:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      dirs

def St.win(s: T.St) -> T.Win:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      win

def St.marks(s: T.St) -> List<&2, T.Pos>:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      marks

def St.spots(s: T.St) -> List<&2, T.Spot>:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      spots

def St.opened(s: T.St) -> List<&2, Nat>:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      opened

def St.bufs(s: T.St) -> List<&2, Nat>:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      bufs

def St.back(s: T.St) -> List<&2, T.Win>:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      back

def St.fwd(s: T.St) -> List<&2, T.Win>:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      fwd

def St.mode(s: T.St) -> T.Mode:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      mode

def St.count(s: T.St) -> Nat:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      count

def St.pend(s: T.St) -> T.Pend:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      pend

def St.find(s: T.St) -> Maybe<&2, T.Find>:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      find

def St.hl(s: T.St) -> Bool:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      hl

def St.opts(s: T.St) -> T.Opts:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      opts

def St.rows(s: T.St) -> Nat:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      rows

def St.cols(s: T.St) -> Nat:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      cols

def St.msg(s: T.St) -> String:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      msg

def St.stat(s: T.St) -> String:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      stat

def St.set_files(s: T.St, x: List<&2, T.Buf>) -> T.St:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      T.St{x, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}

def St.set_folded(s: T.St, x: List<&2, List<&2, String>>) -> T.St:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      T.St{files, x, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}

def St.set_dirs(s: T.St, x: List<&2, T.Listing>) -> T.St:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      T.St{files, folded, x, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}

def St.set_win(s: T.St, x: T.Win) -> T.St:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      T.St{files, folded, dirs, x, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}

def St.set_marks(s: T.St, x: List<&2, T.Pos>) -> T.St:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      T.St{files, folded, dirs, win, x, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}

def St.set_spots(s: T.St, x: List<&2, T.Spot>) -> T.St:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      T.St{files, folded, dirs, win, marks, x, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}

def St.set_opened(s: T.St, x: List<&2, Nat>) -> T.St:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      T.St{files, folded, dirs, win, marks, spots, x, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}

def St.set_bufs(s: T.St, x: List<&2, Nat>) -> T.St:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      T.St{files, folded, dirs, win, marks, spots, opened, x, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}

def St.set_back(s: T.St, x: List<&2, T.Win>) -> T.St:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      T.St{files, folded, dirs, win, marks, spots, opened, bufs, x, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}

def St.set_fwd(s: T.St, x: List<&2, T.Win>) -> T.St:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, x, mode, count, pend, find, hl, opts, rows, cols, msg, stat}

def St.set_mode(s: T.St, x: T.Mode) -> T.St:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, x, count, pend, find, hl, opts, rows, cols, msg, stat}

def St.set_count(s: T.St, x: Nat) -> T.St:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, x, pend, find, hl, opts, rows, cols, msg, stat}

def St.set_pend(s: T.St, x: T.Pend) -> T.St:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, x, find, hl, opts, rows, cols, msg, stat}

def St.set_find(s: T.St, x: Maybe<&2, T.Find>) -> T.St:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, x, hl, opts, rows, cols, msg, stat}

def St.set_hl(s: T.St, x: Bool) -> T.St:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, x, opts, rows, cols, msg, stat}

def St.set_opts(s: T.St, x: T.Opts) -> T.St:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, x, rows, cols, msg, stat}

def St.set_rows(s: T.St, x: Nat) -> T.St:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, x, cols, msg, stat}

def St.set_cols(s: T.St, x: Nat) -> T.St:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, x, msg, stat}

def St.set_msg(s: T.St, x: String) -> T.St:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, x, stat}

def St.set_stat(s: T.St, x: String) -> T.St:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, x}
# Win's fields
# ------------

def Win.tgt(w: T.Win) -> T.Tgt:
  match w:
    case T.Win{tgt, cur, want, top, left}:
      tgt

def Win.cur(w: T.Win) -> T.Pos:
  match w:
    case T.Win{tgt, cur, want, top, left}:
      cur

def Win.want(w: T.Win) -> T.Want:
  match w:
    case T.Win{tgt, cur, want, top, left}:
      want

def Win.top(w: T.Win) -> Nat:
  match w:
    case T.Win{tgt, cur, want, top, left}:
      top

def Win.left(w: T.Win) -> Nat:
  match w:
    case T.Win{tgt, cur, want, top, left}:
      left

# Positions
# ---------

def Pos.line(p: T.Pos) -> Nat:
  match p:
    case T.Pos{line, col}:
      line

def Pos.col(p: T.Pos) -> Nat:
  match p:
    case T.Pos{line, col}:
      col

def Pos.eq(a: T.Pos, b: T.Pos) -> Bool:
  match a b:
    case T.Pos{l1, c1} T.Pos{l2, c2}:
      Bool.and(Nat.is_eq(l1, l2), Nat.is_eq(c1, c2))
