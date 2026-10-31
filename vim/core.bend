# eukhe.com's Neovim: the window
# ==============================
#
# The window over a buffer: where the cursor may go and how the window
# scrolls to it, jumps (Ctrl-o, Ctrl-i), buffers opened, and Oil's folder
# listings. Every change of the cursor goes through Win.settle, which
# pulls it onto the text and scrolls the window to it.

import Base
import ./types.bend as T
import ./text.bend as X
import ./buf.bend as B
import ./move.bend as M
import ./view.bend as V
import ./st.bend as S

# the jumps Ctrl-o goes back through ('jumplist' holds 100)
def Win.max_jumps() -> Nat:
  100n

# The window
# ----------

def Listing.find(xs: List<&2, T.Listing>, +path: String) -> Maybe<&2, List<&2, String>>:
  match xs:
    case Nil{}:
      None{}
    case Con{T.Listing{p, +ls}, t}:
      X.Bool.when(Maybe<&2, List<&2, String>>, String.eq(p, path), u => Listing.find(t, path), u => Some{ls})

def St.lines.at(+s: T.St, t: T.Tgt) -> List<&2, String>:
  match t:
    case T.File{i}:
      B.Buf.lines(B.Files.at(S.St.files(s), i))
    case T.Dir{+path}:
      Maybe.default(&2, List<&2, String>, Listing.find(S.St.dirs(s), path), ["../"])

# the lines the window shows (folders' listings are found at the start),
# at least one
def St.lines(+s: T.St) -> List<&2, String>:
  B.Lines.some(St.lines.at(s, S.Win.tgt(S.St.win(s))))

def Fold.lines(ls: List<&2, String>, +acc: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      List.reverse(&2, String, acc)
    case Con{h, t}:
      Fold.lines(t, X.Text.fold(h) <> acc)

def St.folds.at(+s: T.St, t: T.Tgt) -> List<&2, String>:
  match t:
    case T.File{i}:
      Maybe.default(&2, List<&2, String>, List.get(&2, List<&2, String>, S.St.folded(s), i), Nil{})
    case T.Dir{path}:
      Fold.lines(St.lines(s), Nil{})

# the window's lines in lower case (searches fold case on these; files'
# are folded once, at the start)
def St.folds(+s: T.St) -> List<&2, String>:
  St.folds.at(s, S.Win.tgt(S.St.win(s)))

# whether target t is a file (not a folder's listing)
def Tgt.is_file(t: T.Tgt) -> Bool:
  match t:
    case T.File{i}:
      True{}
    case T.Dir{path}:
      False{}

# whether the window shows a file: file windows have a sign column
def St.on_file(+s: T.St) -> Bool:
  Tgt.is_file(S.Win.tgt(S.St.win(s)))

# the text rows, the gutter and the text columns of the screen
def St.h(+s: T.St) -> Nat:
  V.View.text_rows(S.St.rows(s))

def St.g(+s: T.St) -> Nat:
  V.View.gutter(S.St.opts(s), B.Lines.len(St.lines(s)), St.on_file(s), S.St.cols(s))

def St.w(+s: T.St) -> Nat:
  V.View.text_cols(S.St.cols(s), St.g(s))

def St.line(+s: T.St) -> Nat:
  S.Pos.line(S.Win.cur(S.St.win(s)))

def St.col(+s: T.St) -> Nat:
  S.Pos.col(S.Win.cur(S.St.win(s)))

# the cursor's line
def St.text(+s: T.St) -> String:
  B.Lines.at(St.lines(s), St.line(s))

# the editor with the cursor pulled onto the text and the window scrolled
# to it: the one way a cursor reaches the screen
def Win.settle(+s: T.St) -> T.St:
  +ls = St.lines(s)
  +w = S.St.win(s)
  +p = M.Move.clamp(ls, S.Win.cur(w))
  +h = St.h(s)
  +last = M.Move.last_line(ls)
  +top = V.View.fit(Nat.min(S.Win.top(w), V.View.max_top(h, last)), S.Pos.line(p), h, last)
  +left = V.View.fit_side(S.Win.left(w), S.Pos.col(p), St.w(s), M.Move.last_col(ls, S.Pos.line(p)))
  S.St.set_win(s, T.Win{S.Win.tgt(w), p, S.Win.want(w), top, left})

# the cursor to p; the column j and k aim for follows it unless keep
def Win.go(+s: T.St, p: T.Pos, +keep: Bool) -> T.St:
  +ls = St.lines(s)
  +w = S.St.win(s)
  +q = M.Move.clamp(ls, p)
  +want = Bool.pick(T.Want, keep, S.Win.want(w), T.Col{S.Pos.col(q)})
  Win.settle(S.St.set_win(s, T.Win{S.Win.tgt(w), q, want, S.Win.top(w), S.Win.left(w)}))

# the cursor to line l, at the column it aims for (j k G gg; 'nostartofline')
def Win.go_line(+s: T.St, +l: Nat) -> T.St:
  +ls = St.lines(s)
  +l2 = Nat.min(l, M.Move.last_line(ls))
  Win.go(s, T.Pos{l2, M.Move.aim(ls, l2, S.Win.want(S.St.win(s)))}, True{})

# the window's first line to top, the cursor dragged along to stay
# 'scrolloff' lines inside (Ctrl-e, Ctrl-y, Ctrl-d, the wheel)
def Win.scroll(+s: T.St, +top: Nat, +l: Nat) -> T.St:
  +ls = St.lines(s)
  +h = St.h(s)
  +last = M.Move.last_line(ls)
  +t = Nat.min(top, V.View.max_top(h, last))
  +l2 = V.View.drag(Nat.min(l, last), t, h, last)
  +w = S.St.win(s)
  Win.settle(S.St.set_win(s, T.Win{S.Win.tgt(w), T.Pos{l2, M.Move.aim(ls, l2, S.Win.want(w))}, S.Win.want(w), t, S.Win.left(w)}))

# Jumps and buffers
# -----------------

# the window remembered before a jump (Ctrl-o comes back to it)
def Win.jump(+s: T.St) -> T.St:
  S.St.set_fwd(S.St.set_back(s, List.take(&2, T.Win, S.St.win(s) <> S.St.back(s), Win.max_jumps())), Nil{})

def Spots.drop(xs: List<&2, T.Spot>, +path: String, +acc: List<&2, T.Spot>) -> List<&2, T.Spot>:
  match xs:
    case Nil{}:
      List.reverse(&2, T.Spot, acc)
    case Con{T.Spot{+p, +q}, t}:
      Spots.drop(t, path, Bool.pick(List<&2, T.Spot>, String.eq(p, path), acc, T.Spot{p, q} <> acc))

# where folder path's listing was left
def Spots.get(xs: List<&2, T.Spot>, +path: String) -> Maybe<&2, T.Pos>:
  match xs:
    case Nil{}:
      None{}
    case Con{T.Spot{p, +q}, t}:
      X.Bool.when(Maybe<&2, T.Pos>, String.eq(p, path), u => Spots.get(t, path), u => Some{q})

def Win.leave.at(+s: T.St, t: T.Tgt) -> T.St:
  match t:
    case T.File{i}:
      S.St.set_marks(s, List.set(&2, T.Pos, S.St.marks(s), i, S.Win.cur(S.St.win(s))))
    case T.Dir{+path}:
      S.St.set_spots(s, T.Spot{path, S.Win.cur(S.St.win(s))} <> Spots.drop(S.St.spots(s), path, Nil{}))

# the cursor of the buffer the window leaves, kept for its return
def Win.leave(+s: T.St) -> T.St:
  Win.leave.at(s, S.Win.tgt(S.St.win(s)))

def Opened.drop(os: List<&2, Nat>, +i: Nat, +acc: List<&2, Nat>) -> List<&2, Nat>:
  match os:
    case Nil{}:
      List.reverse(&2, Nat, acc)
    case Con{+h, t}:
      Opened.drop(t, i, Bool.pick(List<&2, Nat>, Nat.is_eq(h, i), acc, h <> acc))

# the files opened, most recent first
def Opened.put(os: List<&2, Nat>, t: T.Tgt) -> List<&2, Nat>:
  match t:
    case T.File{+i}:
      i <> Opened.drop(os, i, Nil{})
    case T.Dir{path}:
      os

def Bufs.has(bs: List<&2, Nat>, +i: Nat) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{+h, t}:
      Bool.or(Nat.is_eq(h, i), Bufs.has(t, i))

# the files in the order they were first opened: buffer i + 1 is file
# number i of the list
def Bufs.put(+bs: List<&2, Nat>, t: T.Tgt) -> List<&2, Nat>:
  match t:
    case T.File{+i}:
      Bool.pick(List<&2, Nat>, Bufs.has(bs, i), bs, List.append(&2, Nat, bs, [i]))
    case T.Dir{path}:
      bs

# the first line of a window over ls with line l in its middle (a jump far
# away), less where that would show rows past the end
def Win.center(+ls: List<&2, String>, +l: Nat, +h: Nat) -> Nat:
  +last = M.Move.last_line(ls)
  Nat.min(Nat.sub(l, Nat.div(Nat.sub(h, 1n), 2n)), Nat.sub(last, Nat.min(last, Nat.sub(h, 1n))))

# the window showing target t with the cursor at p: a jump
def Win.open(+s: T.St, +t: T.Tgt, p: T.Pos) -> T.St:
  +s2 = Win.leave(Win.jump(s))
  +s3 = S.St.set_bufs(S.St.set_opened(s2, Opened.put(S.St.opened(s2), t)), Bufs.put(S.St.bufs(s2), t))
  +ls = St.lines.at(s3, t)
  +q = M.Move.clamp(ls, p)
  Win.settle(S.St.set_win(s3, T.Win{t, q, T.Col{S.Pos.col(q)}, Win.center(ls, S.Pos.line(q), St.h(s3)), 0n}))

# file i where its cursor was left
def Win.open_file(+s: T.St, +i: Nat) -> T.St:
  Win.open(s, T.File{i}, Maybe.default(&2, T.Pos, List.get(&2, T.Pos, S.St.marks(s), i), T.Pos{0n, 0n}))

def Win.to(+s: T.St, m: Maybe<&2, Nat>) -> T.St:
  match m:
    case None{}:
      s
    case Some{i}:
      Win.open_file(s, i)

# Ctrl-^ (and Oil's Ctrl-c): the file shown before this one; from Oil, the
# file it was opened from
def Win.alt(+s: T.St) -> T.St:
  Win.to(s, List.head(&2, Nat, List.drop(&2, Nat, S.St.opened(s), Bool.pick(Nat, St.on_file(s), 1n, 0n))))

# Oil
# ---

# the position of x in ls; 0 when absent
def Lines.index(ls: List<&2, String>, +x: String, +i: Nat) -> Nat:
  match ls:
    case Nil{}:
      0n
    case Con{h, t}:
      X.Bool.when(Nat, String.eq(h, x), u => Lines.index(t, x, 1n+i), u => i)

# Oil on folder dir, the cursor on entry name (oil.open: the entry the
# window came from)
def Oil.on(+s: T.St, +dir: String, +name: String) -> T.St:
  +ls = St.lines.at(s, T.Dir{dir})
  Win.open(s, T.Dir{dir}, T.Pos{Lines.index(ls, name, 0n), 0n})

# Oil on folder dir where its listing was left, else on its first line
# (Enter on a folder or "../", _)
def Oil.dir(+s: T.St, +dir: String) -> T.St:
  Win.open(s, T.Dir{dir}, Maybe.default(&2, T.Pos, Spots.get(S.St.spots(s), dir), T.Pos{0n, 0n}))

def Oil.here.at(+s: T.St, t: T.Tgt) -> T.St:
  match t:
    case T.File{i}:
      +path = B.Buf.path(B.Files.at(S.St.files(s), i))
      +dir = B.Path.dir(path)
      Oil.on(s, dir, B.Path.child(dir, path))
    case T.Dir{+path}:
      +up = B.Path.up(path)
      X.Bool.when(T.St, String.is_empty(path), u => Oil.on(s, up, B.Path.child(up, path)), u => s)

# - and <leader>e: Oil on the folder of the file shown, on its entry; from
# a folder, its parent, on the folder left; in the root, nothing
def Oil.here(+s: T.St) -> T.St:
  Oil.here.at(s, S.Win.tgt(S.St.win(s)))

# _ in Oil: the root's listing
def Oil.root(+s: T.St) -> T.St:
  Oil.dir(s, "")
