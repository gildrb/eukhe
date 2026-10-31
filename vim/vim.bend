# eukhe.com's Neovim: the editor
# ==============================
#
# Vim.step is the whole editor as one pure function: it takes the editor
# and one event (a key, a click, the wheel, a new screen size) and returns
# the editor after it and what the host does (open a URL, copy text).
# Vim.frame says what the screen shows. The host turns browser events into
# Ev, paints Frame and runs Act; it decides nothing.
#
# The modules, each over the ones before it: types, text, buf (files and
# Oil's listings), move (motions), find (search), view (scrolling, the
# number column), st (St's fields), core (the window, jumps, Oil), ex
# (search, links, Ex commands), box (floats), fff and fzf (the pickers),
# pick (a picker's keys), keys (every key), screen (the frame).

import Base
import ./types.bend as T
import ./text.bend as X
import ./buf.bend as B
import ./view.bend as V
import ./st.bend as S
import ./core.bend as C
import ./pick.bend as P
import ./keys.bend as K
import ./screen.bend as R

# The mouse
# ---------

# a click on screen cell (row, col): in the text, the cursor goes there; a
# picker closes
def Vim.click(+s: T.St, m: T.Mode, +row: Nat, +col: Nat) -> T.St:
  match m:
    case T.Normal{}:
      +g = C.St.g(s)
      +w = S.St.win(s)
      +s2 = S.St.set_count(S.St.set_pend(s, T.NoPend{}), 0n)
      X.Bool.when(T.St, Nat.is_lt(row, C.St.h(s)), u => s2, u => C.Win.go(s2, T.Pos{Nat.add(S.Win.top(w), row), Nat.add(S.Win.left(w), Nat.sub(col, g))}, False{}))
    case T.Typing{kind, text}:
      s
    case T.Picking{kind, q, its, n, sel, top, pv, levels}:
      S.St.set_mode(s, T.Normal{})

# notches of the wheel: three lines each, the cursor dragged on screen; in
# a picker, the selection moves
def Vim.wheel(+s: T.St, m: T.Mode, +down: Bool, +notches: Nat) -> T.St:
  match m:
    case T.Normal{}:
      K.Key.scroll_by(s, down, Nat.mul(notches, V.View.notch()), False{})
    case T.Typing{kind, text}:
      s
    case T.Picking{kind, q, its, n, sel, top, pv, levels}:
      P.Pick.key(s, kind, q, its, n, sel, pv, levels, Bool.pick(String, down, "<Down>", "<Up>"))

# The editor
# ----------

# a new screen size (Vim.final takes one under View.min_rows() x
# View.min_cols() as that)
def Vim.size(+s: T.St, +rows: Nat, +cols: Nat) -> T.St:
  S.St.set_cols(S.St.set_rows(s, rows), cols)

# the window over files fs: on a buffer it may show (B.Tgt.real), else on
# the first file's start
def Vim.real(+fs: List<&2, T.Buf>, w: T.Win) -> T.Win:
  match w:
    case T.Win{+tgt, cur, want, top, left}:
      Bool.pick(T.Win, B.Tgt.real(fs, tgt), T.Win{tgt, cur, want, top, left}, T.Win{T.File{0n}, T.Pos{0n, 0n}, T.Col{0n}, 0n, 0n})

# a screen of at least View.min_rows() x View.min_cols(), the cursor on
# the text and the window scrolled to it (Win.settle)
def Vim.fit(+s: T.St) -> T.St:
  C.Win.settle(S.St.set_cols(S.St.set_rows(s, Nat.max(S.St.rows(s), V.View.min_rows())), Nat.max(S.St.cols(s), V.View.min_cols())))

# the editor settled, as every step leaves it: on a buffer it may show,
# then fitted (Vim.fit)
def Vim.final(+s: T.St) -> T.St:
  Vim.fit(S.St.set_win(s, Vim.real(S.St.files(s), S.St.win(s))))

# st on the files and the screen of s: only the start and a size event
# set those
def Vim.keep(+s: T.St, st: T.St) -> T.St:
  S.St.set_cols(S.St.set_rows(S.St.set_files(st, S.St.files(s)), S.St.rows(s)), S.St.cols(s))

# a step from s, its editor settled
def Vim.done(+s: T.St, r: T.Step) -> T.Step:
  match r:
    case T.Step{st, act}:
      T.Step{Vim.final(Vim.keep(s, st)), act}

def Vim.fold.lines(ls: List<&2, String>, +acc: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      List.reverse(&2, String, acc)
    case Con{h, t}:
      Vim.fold.lines(t, X.Text.fold(h) <> acc)

def Vim.fold(fs: List<&2, T.Buf>, +acc: List<&2, List<&2, String>>) -> List<&2, List<&2, String>>:
  match fs:
    case Nil{}:
      List.reverse(&2, List<&2, String>, acc)
    case Con{T.Buf{p, ls}, t}:
      Vim.fold(t, Vim.fold.lines(ls, Nil{}) <> acc)

def Dirs.add(+d: String, ds: List<&2, String>) -> List<&2, String>:
  match ds:
    case Nil{}:
      [d]
    case Con{+h, +t}:
      X.Bool.when(List<&2, String>, String.eq(h, d), u => h <> Dirs.add(d, t), u => h <> t)

# a folder and those above it, up to the root
def Dirs.up(n: Nat, +d: String, +acc: List<&2, String>) -> List<&2, String>:
  match n:
    case 0n:
      acc
    case 1n+p:
      X.Bool.when(List<&2, String>, String.is_empty(d), u => Dirs.up(p, B.Path.up(d), Dirs.add(d, acc)), u => acc)

def Dirs.all(fs: List<&2, T.Buf>, +acc: List<&2, String>) -> List<&2, String>:
  match fs:
    case Nil{}:
      acc
    case Con{T.Buf{+p, ls}, t}:
      Dirs.all(t, Dirs.up(X.Text.len(p), B.Path.dir(p), acc))

def Dirs.list(ds: List<&2, String>, +fs: List<&2, T.Buf>, +acc: List<&2, T.Listing>) -> List<&2, T.Listing>:
  match ds:
    case Nil{}:
      acc
    case Con{+d, t}:
      Dirs.list(t, fs, T.Listing{d, B.Oil.list(fs, d)} <> acc)

# the editor before it settles at the start: the first file (the page) at
# its first line, on a screen of rows x cols
def Vim.start(fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat) -> T.St:
  +files = B.Files.some(fs, Nil{})
  +n = B.Files.len(files)
  {T.St{files, Vim.fold(files, Nil{}), Dirs.list(Dirs.all(files, [""]), files, Nil{}), T.Win{T.File{0n}, T.Pos{0n, 0n}, T.Col{0n}, 0n, 0n}, List.replicate(T.Pos, n, T.Pos{0n, 0n}), Nil{}, [0n], [0n], Nil{}, Nil{}, T.Normal{}, 0n, T.NoPend{}, None{}, False{}, T.Opts{True{}, True{}, True{}}, rows, cols, "", ""} : T.St}

# the editor at the start
def Vim.init(fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat) -> T.St:
  Vim.final(Vim.start(fs, rows, cols))

# one event
def Vim.step(+s: T.St, e: T.Ev) -> T.Step:
  match e:
    case T.EvKey{name}:
      Vim.done(s, K.Key.in(s, S.St.mode(s), name))
    case T.EvClick{row, col}:
      Vim.done(s, K.Key.ok(Vim.click(s, S.St.mode(s), row, col)))
    case T.EvWheel{down, notches}:
      Vim.done(s, K.Key.ok(Vim.wheel(s, S.St.mode(s), down, notches)))
    case T.EvSize{rows, cols}:
      +s2 = Vim.size(s, rows, cols)
      Vim.done(s2, K.Key.ok(s2))

# what the screen shows
def Vim.frame(+s: T.St) -> T.Frame:
  R.Scr.frame(s)

# the lines on screen for the host: the target's lines
def Vim.lines(+s: T.St) -> List<&2, String>:
  C.St.lines(s)
