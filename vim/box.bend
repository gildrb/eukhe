# eukhe.com's Neovim: floats
# ==========================
#
# What fff's and fzf-lua's floats are drawn from: borders with titles, a
# preview pane (a file's lines, numbered or not, wrapped or not), runs of
# cells painted specially (marks). A float's row is a String exactly as
# many cells wide as the float.

import Base
import ./types.bend as T
import ./text.bend as X
import ./buf.bend as B

# Borders
# -------

# a border's run of w cells with title at its start (nvim's title_pos
# "left")
def Box.titled(+title: String, +w: Nat) -> String:
  X.Text.fit(title ++ X.Text.rep('─', w), w)

# a border's run of w cells with title in its middle ("center")
def Box.centered(+title: String, +w: Nat) -> String:
  +n = X.Text.cells(title)
  +pad = Nat.div(Nat.sub(w, n), 2n)
  X.Text.fit(X.Text.rep('─', pad) ++ title ++ X.Text.rep('─', Nat.sub(w, Nat.add(pad, n))), w)

# the column title starts at in a centered run of w cells
def Box.center_at(+title: String, +w: Nat) -> Nat:
  Nat.div(Nat.sub(w, X.Text.cells(title)), 2n)

def Box.mark(+row: Nat, +col: Nat, +len: Nat, g: T.Group) -> T.Mark:
  T.Mark{row, col, len, g}

def Box.side.cols(cs: List<&2, Nat>, +row: Nat, +acc: List<&2, T.Mark>) -> List<&2, T.Mark>:
  match cs:
    case Nil{}:
      acc
    case Con{c, t}:
      Box.side.cols(t, row, T.Mark{row, c, 1n, T.Border{}} <> acc)

# a border cell on each of n rows from row, at each of columns cs,
# painted as border
def Box.sides(n: Nat, +row: Nat, +cs: List<&2, Nat>, +acc: List<&2, T.Mark>) -> List<&2, T.Mark>:
  match n:
    case 0n:
      acc
    case 1n+p:
      Box.sides(p, 1n+row, cs, Box.side.cols(cs, row, acc))

def Marks.shift(ms: List<&2, T.Mark>, +dr: Nat, +dc: Nat, +acc: List<&2, T.Mark>) -> List<&2, T.Mark>:
  match ms:
    case Nil{}:
      acc
    case Con{T.Mark{r, c, n, g}, t}:
      Marks.shift(t, dr, dc, T.Mark{Nat.add(r, dr), Nat.add(c, dc), n, g} <> acc)

def Marks.cols(cs: List<&2, Nat>, +row: Nat, +col: Nat, +lim: Nat, +acc: List<&2, T.Mark>) -> List<&2, T.Mark>:
  match cs:
    case Nil{}:
      acc
    case Con{+c, t}:
      Marks.cols(t, row, col, lim, Bool.pick(List<&2, T.Mark>, Nat.is_lt(c, lim), T.Mark{row, Nat.add(col, c), 1n, T.Match{}} <> acc, acc))

# Previews
# --------

# what a preview shows: the lines from its first one, how many rows, its
# width, the number column's width (0: none) and the number of its first
# line, whether long lines wrap, and the cursorline's line counted from 1
# at the first (0: none)
type Pane is Data:
  Pane{lines: List<&2, String>, rows: Nat, width: Nat, numw: Nat, first: Nat, wrap: Bool, cursor: Nat}

# a file's type wraps in fff's preview (markdown, text)
def Pane.wraps(+path: String) -> Bool:
  Bool.or(String.ends_with(path, ".md"), Bool.or(String.ends_with(path, ".txt"), String.eq(path, "LICENSE")))

# the number column of line n, w cells (a space last), or blanks
def Pane.num(+n: Nat, +w: Nat, +shown: Bool) -> String:
  Bool.pick(String, Nat.is_eq(w, 0n), "", Bool.pick(String, shown, X.Text.right(Nat.show(n), Nat.sub(w, 1n)) ++ " ", X.Text.spaces(w, SNil{})))

# the rows of s cut in runs of w cells, at most n of them, reversed onto
# acc
def Pane.chunks(n: Nat, +s: String, +w: Nat, +acc: List<&2, String>) -> List<&2, String>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +c = X.Text.cut(s, w)
      +rest = X.Text.dropc(s, w)
      X.Bool.when(List<&2, String>, String.is_empty(rest), u => Pane.chunks(p, rest, w, c <> acc), u => c <> acc)

# the screen rows a line takes when wrapped in w cells
def Pane.height(+s: String, +w: Nat) -> Nat:
  Nat.max(1n, Nat.div(Nat.add(X.Text.cells(s), Nat.sub(w, 1n)), Nat.max(w, 1n)))

def Pane.blank(n: Nat, +w: Nat, +acc: List<&2, String>) -> List<&2, String>:
  match n:
    case 0n:
      acc
    case 1n+p:
      Pane.blank(p, w, X.Text.spaces(w, SNil{}) <> acc)

def Pane.sel(n: Nat, +row: Nat, +w: Nat, +ms: List<&2, T.Mark>) -> List<&2, T.Mark>:
  match n:
    case 0n:
      ms
    case 1n+p:
      Pane.sel(p, 1n+row, w, T.Mark{row, 0n, w, T.Sel{}} <> ms)

# the rows of a line's chunks: the number column on the first, blanks on
# the others
def Pane.rows(cs: List<&2, String>, +nw: Nat, +n: Nat, +tw: Nat, +acc: List<&2, String>, +first: Bool) -> List<&2, String>:
  match cs:
    case Nil{}:
      List.reverse(&2, String, acc)
    case Con{c, t}:
      Pane.rows(t, nw, n, tw, (Pane.num(n, nw, first) ++ X.Text.fit(c, tw)) <> acc, False{})

# 'display' lastline: a line that does not fit shows "@@@" at the end of
# the window's last row
def Pane.lastline(+rs: List<&2, String>, +w: Nat) -> List<&2, String>:
  +n = List.length(&2, String, rs)
  +last = Maybe.default(&2, String, List.last(&2, String, rs), SNil{})
  List.append(&2, String, List.take(&2, String, rs, Nat.sub(n, 1n)), [X.Text.cut(last, Nat.sub(w, 3n)) ++ "@@@"])

# a preview's rows (each w cells) and marks, from mark row row on, the
# cursor line cur lines down
def Pane.go(ls: List<&2, String>, h: Nat, +w: Nat, +nw: Nat, +n: Nat, +wrap: Bool, +cur: Nat, +row: Nat, +acc: List<&2, String>, +ms: List<&2, T.Mark>) -> (List<&2, String> & List<&2, T.Mark>):
  match ls h:
    case _ 0n:
      (List.reverse(&2, String, acc), ms)
    case Nil{} 1n+p:
      (List.reverse(&2, String, Pane.blank(1n+p, w, acc)), ms)
    case Con{+l, rest} 1n++p:
      +tw = Nat.sub(w, nw)
      +rows = Bool.pick(Nat, wrap, Pane.height(l, tw), 1n)
      +fits = Nat.is_le(rows, 1n+p)
      +shown = Nat.min(rows, 1n+p)
      +chunks = List.reverse(&2, String, Pane.chunks(shown, l, tw, Nil{}))
      +texts = Pane.rows(chunks, nw, n, tw, Nil{}, True{})
      +texts2 = Bool.pick(List<&2, String>, fits, texts, Pane.lastline(texts, w))
      +nm = Bool.pick(List<&2, T.Mark>, Nat.is_eq(nw, 0n), ms, T.Mark{row, 0n, nw, T.Number{}} <> ms)
      +sel = Bool.pick(List<&2, T.Mark>, Nat.is_eq(cur, 1n), Pane.sel(shown, row, w, nm), nm)
      Pane.go(rest, Nat.sub(1n+p, shown), w, nw, 1n+n, wrap, Nat.sub(cur, 1n), Nat.add(row, shown), List.append(&2, String, List.reverse(&2, String, texts2), acc), sel)

# a preview's rows and marks (from row row0 of the float)
def Pane.draw(p: Pane, +row0: Nat) -> (List<&2, String> & List<&2, T.Mark>):
  match p:
    case Pane{lines, rows, +width, +numw, +first, +wrap, +cursor}:
      Pane.go(lines, rows, width, numw, first, wrap, cursor, row0, Nil{}, Nil{})

# the number column fzf-lua's and fff's previews give a file of n lines
# ('numberwidth' 4)
def Pane.numw(+n: Nat) -> Nat:
  Nat.max(4n, 1n+X.Text.digits(n))

# the first line on screen when line l is in the middle of h rows (zz)
def Pane.zz(+l: Nat, +h: Nat) -> Nat:
  Nat.sub(l, Nat.div(Nat.sub(h, 1n), 2n))

def Pane.above(ls: List<&2, String>, n: Nat, +w: Nat, +need: Nat) -> Nat:
  match ls need:
    case Nil{} _:
      n
    case _ 0n:
      n
    case Con{+h, t} 1n+p:
      Pane.above(t, 1n+n, w, Nat.sub(1n+p, Pane.height(h, w)))

# the first line on screen when line l is put at the top with 8 rows of
# 'scrolloff' above it (fff's grep preview: cursor to l, zt), rows of
# wrapped lines counted as the screen shows them
def Pane.zt(+ls: List<&2, String>, +l: Nat, +w: Nat, +wrap: Bool) -> Nat:
  +above = List.reverse(&2, String, B.Lines.take(ls, l))
  Nat.sub(l, Bool.pick(Nat, wrap, Pane.above(above, 0n, w, 8n), Nat.min(l, 8n)))
