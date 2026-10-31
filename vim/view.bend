# eukhe.com's Neovim: the screen
# ==============================
#
# The screen is rows x cols cells: text rows, then the statusline
# (laststatus=3), then the command line (cmdheight=1). Left of the text,
# the number column. Vim.frame lists what each part shows; the host paints
# it cell for cell.

import Base
import ./types.bend as T
import ./text.bend as X
import ./buf.bend as B
import ./find.bend as F

# Sizes
# -----

# the smallest screen the editor takes: a smaller one is taken as this
def View.min_rows() -> Nat:
  3n

def View.min_cols() -> Nat:
  12n

# 'scrolloff' and 'sidescrolloff' (Gil's config: 8)
def View.so() -> Nat:
  8n

# lines the wheel scrolls a notch ('mousescroll' ver:3)
def View.notch() -> Nat:
  3n

# the text rows of a screen of r rows
def View.text_rows(r: Nat) -> Nat:
  Nat.sub(r, 2n)

# the number column's width for n lines: 'numberwidth' 4, or the digits
# of n and a space; none when neither 'number' nor 'relativenumber' is set
def View.numw(o: T.Opts, n: Nat) -> Nat:
  match o:
    case T.Opts{nu, rnu, hls}:
      Bool.pick(Nat, Bool.or(nu, rnu), Nat.max(4n, 1n+X.Text.digits(n)), 0n)

# the sign column ('signcolumn' yes: two cells), in file windows only (Oil
# sets 'signcolumn' no)
def View.signw(+sign: Bool) -> Nat:
  Bool.pick(Nat, sign, 2n, 0n)

# where text starts: the sign column, then the number column; on a screen
# of c columns, at least one column is left for the text
def View.gutter(o: T.Opts, n: Nat, +sign: Bool, c: Nat) -> Nat:
  Nat.min(Nat.add(View.signw(sign), View.numw(o, n)), Nat.sub(c, 1n))

# the text columns left of a screen of c columns with gutter g
def View.text_cols(c: Nat, g: Nat) -> Nat:
  Nat.sub(c, g)

# Scrolling
# ---------

# the scrolloff a window of h rows can keep above the cursor
def View.so_in(h: Nat) -> Nat:
  Nat.min(View.so(), Nat.div(Nat.sub(h, 1n), 2n))

# below it: one more in a window of even height, as Neovim keeps the
# cursor just above the middle when 'scrolloff' is over half the window
def View.so_dn(h: Nat) -> Nat:
  Nat.min(View.so(), Nat.div(h, 2n))

# the first screen line that shows line l in a window of h rows over a
# buffer whose last line is last: the old first line top moved as little
# as it takes to keep 'scrolloff' lines above and below the cursor where
# the buffer has them; a move of more than half the window puts line l in
# the middle instead, as Vim does after a jump
def View.fit(+top: Nat, +l: Nat, +h: Nat, +last: Nat) -> Nat:
  +so = View.so_in(h)
  +half = Nat.div(Nat.sub(h, 1n), 2n)
  +lo = Nat.sub(l, Nat.min(so, l))
  +hi = Nat.sub(Nat.add(l, Nat.min(View.so_dn(h), Nat.sub(last, l))), Nat.sub(h, 1n))
  +mid = Nat.min(Nat.sub(l, half), Nat.sub(last, Nat.min(last, Nat.sub(h, 1n))))
  +up = Bool.pick(Nat, Nat.is_gt(Nat.sub(top, lo), half), mid, lo)
  +down = Bool.pick(Nat, Nat.is_gt(Nat.sub(hi, top), half), mid, hi)
  Bool.pick(Nat, Nat.is_lt(lo, top), up, Bool.pick(Nat, Nat.is_gt(hi, top), down, top))

# sideways: the first column on screen, moved as little as it takes to
# keep 'sidescrolloff' columns either side of column c where the line has
# them
def View.fit_side(+left: Nat, +c: Nat, +w: Nat, +last: Nat) -> Nat:
  +so = View.so_in(w)
  +lo = Nat.sub(c, Nat.min(so, c))
  +hi = Nat.sub(Nat.add(c, Nat.min(so, Nat.sub(last, c))), Nat.sub(w, 1n))
  Bool.pick(Nat, Nat.is_lt(lo, left), lo, Bool.pick(Nat, Nat.is_gt(hi, left), hi, left))

# the largest first line: the last line on the screen's first row, less
# the scrolloff above it ('scrolloff' always holds)
def View.max_top(+h: Nat, +last: Nat) -> Nat:
  Nat.sub(last, Nat.min(View.so_in(h), last))

# the lines the cursor may take with first line top in a window of h
# rows: from band_lo to band_hi, 'scrolloff' lines from either edge where
# the buffer goes on past it; View.fit keeps top for every line in it
def View.band_lo(+top: Nat, +h: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_eq(top, 0n), 0n, Nat.add(top, View.so_in(h)))

def View.band_hi(+top: Nat, +h: Nat, +last: Nat) -> Nat:
  +bottom = Nat.add(top, Nat.sub(h, 1n))
  Bool.pick(Nat, Nat.is_le(last, bottom), last, Nat.sub(bottom, View.so_dn(h)))

# l pulled into the band of a window with first line top
def View.drag(+l: Nat, +top: Nat, +h: Nat, +last: Nat) -> Nat:
  Nat.max(View.band_lo(top, h), Nat.min(l, View.band_hi(top, h, last)))

# Numbers
# -------

# the number column of buffer line k with the cursor on line l, w cells
# wide: the line's number ('number'), its distance from the cursor
# ('relativenumber'; the cursor's own line shows its number, left
# aligned, when both are set), then a space
def View.num(o: T.Opts, +k: Nat, +l: Nat, +w: Nat) -> String:
  match o:
    case T.Opts{+nu, +rnu, hls}:
      +cell = Nat.sub(w, 1n)
      +here = Nat.is_eq(k, l)
      +dist = Bool.pick(Nat, Nat.is_lt(k, l), Nat.sub(l, k), Nat.sub(k, l))
      +abs = Nat.show(1n+k)
      +text = Bool.pick(String, Bool.and(rnu, Bool.not(here)), X.Text.right(Nat.show(dist), cell), Bool.pick(String, Bool.and(rnu, Bool.and(here, nu)), X.Text.leftpad(abs, cell), Bool.pick(String, nu, X.Text.right(abs, cell), X.Text.right("0", cell))))
      Bool.pick(String, Nat.is_eq(w, 0n), "", text ++ " ")

def View.nums.go(r: Nat, +o: T.Opts, +k: Nat, +l: Nat, +last: Nat, +w: Nat, +g: Nat, +sign: String, +blank: String, +acc: List<&2, String>) -> List<&2, String>:
  match r:
    case 0n:
      List.reverse(&2, String, acc)
    case 1n+p:
      View.nums.go(p, o, 1n+k, l, last, w, g, sign, blank, Bool.pick(String, Nat.is_gt(k, last), blank, X.Text.fitted(sign ++ View.num(o, k, l, w), g)) <> acc)

# the gutter of each text row, g cells, from line top: the sign column
# (blank), then the number column w cells wide; blanks past the end
def View.nums(+h: Nat, +o: T.Opts, +top: Nat, +l: Nat, +last: Nat, +w: Nat, +signs: Bool, +g: Nat) -> List<&2, String>:
  +sign = X.Text.spaces(View.signw(signs), SNil{})
  View.nums.go(h, o, top, l, last, w, g, sign, X.Text.spaces(g, SNil{}), Nil{})

# Search hits on screen
# ---------------------

# a hit at column c of length n, on screen row r, in the window's columns
# left to left + w - 1, starting at screen column g; None when it is off
# screen
def View.span(+r: Nat, +c: Nat, +n: Nat, +left: Nat, +w: Nat, +g: Nat) -> Maybe<&2, T.Span>:
  +from = Nat.max(c, left)
  +to = Nat.min(Nat.add(c, n), Nat.add(left, w))
  Bool.pick(Maybe<&2, T.Span>, Nat.is_lt(from, to), Some{T.Span{r, Nat.add(g, Nat.sub(from, left)), Nat.sub(to, from)}}, None{})

def View.span.put(m: Maybe<&2, T.Span>, acc: List<&2, T.Span>) -> List<&2, T.Span>:
  match m:
    case None{}:
      acc
    case Some{s}:
      s <> acc

def View.spans(cs: List<&2, Nat>, +r: Nat, +n: Nat, +left: Nat, +w: Nat, +g: Nat, +acc: List<&2, T.Span>) -> List<&2, T.Span>:
  match cs:
    case Nil{}:
      acc
    case Con{+c, t}:
      View.spans(t, r, n, left, w, g, View.span.put(View.span(r, c, n, left, w, g), acc))

def View.hits.go(rows: Nat, ls: List<&2, String>, fls: List<&2, String>, +f: T.Find, +n: Nat, +r: Nat, +left: Nat, +w: Nat, +g: Nat, +acc: List<&2, T.Span>) -> List<&2, T.Span>:
  match rows ls fls:
    case 0n _ _:
      List.reverse(&2, T.Span, acc)
    case 1n+p Nil{} _:
      List.reverse(&2, T.Span, acc)
    case 1n+p _ Nil{}:
      List.reverse(&2, T.Span, acc)
    case 1n+p Con{h, t} Con{fh, ft}:
      View.hits.go(p, t, ft, f, n, 1n+r, left, w, g, View.spans(F.Find.hits(f, h, fh), r, n, left, w, g, acc))

# the hits of search f on the h text rows from line top: one span per
# visible run
def View.hits(+ls: List<&2, String>, +fls: List<&2, String>, +f: T.Find, +top: Nat, +h: Nat, +left: Nat, +w: Nat, +g: Nat) -> List<&2, T.Span>:
  match f:
    case T.Find{+text, back, word}:
      View.hits.go(h, B.Lines.drop(ls, top), B.Lines.drop(fls, top), f, X.Text.len(text), 0n, left, w, g, Nil{})

# The scrollbar
# -------------

# the thumb over h rows for a buffer of n lines from line top: its first
# row and its rows in column c; no rows when every line fits
def View.bar(+n: Nat, +h: Nat, +top: Nat, +c: Nat) -> T.Span:
  +len = Nat.min(Nat.max(1n, Nat.div(Nat.mul(h, h), Nat.max(n, 1n))), h)
  +start = Nat.min(Nat.div(Nat.mul(top, h), Nat.max(n, 1n)), Nat.sub(h, len))
  Bool.pick(T.Span, Nat.is_gt(n, h), T.Span{start, c, len}, T.Span{0n, c, 0n})
