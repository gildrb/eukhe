# selection: the in-app text selection of the fullscreen chat. In
# fullscreen the terminal reports every press, drag and release to eukhe
# (crates/eukhe-tui/src/screen_mode.rs), so its own selection cannot
# work; eukhe selects instead (crates/eukhe-tui/src/selection.rs feeds
# each mouse event to this model through bend/ffi_selection.bend).
#
# A press starts a selection at a cell, a drag moves its head (and, past
# the transcript's edge, asks for one scroll step), a release copies the
# cells between anchor and head. A second press on the same cell within
# `window()` ms picks a word, a third the row. A key, a wheel notch or a
# change of the content under the selection clears it.
#
# A cell is a row and a column: the row a transcript row id (Rust numbers
# the transcript's rows top to bottom), the column a screen column. A row
# reaches the model as its glyphs: 0 a blank (one cell), w >= 1 a glyph w
# cells wide, and how it sits in a soft-wrapped block.

import Base

# Types
# -----

type Cell is Data:
  Cell{row: Nat, col: Nat}

# the cells from start to end in reading order, both in
type Rng is Data:
  Rng{start: Cell, end: Cell}

# how a row sits in a soft-wrapped block: a row of its own, a block's
# first row, or a later row of a block (it continues the row above)
type Wrap is Data:
  Single{}
  Head{}
  Cont{}

type Row is Data:
  Row{wrap: Wrap, gs: List<&2, Nat>}

# one input: a press (its cell, the time in ms, the glyphs of its row), a
# drag (its cell, the first and last transcript rows on screen), a release
# (the rows of the selection, from its first row on), a key, Esc, a wheel
# notch, a change of the content under the selection
type Ev is Data:
  EvPress{at: Cell, time: Nat, gs: List<&2, Nat>}
  EvDrag{at: Cell, lo: Nat, hi: Nat}
  EvRelease{rows: List<&2, Row>}
  EvKey{}
  EvEsc{}
  EvWheel{}
  EvChanged{}

# nothing; a button held where it was pressed (no selection yet); a drag
# from anchor to head; a word or a row picked by a double or triple press;
# a selection shown after its release
type Mode is Data:
  Idle{}
  Pressed{at: Cell}
  Selecting{anchor: Cell, head: Cell}
  Picked{r: Rng}
  Shown{r: Rng}

# the last press: its cell, its time, and how many presses it counts
type Click is Data:
  Click{at: Cell, time: Nat, n: Nat}

type St is Data:
  St{mode: Mode, last: Maybe<&2, Click>}

# the scroll step a drag asks for
type Pan is Data:
  PanNone{}
  PanUp{}
  PanDown{}

# glyphs from..to-1 of release row `row`, after a newline when nl
type Piece is Data:
  Piece{row: Nat, from: Nat, to: Nat, nl: Bool}

# the selection to show, the text to copy, the scroll step, and whether
# the input is spent (Esc that cleared a shown selection)
type Out is Data:
  Out{sel: Maybe<&2, Rng>, copy: Maybe<&2, List<&2, Piece>>, pan: Pan, eat: Bool}

type Res is Data:
  Res{st: St, out: Out}

# Constants
# ---------

# a press within this many ms of the last press, on its cell, counts on
# (double and triple click)
def window() -> Nat:
  400n

def start() -> St:
  St{Idle{}, None{}}

# Cells
# -----

# a at or before b in reading order
def cell_le(a: Cell, b: Cell) -> Bool:
  match a:
    case Cell{+ar, ac}:
      match b:
        case Cell{+br, bc}:
          Bool.or(Nat.is_lt(ar, br), Bool.and(Nat.is_eq(ar, br), Nat.is_le(ac, bc)))

def cell_eq(a: Cell, b: Cell) -> Bool:
  match a:
    case Cell{ar, ac}:
      match b:
        case Cell{br, bc}:
          Bool.and(Nat.is_eq(ar, br), Nat.is_eq(ac, bc))

# the cells between a and b, whichever comes first
def order(+a: Cell, +b: Cell) -> Rng:
  Bool.pick(Rng, cell_le(a, b), Rng{a, b}, Rng{b, a})

# Glyphs
# ------

# the last cell of glyph g at column c
def glast(g: Nat, +c: Nat) -> Nat:
  match g:
    case 0n:
      c
    case 1n+p:
      Nat.add(p, c)

# the column after glyph g at column c
def gnext(g: Nat, c: Nat) -> Nat:
  1n+glast(g, c)

# the column after the glyphs gs from column c
def width(gs: List<&2, Nat>, c: Nat) -> Nat:
  match gs:
    case Nil{}:
      c
    case Con{g, rest}:
      width(rest, gnext(g, c))

# The selection
# -------------

def sel(m: Mode) -> Maybe<&2, Rng>:
  match m:
    case Idle{}:
      None{}
    case Pressed{a}:
      None{}
    case Selecting{a, h}:
      Some{order(a, h)}
    case Picked{r}:
      Some{r}
    case Shown{r}:
      Some{r}

# a selection is on screen
def seen(m: Mode) -> Bool:
  match m:
    case Idle{}:
      False{}
    case Pressed{a}:
      False{}
    case Selecting{a, h}:
      True{}
    case Picked{r}:
      True{}
    case Shown{r}:
      True{}

# the answer that keeps mode m: nothing to copy, no scroll
def quiet(+m: Mode, last: Maybe<&2, Click>) -> Res:
  Res{St{m, last}, Out{sel(m), None{}, PanNone{}, False{}}}

# everything cleared
def cleared(eat: Bool) -> Res:
  Res{St{Idle{}, None{}}, Out{None{}, None{}, PanNone{}, eat}}

# Presses
# -------

def next(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+p:
      match p:
        case 0n:
          2n
        case 1n+q:
          match q:
            case 0n:
              3n
            case 1n+x:
              1n

def near(on: Bool, n: Nat) -> Nat:
  match on:
    case True{}:
      next(n)
    case False{}:
      1n

# how many presses a press at `at` and `time` counts: one more than the
# last when it was on the same cell at most window() ms before (3 wraps to
# 1), else 1
def clicks(last: Maybe<&2, Click>, +at: Cell, +time: Nat) -> Nat:
  match last:
    case None{}:
      1n
    case Some{k}:
      match k:
        case Click{a, +t, n}:
          near(Bool.and(cell_eq(a, at), Bool.and(Nat.is_le(t, time), Nat.is_le(Nat.sub(time, t), window()))), n)

# the column after the run of non-blank glyphs gs, at column c on, less 1
# (e: the last cell of the run so far)
def word.last(gs: List<&2, Nat>, +e: Nat) -> Nat:
  match gs:
    case Nil{}:
      e
    case Con{g, rest}:
      match g:
        case 0n:
          e
        case 1n+p:
          word.last(rest, Nat.add(p, 1n+e))

def word.blank(hit: Bool, more: Maybe<&2, Rng>) -> Maybe<&2, Rng>:
  match hit:
    case True{}:
      None{}
    case False{}:
      more

def word.glyph(hit: Bool, +r: Nat, s: Nat, rest: List<&2, Nat>, e: Nat, more: Maybe<&2, Rng>) -> Maybe<&2, Rng>:
  match hit:
    case True{}:
      Some{Rng{Cell{r, s}, Cell{r, word.last(rest, e)}}}
    case False{}:
      more

# the word of row r at column x: the run of non-blank glyphs that covers
# x; gs from column c on, s the column the current run started at
def word(gs: List<&2, Nat>, +c: Nat, +s: Nat, +x: Nat, +r: Nat) -> Maybe<&2, Rng>:
  match gs:
    case Nil{}:
      None{}
    case Con{g, +rest}:
      match g:
        case 0n:
          word.blank(Nat.is_le(x, c), word(rest, 1n+c, 1n+c, x, r))
        case 1n+p:
          +e = Nat.add(p, c)
          word.glyph(Nat.is_le(x, e), r, s, rest, e, word(rest, 1n+e, s, x, r))

def picked_or(m: Maybe<&2, Rng>, at: Cell) -> Mode:
  match m:
    case None{}:
      Pressed{at}
    case Some{r}:
      Picked{r}

def line.of(w: Nat, +r: Nat, x: Nat) -> Mode:
  match w:
    case 0n:
      Pressed{Cell{r, x}}
    case 1n+p:
      Picked{Rng{Cell{r, 0n}, Cell{r, p}}}

def press.pick(q: Nat, +r: Nat, +x: Nat, gs: List<&2, Nat>) -> Mode:
  match q:
    case 0n:
      picked_or(word(gs, 0n, 0n, x, r), Cell{r, x})
    case 1n+y:
      line.of(width(gs, 0n), r, x)

def press.cell(q: Nat, at: Cell, gs: List<&2, Nat>) -> Mode:
  match at:
    case Cell{r, x}:
      press.pick(q, r, x, gs)

def press.mode(n: Nat, at: Cell, gs: List<&2, Nat>) -> Mode:
  match n:
    case 0n:
      Pressed{at}
    case 1n+p:
      match p:
        case 0n:
          Pressed{at}
        case 1n+q:
          press.cell(q, at, gs)

def press.go(+m: Mode, k: Click) -> Res:
  Res{St{m, Some{k}}, Out{sel(m), None{}, PanNone{}, False{}}}

def press(last: Maybe<&2, Click>, +at: Cell, +time: Nat, gs: List<&2, Nat>) -> Res:
  +n = clicks(last, at, time)
  press.go(press.mode(n, at, gs), Click{at, time, n})

# Drags
# -----

# a drag's cell moved into the rows lo..hi
def clamp(at: Cell, +lo: Nat, +hi: Nat) -> Cell:
  match at:
    case Cell{+r, c}:
      Cell{Bool.pick(Nat, Nat.is_lt(r, lo), lo, Bool.pick(Nat, Nat.is_lt(hi, r), hi, r)), c}

# one scroll step toward a drag past the rows lo..hi
def pan(at: Cell, +lo: Nat, +hi: Nat) -> Pan:
  match at:
    case Cell{+r, c}:
      Bool.pick(Pan, Nat.is_lt(r, lo), PanUp{}, Bool.pick(Pan, Nat.is_lt(hi, r), PanDown{}, PanNone{}))

def moved(+m: Mode, p: Pan) -> Res:
  Res{St{m, None{}}, Out{sel(m), None{}, p, False{}}}

def drag.picked(r: Rng, +h: Cell, p: Pan) -> Res:
  match r:
    case Rng{+s, +e}:
      moved(Selecting{Bool.pick(Cell, cell_le(s, h), s, e), h}, p)

def drag(m: Mode, +at: Cell, +lo: Nat, +hi: Nat) -> Res:
  match m:
    case Idle{}:
      quiet(Idle{}, None{})
    case Pressed{+a}:
      +h = clamp(at, lo, hi)
      Bool.pick(Res, cell_eq(a, h), moved(Pressed{a}, pan(at, lo, hi)), moved(Selecting{a, h}, pan(at, lo, hi)))
    case Selecting{a, h}:
      moved(Selecting{a, clamp(at, lo, hi)}, pan(at, lo, hi))
    case Picked{r}:
      drag.picked(r, clamp(at, lo, hi), pan(at, lo, hi))
    case Shown{r}:
      quiet(Shown{r}, None{})

# Copy
# ----

# column c is at or before the last column `to` (None: the row's end)
def before(+c: Nat, to: Maybe<&2, Nat>) -> Bool:
  match to:
    case None{}:
      True{}
    case Some{t}:
      Nat.is_le(c, t)

# glyph g at column c reaches the first column `from` (None: the row's
# start): its last cell is at or past it
def reach(from: Maybe<&2, Nat>, g: Nat, +c: Nat) -> Bool:
  match from:
    case None{}:
      True{}
    case Some{f}:
      Nat.is_le(f, glast(g, c))

def lo.pick(reach: Bool, j: Nat, more: Nat) -> Nat:
  match reach:
    case True{}:
      j
    case False{}:
      more

# the index of the first glyph that reaches column from (gs from column c
# and index j on)
def row_lo(gs: List<&2, Nat>, +c: Nat, +j: Nat, +from: Maybe<&2, Nat>) -> Nat:
  match gs:
    case Nil{}:
      j
    case Con{+g, rest}:
      lo.pick(reach(from, g, c), j, row_lo(rest, gnext(g, c), 1n+j, from))

def counts(trim: Bool, g: Nat) -> Bool:
  match trim:
    case False{}:
      True{}
    case True{}:
      match g:
        case 0n:
          False{}
        case 1n+p:
          True{}

def nb.pick(more: Nat, here: Bool, j: Nat) -> Nat:
  match more:
    case 0n:
      match here:
        case True{}:
          1n+j
        case False{}:
          0n
    case 1n+p:
      1n+p

# one past the index of the last glyph that starts at or before `to` and
# counts (not a blank, when trim), 0 when none does
def row_nb(gs: List<&2, Nat>, +c: Nat, +j: Nat, +to: Maybe<&2, Nat>, +trim: Bool) -> Nat:
  match gs:
    case Nil{}:
      0n
    case Con{+g, rest}:
      nb.pick(row_nb(rest, gnext(g, c), 1n+j, to, trim), Bool.and(before(c, to), counts(trim, g)), j)

def max.pick(le: Bool, a: Nat, b: Nat) -> Nat:
  match le:
    case True{}:
      b
    case False{}:
      a

def not_cont(w: Wrap) -> Bool:
  match w:
    case Single{}:
      True{}
    case Head{}:
      True{}
    case Cont{}:
      False{}

# a row keeps no glyph but blanks up to column `to` (None: the row's end)
def blank_to(gs: List<&2, Nat>, +to: Maybe<&2, Nat>) -> Bool:
  Nat.is_eq(row_nb(gs, 0n, 0n, to, True{}), 0n)

# the rows after a row add only blanks to its line: each later row of the
# copy that continues the line keeps no glyph but blanks (k: rows before
# the copy's last, which ends at column c2)
def rest_blank(rows: List<&2, Row>, k: Nat, +c2: Nat) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case Con{row, more}:
      match row:
        case Row{w, gs}:
          match k:
            case 0n:
              Bool.or(not_cont(w), blank_to(gs, Some{c2}))
            case 1n+m:
              Bool.or(not_cont(w), Bool.and(blank_to(gs, None{}), rest_blank(more, m, c2)))

# the piece of row i: its glyphs from the one that reaches column `from`
# to the last that starts at or before `to`, the trailing blanks dropped
# when the row ends its line of the copy (rest_blank), after a newline
# unless it is the first or continues the row above
def piece(row: Row, i: Nat, +from: Maybe<&2, Nat>, +to: Maybe<&2, Nat>, +trim: Bool, first: Bool) -> Piece:
  match row:
    case Row{w, +gs}:
      +lo = row_lo(gs, 0n, 0n, from)
      +nb = row_nb(gs, 0n, 0n, to, trim)
      Piece{i, lo, max.pick(Nat.is_le(lo, nb), lo, nb), Bool.and(Bool.not(first), not_cont(w))}

# rows i on, k rows before the last; from: the first row's start column,
# c2 the last row's end column
def copy.go(rows: List<&2, Row>, +i: Nat, k: Nat, from: Maybe<&2, Nat>, +c2: Nat, first: Bool) -> List<&2, Piece>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{row, +rest}:
      match k:
        case 0n:
          [piece(row, i, from, Some{c2}, True{}, first)]
        case 1n++m:
          piece(row, i, from, None{}, rest_blank(rest, m, c2), first) <> copy.go(rest, 1n+i, m, None{}, c2, False{})

def copy.rows(below: Bool, rows: List<&2, Row>, k: Nat, c1: Nat, c2: Nat) -> List<&2, Piece>:
  match below:
    case True{}:
      Nil{}
    case False{}:
      copy.go(rows, 0n, k, Some{c1}, c2, True{})

# the pieces of range r over rows (rows[0] is the range's first row)
def copy(r: Rng, rows: List<&2, Row>) -> List<&2, Piece>:
  match r:
    case Rng{s, e}:
      match s:
        case Cell{+r1, c1}:
          match e:
            case Cell{+r2, c2}:
              copy.rows(Nat.is_lt(r2, r1), rows, Nat.sub(r2, r1), c1, c2)

# Releases
# --------

def copied(+r: Rng, last: Maybe<&2, Click>, rows: List<&2, Row>) -> Res:
  Res{St{Shown{r}, last}, Out{Some{r}, Some{copy(r, rows)}, PanNone{}, False{}}}

def release(m: Mode, last: Maybe<&2, Click>, rows: List<&2, Row>) -> Res:
  match m:
    case Idle{}:
      quiet(Idle{}, last)
    case Pressed{a}:
      quiet(Idle{}, last)
    case Selecting{a, h}:
      copied(order(a, h), last, rows)
    case Picked{r}:
      copied(r, last, rows)
    case Shown{r}:
      quiet(Shown{r}, last)

# The step
# --------

def step(s: St, e: Ev) -> Res:
  match s:
    case St{m, last}:
      match e:
        case EvPress{at, time, gs}:
          press(last, at, time, gs)
        case EvDrag{at, lo, hi}:
          drag(m, at, lo, hi)
        case EvRelease{rows}:
          release(m, last, rows)
        case EvKey{}:
          cleared(False{})
        case EvEsc{}:
          cleared(seen(m))
        case EvWheel{}:
          cleared(False{})
        case EvChanged{}:
          cleared(False{})
