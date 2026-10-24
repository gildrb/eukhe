# eukhe: the laws of area selection

import Base
import ../bend/selection.bend as M
import ../bend/ffi_selection.bend as F
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- selection ----

# LAWS: the fullscreen chat selects and copies text itself (the terminal
# gives every press, drag and release to eukhe). Each law is a claim about
# the stepper eukhe runs (bend/ffi_selection.bend) or the model step it
# runs (bend/selection.bend `step`); PROOF.bend proves them (as
# Selection.<law>) with the lemmas of proof/selection/. The spec helpers
# below never call the code.

# Terms
# -----

# a token of the copied text: glyph ix of release row `row`, or a newline
type SlTok is Data:
  SlG{row: Nat, ix: Nat}
  SlNl{}

# glyph ix of a row, and its code (0 a blank)
type SlGl is Data:
  SlGl{ix: Nat, g: Nat}

# a run of non-blank glyphs: its first and last columns
type SlRun is Data:
  SlRun{s: Nat, e: Nat}

# a at or before b in reading order (row first, then column)
def sl_le(a: M.Cell, b: M.Cell) -> Bool:
  match a:
    case M.Cell{+ar, ac}:
      match b:
        case M.Cell{+br, bc}:
          Bool.or(Nat.is_lt(ar, br), Bool.and(Nat.is_eq(ar, br), Nat.is_le(ac, bc)))

def sl_same(a: M.Cell, b: M.Cell) -> Bool:
  match a:
    case M.Cell{ar, ac}:
      match b:
        case M.Cell{br, bc}:
          Bool.and(Nat.is_eq(ar, br), Nat.is_eq(ac, bc))

# the cells between a and b, the earlier first
def sl_order(+a: M.Cell, +b: M.Cell) -> M.Rng:
  Bool.pick(M.Rng, sl_le(a, b), M.Rng{a, b}, M.Rng{b, a})

def sl_row_of(c: M.Cell) -> Nat:
  match c:
    case M.Cell{r, k}:
      r

# the last cell of glyph g at column c: a blank is one cell, w >= 1 is w
def sl_last(g: Nat, +c: Nat) -> Nat:
  match g:
    case 0n:
      c
    case 1n+p:
      Nat.add(p, c)

def sl_next(g: Nat, c: Nat) -> Nat:
  1n+sl_last(g, c)

# The copied text
# ---------------

def sl_pick.k(on: Bool, x: SlGl, more: List<&2, SlGl>) -> List<&2, SlGl>:
  match on:
    case True{}:
      x <> more
    case False{}:
      more

# the glyphs of row R (gs from column c and index j on) with a cell
# between a and b in reading order
def sl_pick(gs: List<&2, Nat>, +c: Nat, +j: Nat, +R: Nat, +a: M.Cell, +b: M.Cell) -> List<&2, SlGl>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{+g, rest}:
      sl_pick.k(Bool.and(sl_le(M.Cell{R, c}, b), sl_le(a, M.Cell{R, sl_last(g, c)})), SlGl{j, g}, sl_pick(rest, sl_next(g, c), 1n+j, R, a, b))

def sl_keep.k(r: List<&2, SlGl>, t: Bool, x: SlGl) -> List<&2, SlGl>:
  match r:
    case Nil{}:
      match t:
        case False{}:
          [x]
        case True{}:
          match x:
            case SlGl{i, g}:
              match g:
                case 0n:
                  Nil{}
                case 1n+p:
                  [SlGl{i, 1n+p}]
    case Con{y, ys}:
      x <> y <> ys

# xs, its trailing blanks dropped when t
def sl_keep(xs: List<&2, SlGl>, +t: Bool) -> List<&2, SlGl>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      sl_keep.k(sl_keep(rest, t), t, x)

def sl_toks(xs: List<&2, SlGl>, +i: Nat) -> List<&2, SlTok>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      match x:
        case SlGl{j, g}:
          SlG{i, j} <> sl_toks(rest, i)

# a row of this wrap starts a line of its own (it continues no row)
def sl_brk(w: M.Wrap) -> Bool:
  match w:
    case M.Single{}:
      True{}
    case M.Head{}:
      True{}
    case M.Cont{}:
      False{}

def sl_next_brk(rest: List<&2, M.Row>) -> Bool:
  match rest:
    case Nil{}:
      True{}
    case Con{row, more}:
      match row:
        case M.Row{w, gs}:
          sl_brk(w)

def sl_nl.k(b: Bool) -> List<&2, SlTok>:
  match b:
    case True{}:
      [SlNl{}]
    case False{}:
      Nil{}

# the newline before row i: none before the first, none before a row that
# continues the row above
def sl_nl(i: Nat, w: M.Wrap) -> List<&2, SlTok>:
  match i:
    case 0n:
      Nil{}
    case 1n+p:
      sl_nl.k(sl_brk(w))

# row i (row id R) of the copy from a to b; ends: the row ends a line of
# the copy (the last row, or the next does not continue it)
def sl_row(row: M.Row, +i: Nat, R: Nat, a: M.Cell, b: M.Cell, ends: Bool) -> List<&2, SlTok>:
  match row:
    case M.Row{w, gs}:
      List.append(&2, SlTok, sl_nl(i, w), sl_toks(sl_keep(sl_pick(gs, 0n, 0n, R, a, b), ends), i))

def sl_rows.k(on: Bool, here: List<&2, SlTok>, more: List<&2, SlTok>) -> List<&2, SlTok>:
  match on:
    case True{}:
      List.append(&2, SlTok, here, more)
    case False{}:
      Nil{}

# rows i on (rows[0] is row a's row): each row up to b's row
def sl_rows(rows: List<&2, M.Row>, +i: Nat, +a: M.Cell, +b: M.Cell) -> List<&2, SlTok>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{row, +rest}:
      +R = Nat.add(i, sl_row_of(a))
      sl_rows.k(Nat.is_le(R, sl_row_of(b)), sl_row(row, i, R, a, b, Bool.or(Nat.is_eq(R, sl_row_of(b)), sl_next_brk(rest))), sl_rows(rest, 1n+i, a, b))

# the text a range copies over the release rows: in reading order every
# glyph with a cell in the range (a wide glyph once), rows joined by a
# newline unless a row continues the row above, a line's trailing blanks
# dropped
def sl_copy(r: M.Rng, rows: List<&2, M.Row>) -> List<&2, SlTok>:
  match r:
    case M.Rng{a, b}:
      sl_rows(rows, 0n, a, b)

# the tokens a list of pieces spells
def sl_span(n: Nat, +row: Nat, +from: Nat) -> List<&2, SlTok>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      SlG{row, from} <> sl_span(m, row, 1n+from)

def sl_nltok(nl: Bool) -> List<&2, SlTok>:
  match nl:
    case True{}:
      [SlNl{}]
    case False{}:
      Nil{}

def sl_expand(ps: List<&2, M.Piece>) -> List<&2, SlTok>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, rest}:
      match p:
        case M.Piece{row, +from, to, nl}:
          List.append(&2, SlTok, sl_nltok(nl), List.append(&2, SlTok, sl_span(Nat.sub(to, from), row, from), sl_expand(rest)))

def sl_copied.m(c: Maybe<&2, List<&2, M.Piece>>) -> Maybe<&2, List<&2, SlTok>>:
  match c:
    case None{}:
      None{}
    case Some{ps}:
      Some{sl_expand(ps)}

# the text an answer copies
def sl_copied(r: M.Res) -> Maybe<&2, List<&2, SlTok>>:
  match r:
    case M.Res{s, o}:
      match o:
        case M.Out{sel, c, p, e}:
          sl_copied.m(c)

# an answer with its copy left out
def sl_uncopied(r: M.Res) -> M.Res:
  match r:
    case M.Res{s, o}:
      match o:
        case M.Out{sel, c, p, e}:
          M.Res{s, M.Out{sel, None{}, p, e}}

def sl_nls(xs: List<&2, SlTok>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, rest}:
      match x:
        case SlG{r, i}:
          sl_nls(rest)
        case SlNl{}:
          1n+sl_nls(rest)

def sl_copied_nls(m: Maybe<&2, List<&2, SlTok>>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{xs}:
      sl_nls(xs)

def sl_all_cont(rows: List<&2, M.Row>) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case Con{row, rest}:
      match row:
        case M.Row{w, gs}:
          Bool.and(Bool.not(sl_brk(w)), sl_all_cont(rest))

# States and answers
# ------------------

def sl_sel(m: M.Mode) -> Maybe<&2, M.Rng>:
  match m:
    case M.Idle{}:
      None{}
    case M.Pressed{a}:
      None{}
    case M.Selecting{a, h}:
      Some{sl_order(a, h)}
    case M.Picked{r}:
      Some{r}
    case M.Shown{r}:
      Some{r}

# the answer that keeps mode m, copies nothing and scrolls nothing
def sl_quiet(+m: M.Mode, last: Maybe<&2, M.Click>) -> M.Res:
  M.Res{M.St{m, last}, M.Out{sl_sel(m), None{}, M.PanNone{}, False{}}}

# everything cleared; eat: the input is spent
def sl_cleared(eat: Bool) -> M.Res:
  M.Res{M.St{M.Idle{}, None{}}, M.Out{None{}, None{}, M.PanNone{}, eat}}

def sl_seen(m: M.Mode) -> Bool:
  match m:
    case M.Idle{}:
      False{}
    case M.Pressed{a}:
      False{}
    case M.Selecting{a, h}:
      True{}
    case M.Picked{r}:
      True{}
    case M.Shown{r}:
      True{}

# Presses
# -------

# a press at `at`, time t, counts on from the last press: the same cell,
# at most 400 ms later, and the last counted one or two presses
def sl_counts_on(last: Maybe<&2, M.Click>, +at: M.Cell, +t: Nat) -> Bool:
  match last:
    case None{}:
      False{}
    case Some{k}:
      match k:
        case M.Click{a, +t1, +n}:
          Bool.and(Bool.and(sl_same(a, at), Bool.and(Nat.is_le(t1, t), Nat.is_le(Nat.sub(t, t1), 400n))), Bool.or(Nat.is_eq(n, 1n), Nat.is_eq(n, 2n)))

def sl_close(cur: Maybe<&2, SlRun>) -> List<&2, SlRun>:
  match cur:
    case None{}:
      Nil{}
    case Some{r}:
      [r]

def sl_grow(cur: Maybe<&2, SlRun>, c: Nat, e: Nat) -> SlRun:
  match cur:
    case None{}:
      SlRun{c, e}
    case Some{r}:
      match r:
        case SlRun{s, x}:
          SlRun{s, e}

# the runs of non-blank glyphs of gs from column c on; cur: the run open
# at c
def sl_runs(gs: List<&2, Nat>, +c: Nat, cur: Maybe<&2, SlRun>) -> List<&2, SlRun>:
  match gs:
    case Nil{}:
      sl_close(cur)
    case Con{g, rest}:
      match g:
        case 0n:
          List.append(&2, SlRun, sl_close(cur), sl_runs(rest, 1n+c, None{}))
        case 1n+p:
          +e = Nat.add(p, c)
          sl_runs(rest, 1n+e, Some{sl_grow(cur, c, e)})

def sl_find.k(on: Bool, r: SlRun, more: Maybe<&2, SlRun>) -> Maybe<&2, SlRun>:
  match on:
    case True{}:
      Some{r}
    case False{}:
      more

# the run that covers column x
def sl_find(runs: List<&2, SlRun>, +x: Nat) -> Maybe<&2, SlRun>:
  match runs:
    case Nil{}:
      None{}
    case Con{r, rest}:
      match r:
        case SlRun{+s, +e}:
          sl_find.k(Bool.and(Nat.is_le(s, x), Nat.is_le(x, e)), SlRun{s, e}, sl_find(rest, x))

def sl_word.k(m: Maybe<&2, SlRun>, +r: Nat) -> Maybe<&2, M.Rng>:
  match m:
    case None{}:
      None{}
    case Some{w}:
      match w:
        case SlRun{s, e}:
          Some{M.Rng{M.Cell{r, s}, M.Cell{r, e}}}

# the word at a cell: the run of non-blank glyphs of its row that covers
# its column (none on a blank or past the row's end)
def sl_word(gs: List<&2, Nat>, at: M.Cell) -> Maybe<&2, M.Rng>:
  match at:
    case M.Cell{r, x}:
      sl_word.k(sl_find(sl_runs(gs, 0n, None{}), x), r)

# the cells a row's glyphs fill
def sl_width(gs: List<&2, Nat>) -> Nat:
  match gs:
    case Nil{}:
      0n
    case Con{g, rest}:
      match g:
        case 0n:
          1n+sl_width(rest)
        case 1n+p:
          Nat.add(1n+p, sl_width(rest))

def sl_line.k(w: Nat, +r: Nat) -> Maybe<&2, M.Rng>:
  match w:
    case 0n:
      None{}
    case 1n+p:
      Some{M.Rng{M.Cell{r, 0n}, M.Cell{r, p}}}

# the row at a cell: its first to its last filled cell (none when empty)
def sl_line(gs: List<&2, Nat>, at: M.Cell) -> Maybe<&2, M.Rng>:
  match at:
    case M.Cell{r, x}:
      sl_line.k(sl_width(gs), r)

# the answer to a press counted n that picks `pick` (none: no selection)
def sl_pressed(pick: Maybe<&2, M.Rng>, +at: M.Cell, t: Nat, n: Nat) -> M.Res:
  match pick:
    case None{}:
      M.Res{M.St{M.Pressed{at}, Some{M.Click{at, t, n}}}, M.Out{None{}, None{}, M.PanNone{}, False{}}}
    case Some{+r}:
      M.Res{M.St{M.Picked{r}, Some{M.Click{at, t, n}}}, M.Out{Some{r}, None{}, M.PanNone{}, False{}}}

# Drags
# -----

# a drag's cell with its row kept within the rows lo..hi on screen
def sl_clamp(at: M.Cell, +lo: Nat, +hi: Nat) -> M.Cell:
  match at:
    case M.Cell{+r, c}:
      M.Cell{Bool.pick(Nat, Nat.is_lt(r, lo), lo, Bool.pick(Nat, Nat.is_lt(hi, r), hi, r)), c}

# one step up past the first row on screen, down past the last, else none
def sl_pan(at: M.Cell, +lo: Nat, +hi: Nat) -> M.Pan:
  match at:
    case M.Cell{+r, c}:
      Bool.pick(M.Pan, Nat.is_lt(r, lo), M.PanUp{}, Bool.pick(M.Pan, Nat.is_lt(hi, r), M.PanDown{}, M.PanNone{}))

def sl_moved(+m: M.Mode, p: M.Pan) -> M.Res:
  M.Res{M.St{m, None{}}, M.Out{sl_sel(m), None{}, p, False{}}}

# a drag: the head moves to the drag's cell kept on screen, the anchor
# stays (a picked word or row anchors at the end away from the head); a
# drag back onto the pressed cell selects nothing; the last press is
# forgotten
def sl_drag(m: M.Mode, +at: M.Cell, +lo: Nat, +hi: Nat) -> M.Res:
  match m:
    case M.Idle{}:
      sl_quiet(M.Idle{}, None{})
    case M.Pressed{+a}:
      +h = sl_clamp(at, lo, hi)
      Bool.pick(M.Res, sl_same(a, h), sl_moved(M.Pressed{a}, sl_pan(at, lo, hi)), sl_moved(M.Selecting{a, h}, sl_pan(at, lo, hi)))
    case M.Selecting{a, h}:
      sl_moved(M.Selecting{a, sl_clamp(at, lo, hi)}, sl_pan(at, lo, hi))
    case M.Picked{r}:
      match r:
        case M.Rng{+s, +e}:
          +h = sl_clamp(at, lo, hi)
          sl_moved(M.Selecting{Bool.pick(M.Cell, sl_le(s, h), s, e), h}, sl_pan(at, lo, hi))
    case M.Shown{r}:
      sl_quiet(M.Shown{r}, None{})

def sl_pan_of(r: M.Res) -> M.Pan:
  match r:
    case M.Res{s, o}:
      match o:
        case M.Out{sel, c, p, e}:
          p

# a drag scrolls only in a selection being made
def sl_drag_pan(m: M.Mode, +at: M.Cell, +lo: Nat, +hi: Nat) -> M.Pan:
  match m:
    case M.Idle{}:
      M.PanNone{}
    case M.Pressed{a}:
      sl_pan(at, lo, hi)
    case M.Selecting{a, h}:
      sl_pan(at, lo, hi)
    case M.Picked{r}:
      sl_pan(at, lo, hi)
    case M.Shown{r}:
      M.PanNone{}

# Releases
# --------

# the state after a release: a selection being made is shown, a press
# with no drag selects nothing
def sl_release(m: M.Mode, last: Maybe<&2, M.Click>) -> M.Res:
  match m:
    case M.Idle{}:
      sl_quiet(M.Idle{}, last)
    case M.Pressed{a}:
      sl_quiet(M.Idle{}, last)
    case M.Selecting{+a, +h}:
      sl_quiet(M.Shown{sl_order(a, h)}, last)
    case M.Picked{r}:
      sl_quiet(M.Shown{r}, last)
    case M.Shown{r}:
      sl_quiet(M.Shown{r}, last)

# what a release copies: the selection being made, over the rows
def sl_release_copy(m: M.Mode, rows: List<&2, M.Row>) -> Maybe<&2, List<&2, SlTok>>:
  match m:
    case M.Idle{}:
      None{}
    case M.Pressed{a}:
      None{}
    case M.Selecting{+a, +h}:
      Some{sl_copy(sl_order(a, h), rows)}
    case M.Picked{r}:
      Some{sl_copy(r, rows)}
    case M.Shown{r}:
      None{}

def sl_st(r: M.Res) -> M.St:
  match r:
    case M.Res{s, o}:
      s

# Laws
# ----

# LAW sel_release_copies: a release shows the selection being made and copies, over the
# release rows, exactly the text sl_copy spells for it (its cells in
# reading order, a wide glyph once, rows joined by a newline unless the
# row continues the row above, a line's trailing blanks dropped); a press
# with no drag, nothing and a shown selection copy nothing
# EXCLUDES: a copy of the wrong cells (off by one, the anchor's or the
#   head's cell left out, a reversed range), a wide glyph copied twice, a
#   newline inside a soft-wrapped line or missing between rows, trailing
#   blanks kept or blanks inside a line dropped, a copy on a plain click,
#   a selection hidden by its release
law sel_release_copies:
  for +m: M.Mode
  for +last: Maybe<&2, M.Click>
  for +rows: List<&2, M.Row>
  {sl_copied(M.step(M.St{m, last}, M.EvRelease{rows})) == sl_release_copy(m, rows) : Maybe<&2, List<&2, SlTok>>} & {sl_uncopied(M.step(M.St{m, last}, M.EvRelease{rows})) == sl_release(m, last) : M.Res}

# LAW sel_copy_anchor_to_head: a press at a, a drag to a cell h on screen other than a, then a
# release copy exactly the cells between a and h in reading order
# EXCLUDES: a drag that loses the anchor, a head taken from the wrong
#   event, a copy of the range the other way round
law sel_copy_anchor_to_head:
  for +m: M.Mode
  for +a: M.Cell
  for +t: Nat
  for +gs: List<&2, Nat>
  for +h: M.Cell
  for +lo: Nat
  for +hi: Nat
  for +rows: List<&2, M.Row>
  for on: {Bool.and(Nat.is_le(lo, sl_row_of(h)), Nat.is_le(sl_row_of(h), hi)) == True{} : Bool}
  for moved: {sl_same(a, h) == False{} : Bool}
  {sl_copied(M.step(sl_st(M.step(sl_st(M.step(M.St{m, None{}}, M.EvPress{a, t, gs})), M.EvDrag{h, lo, hi})), M.EvRelease{rows})) == Some{sl_copy(sl_order(a, h), rows)} : Maybe<&2, List<&2, SlTok>>}

# LAW sel_wrap_joins: a copy over a soft-wrapped block (a row, then rows that each continue
# the row above) holds no newline: the block copies as one line
# EXCLUDES: a newline at a soft wrap (a wrapped URL copied broken)
law sel_wrap_joins:
  for +m: M.Mode
  for +last: Maybe<&2, M.Click>
  for +row: M.Row
  for +conts: List<&2, M.Row>
  for wrapped: {sl_all_cont(conts) == True{} : Bool}
  {sl_copied_nls(sl_copied(M.step(M.St{m, last}, M.EvRelease{row <> conts}))) == 0n : Nat}

# LAW sel_release_copies_once: after a release, another release copies nothing
# EXCLUDES: a second copy of one selection (a stray release report)
law sel_release_copies_once:
  for +s: M.St
  for +rows: List<&2, M.Row>
  for +more: List<&2, M.Row>
  {sl_copied(M.step(sl_st(M.step(s, M.EvRelease{rows})), M.EvRelease{more})) == None{} : Maybe<&2, List<&2, SlTok>>}

# LAW sel_click_copies_nothing: a first press and its release with no drag select and copy
# nothing; the press is kept for a double click
# EXCLUDES: a click that selects or copies a cell, a click forgotten
#   before its second press
law sel_click_copies_nothing:
  for +m: M.Mode
  for +at: M.Cell
  for +t: Nat
  for +gs: List<&2, Nat>
  for +rows: List<&2, M.Row>
  {M.step(sl_st(M.step(M.St{m, None{}}, M.EvPress{at, t, gs})), M.EvRelease{rows}) == M.Res{M.St{M.Idle{}, Some{M.Click{at, t, 1n}}}, M.Out{None{}, None{}, M.PanNone{}, False{}}} : M.Res}

# LAW sel_single_press: a press that does not count on from the last press (another cell,
# more than 400 ms later, an earlier time, or after a triple press)
# starts a selection at its cell and shows none
# EXCLUDES: a word or row picked by two far-apart presses, a fourth press
#   that picks again, a press that keeps the old selection on screen
law sel_single_press:
  for +m: M.Mode
  for +last: Maybe<&2, M.Click>
  for +at: M.Cell
  for +t: Nat
  for +gs: List<&2, Nat>
  for no: {sl_counts_on(last, at, t) == False{} : Bool}
  {M.step(M.St{m, last}, M.EvPress{at, t, gs}) == M.Res{M.St{M.Pressed{at}, Some{M.Click{at, t, 1n}}}, M.Out{None{}, None{}, M.PanNone{}, False{}}} : M.Res}

# LAW sel_word_bounds: a second press on the cell of a first, at most 400 ms later, picks
# the word there: the run of non-blank glyphs that covers the cell (none
# on a blank or past the row's end)
# EXCLUDES: a word cut at a wide glyph or punctuation, a word that takes
#   the blank after it, a word picked on a blank, a wrong row
law sel_word_bounds:
  for +m: M.Mode
  for +at: M.Cell
  for +t1: Nat
  for +t2: Nat
  for +gs: List<&2, Nat>
  for near: {Bool.and(Nat.is_le(t1, t2), Nat.is_le(Nat.sub(t2, t1), 400n)) == True{} : Bool}
  {M.step(M.St{m, Some{M.Click{at, t1, 1n}}}, M.EvPress{at, t2, gs}) == sl_pressed(sl_word(gs, at), at, t2, 2n) : M.Res}

# LAW sel_line_bounds: a third press on the cell, at most 400 ms after the second, picks
# the row: its first to its last filled cell (none on an empty row)
# EXCLUDES: a line cut at a wide glyph, a line past the row's cells, a
#   line of another row
law sel_line_bounds:
  for +m: M.Mode
  for +at: M.Cell
  for +t1: Nat
  for +t2: Nat
  for +gs: List<&2, Nat>
  for near: {Bool.and(Nat.is_le(t1, t2), Nat.is_le(Nat.sub(t2, t1), 400n)) == True{} : Bool}
  {M.step(M.St{m, Some{M.Click{at, t1, 2n}}}, M.EvPress{at, t2, gs}) == sl_pressed(sl_line(gs, at), at, t2, 3n) : M.Res}

# LAW sel_drag_moves_head: a drag moves the head of the selection being made to its cell,
# kept within the rows on screen, and keeps the anchor (sl_drag)
# EXCLUDES: a head on a row off screen (the dock's rows), a moved
#   anchor, a drag that starts a selection with no press, a drag that
#   changes a shown selection
law sel_drag_moves_head:
  for +m: M.Mode
  for +last: Maybe<&2, M.Click>
  for +at: M.Cell
  for +lo: Nat
  for +hi: Nat
  {M.step(M.St{m, last}, M.EvDrag{at, lo, hi}) == sl_drag(m, at, lo, hi) : M.Res}

# LAW sel_scroll_past_edge: a drag asks for one scroll step only past an edge: up above the
# first row on screen, down below the last, none inside; and only while
# a selection is being made
# EXCLUDES: a scroll inside the transcript, a scroll the wrong way, a
#   scroll with no press
law sel_scroll_past_edge:
  for +m: M.Mode
  for +last: Maybe<&2, M.Click>
  for +at: M.Cell
  for +lo: Nat
  for +hi: Nat
  {sl_pan_of(M.step(M.St{m, last}, M.EvDrag{at, lo, hi})) == sl_drag_pan(m, at, lo, hi) : M.Pan}

# LAW sel_key_clears: a key, a wheel notch or a change of the content under the selection
# clears everything, and the input goes on to its own use
# EXCLUDES: a selection left on screen after typing or scrolling, or over
#   changed text; a key swallowed by the selection
law sel_key_clears:
  for +s: M.St
  {M.step(s, M.EvKey{}) == sl_cleared(False{}) : M.Res} & {M.step(s, M.EvWheel{}) == sl_cleared(False{}) : M.Res} & {M.step(s, M.EvChanged{}) == sl_cleared(False{}) : M.Res}

# LAW sel_esc_clears: Esc clears everything, and is spent exactly when a selection was on
# screen
# EXCLUDES: Esc that clears a selection and also aborts the run, Esc
#   swallowed when no selection is shown
law sel_esc_clears:
  for +m: M.Mode
  for +last: Maybe<&2, M.Click>
  {M.step(M.St{m, last}, M.EvEsc{}) == sl_cleared(sl_seen(m)) : M.Res}

# ---- selection entry ----

# Spec spellers (the wire format of bend/ffi_selection.bend, spelled with
# the W primitives; never the entry's own encoders)

def sl_spell_cell(c: M.Cell, rest: String) -> String:
  match c:
    case M.Cell{r, k}:
      Wr.put_nat(r, Wr.put_nat(k, rest))

def sl_spell_gs(gs: List<&2, Nat>, rest: String) -> String:
  Wr.put_list(~Nat, ~Wr.put_nat, gs, rest)

def sl_spell_wrap(w: M.Wrap, rest: String) -> String:
  match w:
    case M.Single{}:
      Wr.put_nat(0n, rest)
    case M.Head{}:
      Wr.put_nat(1n, rest)
    case M.Cont{}:
      Wr.put_nat(2n, rest)

def sl_spell_rows.items(rows: List<&2, M.Row>, rest: String) -> String:
  match rows:
    case Nil{}:
      rest
    case Con{row, more}:
      match row:
        case M.Row{w, gs}:
          sl_spell_wrap(w, sl_spell_gs(gs, sl_spell_rows.items(more, rest)))

def sl_spell_ev(e: M.Ev, rest: String) -> String:
  match e:
    case M.EvPress{at, t, gs}:
      Wr.put_nat(0n, sl_spell_cell(at, Wr.put_nat(t, sl_spell_gs(gs, rest))))
    case M.EvDrag{at, lo, hi}:
      Wr.put_nat(1n, sl_spell_cell(at, Wr.put_nat(lo, Wr.put_nat(hi, rest))))
    case M.EvRelease{+rows}:
      Wr.put_nat(2n, Wr.put_nat(List.length(&2, M.Row, rows), sl_spell_rows.items(rows, rest)))
    case M.EvKey{}:
      Wr.put_nat(3n, rest)
    case M.EvEsc{}:
      Wr.put_nat(4n, rest)
    case M.EvWheel{}:
      Wr.put_nat(5n, rest)
    case M.EvChanged{}:
      Wr.put_nat(6n, rest)

def sl_spell_pieces.items(ps: List<&2, M.Piece>, rest: String) -> String:
  match ps:
    case Nil{}:
      rest
    case Con{p, more}:
      match p:
        case M.Piece{row, from, to, nl}:
          Wr.put_nat(row, Wr.put_nat(from, Wr.put_nat(to, Wr.put_bool(nl, sl_spell_pieces.items(more, rest)))))

def sl_spell_sel(m: Maybe<&2, M.Rng>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{r}:
      match r:
        case M.Rng{a, b}:
          Wr.put_nat(1n, sl_spell_cell(a, sl_spell_cell(b, rest)))

def sl_spell_copy(m: Maybe<&2, List<&2, M.Piece>>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{+ps}:
      Wr.put_nat(1n, Wr.put_nat(List.length(&2, M.Piece, ps), sl_spell_pieces.items(ps, rest)))

def sl_spell_pan(p: M.Pan, rest: String) -> String:
  match p:
    case M.PanNone{}:
      Wr.put_nat(0n, rest)
    case M.PanUp{}:
      Wr.put_nat(1n, rest)
    case M.PanDown{}:
      Wr.put_nat(2n, rest)

# the reply that spells an answer of the model
def sl_spell_reply(r: M.Res) -> String:
  match r:
    case M.Res{s, o}:
      match o:
        case M.Out{sel, c, p, e}:
          sl_spell_sel(sel, sl_spell_copy(c, sl_spell_pan(p, Wr.put_bool(e, ""))))

# the stepper's state after an answer of the model
def sl_live(r: M.Res) -> F.St:
  match r:
    case M.Res{s, o}:
      F.Live{s}

def sl_cell_fits(c: M.Cell) -> Bool:
  match c:
    case M.Cell{r, k}:
      Bool.and(LawsBase.wire_fits(r), LawsBase.wire_fits(k))

def sl_gs_fit(gs: List<&2, Nat>) -> Bool:
  +xs = gs
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))

def sl_rows_fit(rows: List<&2, M.Row>) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case Con{row, more}:
      match row:
        case M.Row{w, gs}:
          Bool.and(sl_gs_fit(gs), sl_rows_fit(more))

# every number of an input fits the wire
def sl_ev_fits(e: M.Ev) -> Bool:
  match e:
    case M.EvPress{at, t, gs}:
      Bool.and(sl_cell_fits(at), Bool.and(LawsBase.wire_fits(t), sl_gs_fit(gs)))
    case M.EvDrag{at, lo, hi}:
      Bool.and(sl_cell_fits(at), Bool.and(LawsBase.wire_fits(lo), LawsBase.wire_fits(hi)))
    case M.EvRelease{+rows}:
      Bool.and(LawsBase.wire_fits(List.length(&2, M.Row, rows)), sl_rows_fit(rows))
    case M.EvKey{}:
      True{}
    case M.EvEsc{}:
      True{}
    case M.EvWheel{}:
      True{}
    case M.EvChanged{}:
      True{}

# LAW selection_ffi_decides (compiled core): the stepper reads a spelled input that fits and
# answers the model's step: the state it keeps and the reply spelling the
# answer
# EXCLUDES: an input field misread, dropped or reordered; a reply field
#   misspelled; a stepper that keeps another state than the model's
law selection_ffi_decides:
  for +s: M.St
  for +e: M.Ev
  for h: {sl_ev_fits(e) == True{} : Bool}
  {F.step(F.Live{s}, sl_spell_ev(e, "")) == (sl_live(M.step(s, e)), sl_spell_reply(M.step(s, e))) : F.St & String}

# LAW selection_ffi_left_over (compiled core): an input followed by more answers the error form and keeps
# the state
# EXCLUDES: a stepper that runs an input followed by garbage, or two
#   inputs sent as one
law selection_ffi_left_over:
  for +s: M.St
  for +e: M.Ev
  for +rest: String
  for h: {sl_ev_fits(e) == True{} : Bool}
  for more: {String.is_empty(rest) == False{} : Bool}
  {F.step(F.Live{s}, sl_spell_ev(e, rest)) == (F.Live{s}, Wr.err("selection: input left over")) : F.St & String}

# LAW selection_ffi_error_keeps_the_state (compiled core): every input the stepper answers with
# the error form (malformed anywhere, a bad tag or wrap in any row, left
# over text) keeps the state it was given
# EXCLUDES: a malformed release that drops the selection being made, so
#   the next Esc is not spent and aborts the run with a selection shown
#   (a blind adversary's gap: a bad wrap tag in the second release row)
law selection_ffi_error_keeps_the_state:
  for +s: M.St
  for +str: String
  for bad: {LawsBase.wire_opens_err(Pair.snd(F.St, String, F.step(F.Live{s}, str))) == True{} : Bool}
  {Pair.fst(F.St, String, F.step(F.Live{s}, str)) == F.Live{s} : F.St}

# LAW selection_ffi_reads_only_events (compiled core): every text the stepper answers with no
# error is the spelling of an input that fits, and the answer is the
# model's step on it
# EXCLUDES: a decoder that accepts another spelling (a default field, a
#   lenient tag, a short list), a decision made on input that is no event
law selection_ffi_reads_only_events:
  for +s: M.St
  for +str: String
  for ok: {LawsBase.wire_opens_err(Pair.snd(F.St, String, F.step(F.Live{s}, str))) == False{} : Bool}
  exs e: M.Ev
  {(str, (sl_ev_fits(e), F.step(F.Live{s}, str))) == (sl_spell_ev(e, ""), (True{}, (sl_live(M.step(s, e)), sl_spell_reply(M.step(s, e))))) : String & (Bool & (F.St & String))}

# LAW selection_ffi_unknown_event (compiled core): an input tag past the seven inputs answers the
# error form and keeps the state
# EXCLUDES: an unknown input read as a known one
law selection_ffi_unknown_event:
  for +s: M.St
  for +n: Nat
  for +rest: String
  {F.step(F.Live{s}, Wr.put_nat(7n+n, rest)) == (F.Live{s}, Wr.err("selection: malformed event")) : F.St & String}

# LAW selection_ffi_unknown_wrap (compiled core): a release whose first row has a wrap tag past
# the three wraps answers the error form and keeps the state
# EXCLUDES: an unknown wrap read as a single row or a continuation
law selection_ffi_unknown_wrap:
  for +s: M.St
  for +k: Nat
  for +n: Nat
  for +rest: String
  {F.step(F.Live{s}, Wr.put_nat(2n, Wr.put_nat(1n+k, Wr.put_nat(3n+n, rest)))) == (F.Live{s}, Wr.err("selection: malformed event")) : F.St & String}

# LAW selection_ffi_open (compiled core): an open with no input selects nothing; any input
# refuses it, and a refused stepper answers every input with the error
# form
# EXCLUDES: an open that starts with a selection or a remembered press, a
#   refused open that later runs inputs
law selection_ffi_open:
  for +c: Char
  for +rest: String
  for +input: String
  {F.open("") == (F.Live{M.St{M.Idle{}, None{}}}, "0,0,0,F") : F.St & String} & {F.open(SCon{c, rest}) == (F.Refused{}, Wr.err("selection: open takes no input")) : F.St & String} & {F.step(F.Refused{}, input) == (F.Refused{}, Wr.err("selection: the open was refused")) : F.St & String}

# LAW selection_ffi_example (compiled core): anchor: the exact text Rust sends and reads: a
# press at row 3 column 3 starts a selection, a drag to column 6 selects
# 3:3..3:6, the release over "ab cd  " copies glyphs 3..5 of row 0 ("cd"),
# and an unknown tag is malformed
# EXCLUDES: a codec in another order than the header's
law selection_ffi_example:
  {F.step(F.Live{M.St{M.Idle{}, None{}}}, "0,3,3,1000,7,1,1,0,1,1,0,0,") == (F.Live{M.St{M.Pressed{M.Cell{3n, 3n}}, Some{M.Click{M.Cell{3n, 3n}, 1000n, 1n}}}}, "0,0,0,F") : F.St & String} & {F.step(F.Live{M.St{M.Pressed{M.Cell{3n, 3n}}, None{}}}, "1,3,6,2,9,") == (F.Live{M.St{M.Selecting{M.Cell{3n, 3n}, M.Cell{3n, 6n}}, None{}}}, "1,3,3,3,6,0,0,F") : F.St & String} & {F.step(F.Live{M.St{M.Selecting{M.Cell{3n, 3n}, M.Cell{3n, 6n}}, None{}}}, "2,1,0,7,1,1,0,1,1,0,0,") == (F.Live{M.St{M.Shown{M.Rng{M.Cell{3n, 3n}, M.Cell{3n, 6n}}}, None{}}}, "1,3,3,3,6,1,1,0,3,5,F0,F") : F.St & String} & {F.step(F.Live{M.St{M.Idle{}, None{}}}, "9,") == (F.Live{M.St{M.Idle{}, None{}}}, "E selection: malformed event") : F.St & String}
