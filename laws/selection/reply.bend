# eukhe: the laws of area selection: the stepper's whole reply
#
# laws/selection.bend pins the model's step and the entry's codec; the
# laws here close what it left open about the reply Rust reads: which
# pieces spell a copy (sel_release_copies pins only the text they spell,
# so an extra empty piece, a piece split in two or a backward piece
# passed), and which error text the stepper answers to an input that is no
# event. The spec helpers below never call the code.

import Base
import ../../bend/selection.bend as M
import ../../bend/ffi_selection.bend as F
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase
import ../selection.bend as Selection

# The pieces of a copy
# --------------------

# a piece of a copy, its glyphs left out: its release row, its first
# glyph, the newline before it, and that it runs forward (from <= to)
type SlFrame is Data:
  SlFrame{row: Nat, from: Nat, nl: Bool, fwd: Bool}

def sl_frame(p: M.Piece) -> SlFrame:
  match p:
    case M.Piece{row, +from, to, nl}:
      SlFrame{row, from, nl, Nat.is_le(from, to)}

def sl_frame_list(ps: List<&2, M.Piece>) -> List<&2, SlFrame>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, rest}:
      sl_frame(p) <> sl_frame_list(rest)

def sl_frames.m(c: Maybe<&2, List<&2, M.Piece>>) -> Maybe<&2, List<&2, SlFrame>>:
  match c:
    case None{}:
      None{}
    case Some{ps}:
      Some{sl_frame_list(ps)}

# the pieces of an answer's copy, framed
def sl_frames(r: M.Res) -> Maybe<&2, List<&2, SlFrame>>:
  match r:
    case M.Res{s, o}:
      match o:
        case M.Out{sel, c, p, e}:
          sl_frames.m(c)

def sl_first.k(on: Bool, j: Nat, more: Nat) -> Nat:
  match on:
    case True{}:
      j
    case False{}:
      more

# the index of the first glyph of a row (gs from column c and index j on)
# whose last cell is at or past column x; the row's glyph count when none
# is
def sl_first(gs: List<&2, Nat>, +c: Nat, +j: Nat, +x: Nat) -> Nat:
  match gs:
    case Nil{}:
      j
    case Con{+g, rest}:
      sl_first.k(Nat.is_le(x, Selection.sl_last(g, c)), j, sl_first(rest, Selection.sl_next(g, c), 1n+j, x))

# the first glyph a copied row's piece starts at: the first row of the
# copy from the glyph that reaches the range's start column x, every
# later row from its first glyph
def sl_frame_from(i: Nat, gs: List<&2, Nat>, +x: Nat) -> Nat:
  match i:
    case 0n:
      sl_first(gs, 0n, 0n, x)
    case 1n+p:
      0n

# a newline before every copied row but the first, unless the row
# continues the row above
def sl_frame_nl(i: Nat, w: M.Wrap) -> Bool:
  match i:
    case 0n:
      False{}
    case 1n+p:
      Selection.sl_brk(w)

def sl_row_frame(row: M.Row, +i: Nat, +x: Nat) -> SlFrame:
  match row:
    case M.Row{w, gs}:
      SlFrame{i, sl_frame_from(i, gs, x), sl_frame_nl(i, w), True{}}

# the frames of the copied rows from release row i on, k more rows after
# this one: one piece per row, in order
def sl_frame_rows(rows: List<&2, M.Row>, +i: Nat, k: Nat, +x: Nat) -> List<&2, SlFrame>:
  match rows k:
    case Nil{} k:
      Nil{}
    case Con{row, rest} 0n:
      [sl_row_frame(row, i, x)]
    case Con{row, rest} 1n+m:
      sl_row_frame(row, i, x) <> sl_frame_rows(rest, 1n+i, m, x)

def sl_frame_rng.k(below: Bool, rows: List<&2, M.Row>, k: Nat, +x: Nat) -> List<&2, SlFrame>:
  match below:
    case True{}:
      Nil{}
    case False{}:
      sl_frame_rows(rows, 0n, k, x)

# the frames of the copy of range r over the release rows (rows[0] is the
# range's first row): a piece for each row from the range's first row to
# its last, none for a range that ends above its start
def sl_frame_rng(r: M.Rng, rows: List<&2, M.Row>) -> List<&2, SlFrame>:
  match r:
    case M.Rng{a, b}:
      match a:
        case M.Cell{+r1, c1}:
          match b:
            case M.Cell{+r2, c2}:
              sl_frame_rng.k(Nat.is_lt(r2, r1), rows, Nat.sub(r2, r1), c1)

# the frames of what a release copies (as Selection.sl_release_copy)
def sl_release_frames(m: M.Mode, rows: List<&2, M.Row>) -> Maybe<&2, List<&2, SlFrame>>:
  match m:
    case M.Idle{}:
      None{}
    case M.Pressed{a}:
      None{}
    case M.Selecting{+a, +h}:
      Some{sl_frame_rng(Selection.sl_order(a, h), rows)}
    case M.Picked{r}:
      Some{sl_frame_rng(r, rows)}
    case M.Shown{r}:
      None{}

# LAW sel_release_pieces: a release's copy is one piece per copied row
# (from the range's first row to its last, cut at the release rows), in
# order: piece i is release row i, starts at the first glyph that reaches
# the range's start column (row 0) or at the row's first glyph (later
# rows), has a newline before it exactly when it is not the first and does
# not continue the row above, and runs forward; with sel_release_copies
# (the text the pieces spell) this pins every field of every piece
# EXCLUDES: an extra empty piece, a piece split in two or merged with the
#   next, a backward piece (to < from), a piece of another row, a newline
#   flag on an empty piece that the text alone does not show
law sel_release_pieces:
  for +m: M.Mode
  for +last: Maybe<&2, M.Click>
  for +rows: List<&2, M.Row>
  {sl_frames(M.step(M.St{m, last}, M.EvRelease{rows})) == sl_release_frames(m, rows) : Maybe<&2, List<&2, SlFrame>>}

# The error forms
# ---------------

# an event with more input after it: the event, then a char and the rest
type SlLeftOver is Data:
  SlLeftOver{ev: M.Ev, head: Char, tail: String}

def sl_left_ev(w: SlLeftOver) -> M.Ev:
  match w:
    case SlLeftOver{e, h, t}:
      e

def sl_spell_left_over(w: SlLeftOver) -> String:
  match w:
    case SlLeftOver{e, h, t}:
      Selection.sl_spell_ev(e, SCon{h, t})

# the reply of the stepper on a selection
def sl_reply(+s: M.St, +str: String) -> String:
  Pair.snd(F.St, String, F.step(F.Live{s}, str))

# LAW selection_ffi_left_over_exact (compiled core): the stepper answers
# the left-over error form only to a spelled event that fits the wire,
# followed by more input
# EXCLUDES: the left-over text for malformed input
law selection_ffi_left_over_exact:
  for +s: M.St
  for +str: String
  for e: {sl_reply(s, str) == Wr.err("selection: input left over") : String}
  exs w: SlLeftOver
  {str == sl_spell_left_over(w) : String} & {Selection.sl_ev_fits(sl_left_ev(w)) == True{} : Bool}

# LAW selection_ffi_errors (compiled core): every error a live stepper
# answers is the malformed or the left-over error form; with
# selection_ffi_left_over and selection_ffi_left_over_exact, every input
# that spells no event answers exactly "selection: malformed event"
# (selection_ffi_open pins the refused stepper's answer)
# EXCLUDES: another error text, a text that varies with the input
law selection_ffi_errors:
  for +s: M.St
  for +str: String
  for e: {LawsBase.wire_opens_err(sl_reply(s, str)) == True{} : Bool}
  {Bool.or(LawsBase.text_same(sl_reply(s, str), Wr.err("selection: malformed event")), LawsBase.text_same(sl_reply(s, str), Wr.err("selection: input left over"))) == True{} : Bool}
