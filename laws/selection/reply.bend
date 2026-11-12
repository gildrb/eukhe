# eukhe: the laws of area selection: the stepper's whole reply
#
# laws/selection.bend pins the model's step and the entry's codec; the
# laws here close what it left open about the reply Rust reads: which
# pieces spell a copy (sel_release_copies pins only the text they spell,
# so an extra empty piece, a piece split in two or a backward piece
# passed; A12 of laws/selection.bend), and which error text the stepper
# answers to an input that is no event (A13). The spec helpers below never
# call the code.

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

def sl_before.k(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      1n+n
    case False{}:
      n

# A12: how many glyphs of a row (gs from column c on) end before column x
# (their last cell left of x)
def sl_before(gs: List<&2, Nat>, +c: Nat, +x: Nat) -> Nat:
  match gs:
    case Nil{}:
      0n
    case Con{+g, rest}:
      sl_before.k(Nat.is_lt(Selection.sl_last(g, c), x), sl_before(rest, Selection.sl_next(g, c), x))

# A12: the frames of the copied rows after the first, row i first: each
# from its glyph 0, after a newline unless it continues the row above
def sl_frames_later(rows: List<&2, M.Row>, +i: Nat) -> List<&2, SlFrame>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{row, rest}:
      match row:
        case M.Row{w, gs}:
          SlFrame{i, 0n, Selection.sl_brk(w), True{}} <> sl_frames_later(rest, 1n+i)

# A12: the frames of the copied rows: the first from the glyph after every
# glyph of its row that ends before the start column x, with no newline;
# then the later rows
def sl_frames_first(rows: List<&2, M.Row>, +x: Nat) -> List<&2, SlFrame>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{row, rest}:
      match row:
        case M.Row{w, gs}:
          SlFrame{0n, sl_before(gs, 0n, x), False{}, True{}} <> sl_frames_later(rest, 1n)

# A12: the frames of the copy of a range from r1:c1 to row r2 over the
# release rows (rows[0] is row r1): none when r2 is above r1, else one per
# row of the first 1 + r2 - r1 release rows
def sl_frames_of(+r1: Nat, +c1: Nat, +r2: Nat, rows: List<&2, M.Row>) -> List<&2, SlFrame>:
  Bool.pick(List<&2, SlFrame>, Nat.is_lt(r2, r1), Nil{}, sl_frames_first(List.take(&2, M.Row, rows, 1n+Nat.sub(r2, r1)), c1))

# LAW sel_release_pieces_rows (A12): a release of a selection being made
# (a drag or a picked word or row) whose range runs from r1:c1 to r2:c2
# copies one piece per row among the first 1 + r2 - r1 release rows (none
# when r2 < r1), in order: piece i is release row i and runs forward
# (from <= to); piece 0 has no newline before it and starts at the glyph
# after every glyph of its row that ends before column c1; every later
# piece starts at its row's glyph 0, after a newline unless the row
# continues the row above. With sel_release_copies (the text the pieces
# spell) this pins every field of every piece.
# EXCLUDES: an extra empty piece, a piece split in two or merged with the
#   next, a backward piece (to < from), a piece of another row, a first
#   piece that starts a glyph early or late, a newline flag on an empty
#   piece that the text alone does not show
law sel_release_pieces_rows:
  for +m: M.Mode
  for +last: Maybe<&2, M.Click>
  for +rows: List<&2, M.Row>
  for +r1: Nat
  for +c1: Nat
  for +r2: Nat
  for +c2: Nat
  for held: {Selection.sl_held(m) == True{} : Bool}
  for shown: {Selection.sl_sel(m) == Some{M.Rng{M.Cell{r1, c1}, M.Cell{r2, c2}}} : Maybe<&2, M.Rng>}
  {sl_frames(M.step(M.St{m, last}, M.EvRelease{rows})) == Some{sl_frames_of(r1, c1, r2, rows)} : Maybe<&2, List<&2, SlFrame>>}

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
