# eukhe: the laws of area selection: drags (A8, A9 of laws/selection.bend)
#
# Each law is a claim about the model step bend/selection.bend runs for a
# drag. The spec helpers below never call the code.

import Base
import ../../bend/selection.bend as M
import ../selection.bend as Selection

# Spec helpers
# ------------

# A8: h is the cell at kept on the rows lo..hi on screen: at's column;
# at's row when it is on screen; the first row when at is above it, the
# last when at is below it
def sl_head_for(h: M.Cell, at: M.Cell, +lo: Nat, +hi: Nat) -> Bool:
  match h:
    case M.Cell{+hr, hc}:
      match at:
        case M.Cell{+r, c}:
          Bool.and(Nat.is_eq(hc, c), Bool.and(Bool.or(Bool.not(Nat.is_lt(r, lo)), Nat.is_eq(hr, lo)), Bool.and(Bool.or(Bool.not(Nat.is_lt(hi, r)), Nat.is_eq(hr, hi)), Bool.or(Bool.or(Nat.is_lt(r, lo), Nat.is_lt(hi, r)), Nat.is_eq(hr, r)))))

# A8: the mode a drag whose head is h leaves: a press becomes a selection
# from the pressed cell (none while h is that cell), a selection keeps its
# anchor, a picked word or row anchors at its end away from h (its start
# when h is at or after it, else its end); idle and a shown selection stay
def sl_dragged(m: M.Mode, +h: M.Cell) -> M.Mode:
  match m:
    case M.Idle{}:
      M.Idle{}
    case M.Pressed{+a}:
      Bool.pick(M.Mode, Selection.sl_same(a, h), M.Pressed{a}, M.Selecting{a, h})
    case M.Selecting{a, x}:
      M.Selecting{a, h}
    case M.Picked{r}:
      match r:
        case M.Rng{+s, +e}:
          M.Selecting{Bool.pick(M.Cell, Selection.sl_le(s, h), s, e), h}
    case M.Shown{r}:
      M.Shown{r}

# Laws
# ----

# LAW sel_drag_head (A8): for rows lo..hi on screen (lo <= hi), a drag
# leaves the mode sl_dragged gives for some head h that is the drag's cell
# kept on screen (sl_head_for): the anchor kept, a picked word or row
# anchored at its end away from h, idle and a shown selection unchanged
# EXCLUDES: a head on a row off screen (the dock's rows) or in another
#   column, a head not at the drag's cell when that cell is on screen, a
#   moved anchor, a picked word anchored at the near end, a drag that
#   starts a selection with no press, a drag that changes a shown
#   selection
law sel_drag_head:
  for +m: M.Mode
  for +last: Maybe<&2, M.Click>
  for +at: M.Cell
  for +lo: Nat
  for +hi: Nat
  for ok: {Nat.is_le(lo, hi) == True{} : Bool}
  exs h: M.Cell
  {sl_head_for(h, at, lo, hi) == True{} : Bool} & {Selection.sl_mode(M.step(M.St{m, last}, M.EvDrag{at, lo, hi})) == sl_dragged(m, h) : M.Mode}

# LAW sel_drag_answers (A8): a drag's answer keeps its mode with the last
# press forgotten, shows that mode's selection, copies nothing and is not
# spent
# EXCLUDES: a drag that copies, a drag that keeps the last press (a later
#   press read as a double click), a shown range other than the mode's
law sel_drag_answers:
  for +m: M.Mode
  for +last: Maybe<&2, M.Click>
  for +at: M.Cell
  for +lo: Nat
  for +hi: Nat
  {M.step(M.St{m, last}, M.EvDrag{at, lo, hi}) == Selection.sl_moved(Selection.sl_mode(M.step(M.St{m, last}, M.EvDrag{at, lo, hi})), Selection.sl_pan_of(M.step(M.St{m, last}, M.EvDrag{at, lo, hi}))) : M.Res}

# LAW sel_drag_scrolls_up (A9): a drag above the first row on screen while
# a selection is being made asks for one step up
# EXCLUDES: no scroll past the top edge, a scroll the wrong way
law sel_drag_scrolls_up:
  for +m: M.Mode
  for +last: Maybe<&2, M.Click>
  for +r: Nat
  for +c: Nat
  for +lo: Nat
  for +hi: Nat
  for held: {Selection.sl_held(m) == True{} : Bool}
  for above: {Nat.is_lt(r, lo) == True{} : Bool}
  {Selection.sl_pan_of(M.step(M.St{m, last}, M.EvDrag{M.Cell{r, c}, lo, hi})) == M.PanUp{} : M.Pan}

# LAW sel_drag_scrolls_down (A9): a drag below the last row on screen
# (lo <= hi) while a selection is being made asks for one step down
# EXCLUDES: no scroll past the bottom edge, a scroll the wrong way
law sel_drag_scrolls_down:
  for +m: M.Mode
  for +last: Maybe<&2, M.Click>
  for +r: Nat
  for +c: Nat
  for +lo: Nat
  for +hi: Nat
  for held: {Selection.sl_held(m) == True{} : Bool}
  for ok: {Nat.is_le(lo, hi) == True{} : Bool}
  for below: {Nat.is_lt(hi, r) == True{} : Bool}
  {Selection.sl_pan_of(M.step(M.St{m, last}, M.EvDrag{M.Cell{r, c}, lo, hi})) == M.PanDown{} : M.Pan}

# LAW sel_drag_scrolls_none (A9): a drag on a row on screen, or with no
# selection being made, asks for no scroll
# EXCLUDES: a scroll inside the transcript, a scroll with no press or over
#   a shown selection
law sel_drag_scrolls_none:
  for +m: M.Mode
  for +last: Maybe<&2, M.Click>
  for +r: Nat
  for +c: Nat
  for +lo: Nat
  for +hi: Nat
  for still: {Bool.and(Selection.sl_held(m), Bool.or(Nat.is_lt(r, lo), Nat.is_lt(hi, r))) == False{} : Bool}
  {Selection.sl_pan_of(M.step(M.St{m, last}, M.EvDrag{M.Cell{r, c}, lo, hi})) == M.PanNone{} : M.Pan}
