# eukhe: the proof of LAW sel_esc_spent_when_shown
#
# Every answer the code gives keeps a mode m and shows M.sel(m) (M.quiet,
# M.moved, M.press.go), a released range (M.copied) or nothing with the
# mode idle (M.cleared). Esc is spent when the kept mode is seen (M.seen),
# and a mode is seen exactly when it shows a selection (see.form). A press's
# two drag answers are each of that form (see.pick).

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection
import ./base.bend as LS

# Esc after the answer r is spent as r showed a selection
def see.Spent(r: M.Res) -> Type:
  {M.step(Selection.sl_st(r), M.EvEsc{}) == Selection.sl_cleared(Selection.sl_shows(r)) : M.Res}

# an answer that keeps mode m and shows its selection
def see.form(m: M.Mode, +l: Maybe<&2, M.Click>, +c: Maybe<&2, List<&2, M.Piece>>, +p: M.Pan, +e: Bool) -> see.Spent(M.Res{M.St{m, l}, M.Out{M.sel(m), c, p, e}}):
  match m:
    case M.Idle{}:
      {==}
    case M.Pressed{a}:
      {==}
    case M.Selecting{a, h}:
      {==}
    case M.Picked{r}:
      {==}
    case M.Shown{r}:
      {==}

def see.pick(b: Bool, +x: M.Res, +y: M.Res, hx: see.Spent(x), hy: see.Spent(y)) -> see.Spent(Bool.pick(M.Res, b, x, y)):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a drag's answer
def see.drag(m: M.Mode, +at: M.Cell, +lo: Nat, +hi: Nat) -> see.Spent(M.drag(m, at, lo, hi)):
  match m:
    case M.Idle{}:
      {==}
    case M.Pressed{+a}:
      +h = M.clamp(at, lo, hi)
      +p = M.pan(at, lo, hi)
      see.pick(M.cell_eq(a, h), M.moved(M.Pressed{a}, p), M.moved(M.Selecting{a, h}, p), see.form(M.Pressed{a}, None{}, None{}, p, False{}), see.form(M.Selecting{a, h}, None{}, None{}, p, False{}))
    case M.Selecting{a, x}:
      {==}
    case M.Picked{g}:
      match g:
        case M.Rng{s, e}:
          {==}
    case M.Shown{g}:
      {==}

# a release's answer
def see.release(m: M.Mode, +last: Maybe<&2, M.Click>, +rows: List<&2, M.Row>) -> see.Spent(M.release(m, last, rows)):
  match m:
    case M.Idle{}:
      {==}
    case M.Pressed{a}:
      {==}
    case M.Selecting{a, h}:
      {==}
    case M.Picked{r}:
      {==}
    case M.Shown{r}:
      {==}

def see.step(s: M.St, e: M.Ev) -> see.Spent(M.step(s, e)):
  match s:
    case M.St{m, last}:
      match e:
        case M.EvPress{+at, +time, +gs}:
          +n = M.clicks(last, at, time)
          see.form(M.press.mode(n, at, gs), Some{M.Click{at, time, n}}, None{}, M.PanNone{}, False{})
        case M.EvDrag{at, lo, hi}:
          see.drag(m, at, lo, hi)
        case M.EvRelease{rows}:
          see.release(m, last, rows)
        case M.EvKey{}:
          {==}
        case M.EvEsc{}:
          {==}
        case M.EvWheel{}:
          {==}
        case M.EvChanged{}:
          {==}

def Selection.sel_esc_spent_when_shown(s, e):
  (see.step(s, e), {==})
