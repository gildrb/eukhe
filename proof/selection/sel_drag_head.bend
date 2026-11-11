# eukhe: the proof of LAW sel_drag_head
#
# The head is the code's clamped cell M.clamp(at, lo, hi). With lo <= hi it
# is the drag's cell kept on screen (sdh.for: a row above lo is not below
# hi, LD.sdg.le_lt and LD.sdg.lt_asym). Per mode the code's answer keeps the
# mode sl_dragged gives for that head: the code's cell order and cell test
# are the spec's (LS.ls.le, LS.ls.same).

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection
import ../../laws/selection/drag.bend as SelectionDrag
import ./base.bend as LS
import ./base/drag.bend as LD

# the clamped cell, for every answer b1 (above lo) and b2 (below hi)
def sdh.for.at(+r: Nat, +c: Nat, +lo: Nat, +hi: Nat, b1: Bool, e1: {Nat.is_lt(r, lo) == b1 : Bool}, b2: Bool, e2: {Nat.is_lt(hi, r) == b2 : Bool}, ok: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Bool.and(Nat.is_eq(c, c), Bool.and(Bool.or(Bool.not(b1), Nat.is_eq(Bool.pick(Nat, b1, lo, Bool.pick(Nat, b2, hi, r)), lo)), Bool.and(Bool.or(Bool.not(b2), Nat.is_eq(Bool.pick(Nat, b1, lo, Bool.pick(Nat, b2, hi, r)), hi)), Bool.or(Bool.or(b1, b2), Nat.is_eq(Bool.pick(Nat, b1, lo, Bool.pick(Nat, b2, hi, r)), r))))) == True{} : Bool}:
  match b1 b2:
    case True{} True{}:
      +na = LD.sdg.lt_asym(r, hi, LS.ls.lt_le(r, lo, hi, e1, ok))
      LS.ls.absurd({Bool.and(Nat.is_eq(c, c), Bool.and(Bool.or(Bool.not(True{}), Nat.is_eq(lo, lo)), Bool.and(Bool.or(Bool.not(True{}), Nat.is_eq(lo, hi)), Bool.or(Bool.or(True{}, True{}), Nat.is_eq(lo, r))))) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(hi, r), True{}, Equal.sym(Bool, Nat.is_lt(hi, r), False{}, na), e2))
    case True{} False{}:
      LS.ls.and_tt(Nat.is_eq(c, c), Bool.and(Nat.is_eq(lo, lo), True{}), LS.ls.eq_refl(c), LS.ls.and_tt(Nat.is_eq(lo, lo), True{}, LS.ls.eq_refl(lo), {==}))
    case False{} True{}:
      LS.ls.and_tt(Nat.is_eq(c, c), Bool.and(Nat.is_eq(hi, hi), True{}), LS.ls.eq_refl(c), LS.ls.and_tt(Nat.is_eq(hi, hi), True{}, LS.ls.eq_refl(hi), {==}))
    case False{} False{}:
      LS.ls.and_tt(Nat.is_eq(c, c), Nat.is_eq(r, r), LS.ls.eq_refl(c), LS.ls.eq_refl(r))

# the code's clamped cell is the drag's cell kept on screen
def sdh.for(at: M.Cell, +lo: Nat, +hi: Nat, ok: {Nat.is_le(lo, hi) == True{} : Bool}) -> {SelectionDrag.sl_head_for(M.clamp(at, lo, hi), at, lo, hi) == True{} : Bool}:
  match at:
    case M.Cell{+r, +c}:
      sdh.for.at(r, c, lo, hi, Nat.is_lt(r, lo), {==}, Nat.is_lt(hi, r), {==}, ok)

# a press's two answers keep the two modes of sl_dragged
def sdh.pick(b: Bool, +a: M.Cell, +h: M.Cell, +p: M.Pan) -> {Selection.sl_mode(Bool.pick(M.Res, b, M.moved(M.Pressed{a}, p), M.moved(M.Selecting{a, h}, p))) == Bool.pick(M.Mode, b, M.Pressed{a}, M.Selecting{a, h}) : M.Mode}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# per mode, the mode the code's answer keeps for the clamped head
def sdh.mode(m: M.Mode, +last: Maybe<&2, M.Click>, +at: M.Cell, +lo: Nat, +hi: Nat) -> {Selection.sl_mode(M.step(M.St{m, last}, M.EvDrag{at, lo, hi})) == SelectionDrag.sl_dragged(m, M.clamp(at, lo, hi)) : M.Mode}:
  match m:
    case M.Idle{}:
      {==}
    case M.Pressed{+a}:
      +h = M.clamp(at, lo, hi)
      %LS.ls.same(a, h) : {Selection.sl_mode(Bool.pick(M.Res, M.cell_eq(a, h), M.moved(M.Pressed{a}, M.pan(at, lo, hi)), M.moved(M.Selecting{a, h}, M.pan(at, lo, hi)))) == Bool.pick(M.Mode, _, M.Pressed{a}, M.Selecting{a, h}) : M.Mode}
      sdh.pick(M.cell_eq(a, h), a, h, M.pan(at, lo, hi))
    case M.Selecting{a, x}:
      {==}
    case M.Picked{g}:
      match g:
        case M.Rng{+s, +e}:
          +h = M.clamp(at, lo, hi)
          %LS.ls.le(s, h) : {M.Selecting{Bool.pick(M.Cell, M.cell_le(s, h), s, e), h} == M.Selecting{Bool.pick(M.Cell, _, s, e), h} : M.Mode}
          {==}
    case M.Shown{g}:
      {==}

def SelectionDrag.sel_drag_head(m, last, at, lo, hi, ok):
  (M.clamp(at, lo, hi), (sdh.for(at, lo, hi, ok), sdh.mode(m, last, at, lo, hi)))
