# eukhe: lemmas shared by the proofs of the drag laws (laws/selection.bend
# A8, A9): a drag's scroll step is M.pan of its cell while a selection is
# being made and none otherwise; Nat order facts.

import Base
import ../../../bend/selection.bend as M
import ../../../laws/selection.bend as Selection
import ../base.bend as LS

# a below b: b is not below a
def sdg.lt_asym(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      LS.ls.absurd({Nat.is_lt(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LS.ls.absurd({Nat.is_lt(0n, 1n+p) == False{} : Bool}, h)
    case 1n+p 1n+q:
      sdg.lt_asym(p, q, h)

# a at most b below c: a below c
def sdg.le_lt(a: Nat, b: Nat, c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n q:
      h2
    case 0n 1n+p 0n:
      LS.ls.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, h2)
    case 0n 1n+p 1n+q:
      {==}
    case 1n+x 0n q:
      LS.ls.absurd({Nat.is_lt(1n+x, q) == True{} : Bool}, h1)
    case 1n+x 1n+p 0n:
      LS.ls.absurd({Nat.is_lt(1n+x, 0n) == True{} : Bool}, h2)
    case 1n+x 1n+p 1n+q:
      sdg.le_lt(x, p, q, h1, h2)

# a or b false: a false
def sdg.or_l(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      LS.ls.absurd_t({True{} == False{} : Bool}, e)
    case False{}:
      {==}

def sdg.or_r(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      LS.ls.absurd_t({b == False{} : Bool}, e)
    case False{}:
      e

# a press's two answers to a drag share their scroll step
def sdg.pick(b: Bool, +a: M.Cell, +h: M.Cell, +p: M.Pan) -> {Selection.sl_pan_of(Bool.pick(M.Res, b, M.moved(M.Pressed{a}, p), M.moved(M.Selecting{a, h}, p))) == p : M.Pan}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# while a selection is being made, a drag's scroll step is M.pan of its cell
def sdg.held(m: M.Mode, +last: Maybe<&2, M.Click>, +at: M.Cell, +lo: Nat, +hi: Nat, held: {Selection.sl_held(m) == True{} : Bool}) -> {Selection.sl_pan_of(M.step(M.St{m, last}, M.EvDrag{at, lo, hi})) == M.pan(at, lo, hi) : M.Pan}:
  match m:
    case M.Idle{}:
      LS.ls.absurd({Selection.sl_pan_of(M.step(M.St{M.Idle{}, last}, M.EvDrag{at, lo, hi})) == M.pan(at, lo, hi) : M.Pan}, held)
    case M.Pressed{+a}:
      sdg.pick(M.cell_eq(a, M.clamp(at, lo, hi)), a, M.clamp(at, lo, hi), M.pan(at, lo, hi))
    case M.Selecting{a, h}:
      {==}
    case M.Picked{r}:
      match r:
        case M.Rng{s, e}:
          {==}
    case M.Shown{r}:
      LS.ls.absurd({Selection.sl_pan_of(M.step(M.St{M.Shown{r}, last}, M.EvDrag{at, lo, hi})) == M.pan(at, lo, hi) : M.Pan}, held)
