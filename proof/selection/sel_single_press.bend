# eukhe: the proof of LAW sel_single_press

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection
import ./base.bend as LS

# A press that does not count on counts 1 (ssp.clicks): the model's count
# is 1 unless the press is near the last one and that one counted 1 or 2
# (next(n) is 1 from 3 on); a count of 1 holds the button (Pressed).

def ssp.near(c: Bool, n: Nat, no: {Bool.and(c, Bool.or(Nat.is_eq(n, 1n), Nat.is_eq(n, 2n))) == False{} : Bool}) -> {M.near(c, n) == 1n : Nat}:
  match c:
    case False{}:
      {==}
    case True{}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          match p:
            case 0n:
              LS.ls.absurd_t({M.near(True{}, 1n) == 1n : Nat}, no)
            case 1n+q:
              match q:
                case 0n:
                  LS.ls.absurd_t({M.near(True{}, 2n) == 1n : Nat}, no)
                case 1n+y:
                  {==}

def ssp.clicks(last: Maybe<&2, M.Click>, +at: M.Cell, +t: Nat, no: {Selection.sl_counts_on(last, at, t) == False{} : Bool}) -> {M.clicks(last, at, t) == 1n : Nat}:
  match last:
    case None{}:
      {==}
    case Some{k}:
      match k:
        case M.Click{+a, +t1, +n}:
          %Equal.sym(Bool, M.cell_eq(a, at), Selection.sl_same(a, at), LS.ls.same(a, at)) : {M.near(Bool.and(_, Bool.and(Nat.is_le(t1, t), Nat.is_le(Nat.sub(t, t1), 400n))), n) == 1n : Nat}
          ssp.near(Bool.and(Selection.sl_same(a, at), Bool.and(Nat.is_le(t1, t), Nat.is_le(Nat.sub(t, t1), 400n))), n, no)

def Selection.sel_single_press(m, last, at, t, gs, no):
  %Equal.sym(Nat, M.clicks(last, at, t), 1n, ssp.clicks(last, at, t, no)) : {M.press.go(M.press.mode(_, at, gs), M.Click{at, t, _}) == M.Res{M.St{M.Pressed{at}, Some{M.Click{at, t, 1n}}}, M.Out{None{}, None{}, M.PanNone{}, False{}}} : M.Res}
  {==}
