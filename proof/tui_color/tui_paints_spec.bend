# eukhe: the proof of LAW tui_paints_spec: per role, the model's lookup
# is the spec's (tp.has, induction on the table); then induction on the
# roles

import Base
import ../../bend/color.bend as Co
import ../../bend/tui_color.bend as TC
import ../../laws/tui_color.bend as TuiColor

def tp.has(xs: List<&2, Co.Rgb>, r: Nat) -> {Maybe.is_some(&2, Co.Rgb, List.get(&2, Co.Rgb, xs, r)) == TuiColor.tc_has(xs, r) : Bool}:
  match xs r:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+k:
      tp.has(t, k)

def TuiColor.tui_paints_spec(xs, rs):
  match rs:
    case Nil{}:
      {==}
    case Con{+r, rest}:
      %TuiColor.tui_paints_spec(xs, rest) : {Bool.and(Maybe.is_some(&2, Co.Rgb, List.get(&2, Co.Rgb, xs, r)), TC.paints(xs, rest)) == Bool.and(TuiColor.tc_has(xs, r), _) : Bool}
      %tp.has(xs, r) : {Bool.and(Maybe.is_some(&2, Co.Rgb, List.get(&2, Co.Rgb, xs, r)), TC.paints(xs, rest)) == Bool.and(_, TC.paints(xs, rest)) : Bool}
      {==}
