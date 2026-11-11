# eukhe: the proof of LAW tui_paints_bound
# A role has a color in the table exactly when its index is below the
# table's length (pb.has, induction on the table); then induction on the
# roles.

import Base
import ../../bend/color.bend as Co
import ../../bend/tui_color.bend as TC
import ../../laws/tui_color.bend as TuiColor

def pb.has(xs: List<&2, Co.Rgb>, r: Nat) -> {Maybe.is_some(&2, Co.Rgb, List.get(&2, Co.Rgb, xs, r)) == Nat.is_lt(r, List.length(&2, Co.Rgb, xs)) : Bool}:
  match xs r:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+j:
      pb.has(t, j)

def TuiColor.tui_paints_bound(xs, rs):
  match rs:
    case Nil{}:
      {==}
    case Con{+r, rest}:
      %TuiColor.tui_paints_bound(xs, rest) : {Bool.and(Maybe.is_some(&2, Co.Rgb, List.get(&2, Co.Rgb, xs, r)), TC.paints(xs, rest)) == Bool.and(Nat.is_lt(r, List.length(&2, Co.Rgb, xs)), _) : Bool}
      %pb.has(xs, r) : {Bool.and(Maybe.is_some(&2, Co.Rgb, List.get(&2, Co.Rgb, xs, r)), TC.paints(xs, rest)) == Bool.and(_, TC.paints(xs, rest)) : Bool}
      {==}
