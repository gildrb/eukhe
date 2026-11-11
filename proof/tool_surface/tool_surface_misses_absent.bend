# eukhe: the proof of LAW tool_surface_misses_absent
# By induction on the dynamic tools: with no copy of t, no head is t (a
# head that is t counts one), and the rest holds none.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tool_surface.bend as ToolSurface
import ./base.bend as LATs

# a head y with test b, then the rest (ih: the rest misses t)
def tsm.head(b: Bool, +y: Nat, -rest: List<&2, Nat>, +t: Nat, +e: {Nat.is_eq(y, t) == b : Bool}, none: {Nat.add(ToolSurface.ts_one(Nat.is_eq(y, t)), ToolSurface.ts_count(rest, t)) == 0n : Nat}, ih: {ToolSurface.ts_count(rest, t) == 0n : Nat} -> {Tl.elem(rest, t) == False{} : Bool}) -> {Bool.or(Nat.is_eq(y, t), Tl.elem(rest, t)) == False{} : Bool}:
  match b:
    case True{}:
      LATs.ts.succ_zero(ToolSurface.ts_count(rest, t), {Bool.or(Nat.is_eq(y, t), Tl.elem(rest, t)) == False{} : Bool}, LATs.ts.zero_tail(y, t, rest, True{}, e, none))
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(y, t), False{}, e) : {Bool.or(_, Tl.elem(rest, t)) == False{} : Bool}
      ih(LATs.ts.zero_tail(y, t, rest, False{}, e, none))

def tsm.miss(xs: List<&2, Nat>, +t: Nat, none: {ToolSurface.ts_count(xs, t) == 0n : Nat}) -> {Tl.elem(xs, t) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +rest:
      tsm.head(Nat.is_eq(y, t), y, rest, t, {==}, none, k => tsm.miss(rest, t, k))

def ToolSurface.tool_surface_misses_absent(r, d, x, t, none):
  tsm.miss(d, t, none)
