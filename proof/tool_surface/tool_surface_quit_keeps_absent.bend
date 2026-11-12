# eukhe: the proof of LAW tool_surface_quit_keeps_absent
# By induction on the dynamic tools: with no copy of t, no head is t
# (a head that is t counts one), so the model's drop keeps each head.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tool_surface.bend as ToolSurface
import ./base.bend as LATs

def tsq.keep(xs: List<&2, Nat>, +t: Nat, hit: Bool, e: {Tl.is.at(xs, t) == hit : Bool}, none: {ToolSurface.ts_count(xs, t) == 0n : Nat}) -> {Tl.drop.go(xs, t, hit) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +rest:
      match hit:
        case True{}:
          LATs.ts.succ_zero(ToolSurface.ts_count(rest, t), {Tl.drop.go(y <> rest, t, True{}) == y <> rest : List<&2, Nat>}, LATs.ts.zero_tail(y, t, rest, True{}, e, none))
        case False{}:
          %Equal.sym(List<&2, Nat>, Tl.drop.go(rest, t, Tl.is.at(rest, t)), rest, tsq.keep(rest, t, Tl.is.at(rest, t), {==}, LATs.ts.zero_tail(y, t, rest, False{}, e, none))) : {y <> _ == y <> rest : List<&2, Nat>}
          {==}

def ToolSurface.tool_surface_quit_keeps_absent(r, d, x, t, none):
  tsq.keep(d, t, Tl.is.at(d, t), {==}, none)
