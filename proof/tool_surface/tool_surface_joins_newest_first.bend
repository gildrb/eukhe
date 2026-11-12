# eukhe: the proof of LAW tool_surface_joins_newest_first
# Each join puts its tool in front, so the joins of ts from d give
# List.reverse.go(ts, d) (tsj.all, by induction on ts); that is the
# reverse of ts in front of d (tsj.go, by induction with append's
# associativity).

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tool_surface.bend as ToolSurface
import ../base/list.bend as LList

# reverse.go puts its list, last first, in front of acc
def tsj.go(xs: List<&2, Nat>, +acc: List<&2, Nat>) -> {List.reverse.go(&2, Nat, xs, acc) == List.append(&2, Nat, List.reverse.go(&2, Nat, xs, Nil{}), acc) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %Equal.sym(List<&2, Nat>, List.reverse.go(&2, Nat, t, h <> acc), List.append(&2, Nat, List.reverse.go(&2, Nat, t, Nil{}), h <> acc), tsj.go(t, h <> acc)) : {_ == List.append(&2, Nat, List.reverse.go(&2, Nat, t, [h]), acc) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, List.reverse.go(&2, Nat, t, [h]), List.append(&2, Nat, List.reverse.go(&2, Nat, t, Nil{}), [h]), tsj.go(t, [h])) : {List.append(&2, Nat, List.reverse.go(&2, Nat, t, Nil{}), h <> acc) == List.append(&2, Nat, _, acc) : List<&2, Nat>}
      Equal.sym(List<&2, Nat>, List.append(&2, Nat, List.append(&2, Nat, List.reverse.go(&2, Nat, t, Nil{}), [h]), acc), List.append(&2, Nat, List.reverse.go(&2, Nat, t, Nil{}), h <> acc), LList.cb_app_assoc(Nat, List.reverse.go(&2, Nat, t, Nil{}), [h], acc))

# the joins of ts from the dynamic tools d leave ts, last first, in front
# of d
def tsj.all(ts: List<&2, Nat>, +r: List<&2, Nat>, +d: List<&2, Nat>, +x: List<&2, List<&2, Nat>>) -> {Tl.Sess.dyn(ToolSurface.ts_join_all(ts, Tl.Sess{r, d, x})) == List.reverse.go(&2, Nat, ts, d) : List<&2, Nat>}:
  match ts:
    case Nil{}:
      {==}
    case t <> rest:
      tsj.all(rest, r, t <> d, x)

def ToolSurface.tool_surface_joins_newest_first(ts, r, d, x):
  Equal.trans(List<&2, Nat>, Tl.Sess.dyn(ToolSurface.ts_join_all(ts, Tl.Sess{r, d, x})), List.reverse.go(&2, Nat, ts, d), List.append(&2, Nat, List.reverse(&2, Nat, ts), d), tsj.all(ts, r, d, x), tsj.go(ts, d))
