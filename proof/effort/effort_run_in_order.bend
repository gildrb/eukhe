# eukhe: the proof of LAW effort_run_in_order
# A run of one action is that action; a run of xs ++ ys by induction on xs.

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort/depth.bend as Effort
import ./base.bend as LA

def ro.app(xs: List<&2, Ef.Act>, +ys: List<&2, Ef.Act>, s: Ef.Sess) -> {Ef.run(List.append(&2, Ef.Act, xs, ys), s) == Ef.run(ys, Ef.run(xs, s)) : Ef.Sess}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      ro.app(rest, ys, Ef.act(x, s))

def Effort.effort_run_in_order(a, xs, ys, s):
  ({==}, ro.app(xs, ys, s))
