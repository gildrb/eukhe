# eukhe: the proof of LAW bind_absent_runs_nothing
# Bind by bind: each is of another key (LE.ex.miss), so the lookup goes on;
# past the last one there is nothing to run.

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/entry.bend as CvarEntry
import ./base.bend as LA
import ./base/expand.bend as LE

def CvarEntry.bind_absent_runs_nothing(bs, k, as, none):
  match bs:
    case Nil{}:
      {==}
    case Cv.KeyBind{+j, +c} <> +rest:
      %LE.ex.miss(Nat.is_eq(j, k), LA.cvar.pv.and_l(Bool.not(Nat.is_eq(j, k)), CvarEntry.spec_no_bind(rest, k), none)) : {Cv.expand(Cv.bound.go(Cv.KeyBind{j, c} <> rest, k, _), as) == Cv.Flat{Nil{}} : Cv.Exp}
      CvarEntry.bind_absent_runs_nothing(rest, k, as, LA.cvar.pv.and_r(Bool.not(Nat.is_eq(j, k)), CvarEntry.spec_no_bind(rest, k), none))
