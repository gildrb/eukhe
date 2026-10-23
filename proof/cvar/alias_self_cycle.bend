# eukhe: the proof of LAW alias_self_cycle

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar.bend as Cvar
import ./base.bend as LA

def pv.self(k: Nat, +n: Nat, +as: List<&2, Cv.Alias>, +out: List<&2, Cv.Cmd>) -> {Cv.expand.go(k, [Cv.CRun{n}], Cv.Alias{n, [Cv.CRun{n}]} <> as, Cv.Flat{out}) == Cv.Cycle{n} : Cv.Exp}:
  match k:
    case 0n:
      {==}
    case 1n+e:
      +t = {Cv.Alias{n, [Cv.CRun{n}]} <> as : List<&2, Cv.Alias>}
      %Equal.sym(List<&2, Cv.Cmd>, Cv.body(t, n), [Cv.CRun{n}], LA.pv.body_head(n, [Cv.CRun{n}], as)) : {Cv.expand.go(e, _, t, Cv.Flat{out}) == Cv.Cycle{n} : Cv.Exp}
      pv.self(e, n, as, out)

def Cvar.alias_self_cycle(n, as):
  +t = {Cv.Alias{n, [Cv.CRun{n}]} <> as : List<&2, Cv.Alias>}
  %Equal.sym(Cv.Exp, Cv.expand.go(1n+List.length(&2, Cv.Alias, t), [Cv.CRun{n}], t, Cv.Flat{Nil{}}), Cv.Cycle{n}, pv.self(1n+List.length(&2, Cv.Alias, t), n, as, Nil{})) : {Cv.fin(_) == Cv.Cycle{n} : Cv.Exp}
  {==}
