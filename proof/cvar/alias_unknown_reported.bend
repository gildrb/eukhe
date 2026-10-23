# eukhe: the proof of LAW alias_unknown_reported

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar.bend as Cvar

def pv.gone(k: Nat, +n: Nat, +as: List<&2, Cv.Alias>, +out: List<&2, Cv.Cmd>) -> {Cv.expand.go(k, [Cv.CGone{n}], as, Cv.Flat{out}) == Cv.Unknown{n} : Cv.Exp}:
  match k:
    case 0n:
      {==}
    case 1n+e:
      {==}

def Cvar.alias_unknown_reported(n, as, gone):
  +k = List.length(&2, Cv.Alias, as)
  %Equal.sym(List<&2, Cv.Cmd>, Cv.body(as, n), [Cv.CGone{n}], gone) : {Cv.fin(Cv.expand.go(k, _, as, Cv.Flat{Nil{}})) == Cv.Unknown{n} : Cv.Exp}
  %Equal.sym(Cv.Exp, Cv.expand.go(k, [Cv.CGone{n}], as, Cv.Flat{Nil{}}), Cv.Unknown{n}, pv.gone(k, n, as, Nil{})) : {Cv.fin(_) == Cv.Unknown{n} : Cv.Exp}
  {==}
