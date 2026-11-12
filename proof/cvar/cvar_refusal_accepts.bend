# eukhe: the proof of LAW cvar_refusal_accepts
# A list kept whole runs the refusal through to its end (LW.wh.ref).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/whole.bend as CvarWhole
import ./base/whole.bend as LW

def CvarWhole.cvar_refusal_accepts(xs, whole):
  %Equal.sym(List<&2, Cv.Decl>, xs, List.append(&2, Cv.Decl, xs, Nil{}), LW.wh.app_nil(xs)) : {Cv.refusal.go(_, Nil{}, Cv.taken.at(_, Nil{}), Cv.typed.first(_)) == Cv.Accept{} : Cv.Refusal}
  LW.wh.ref(xs, Nil{}, Nil{}, whole, LW.wh.fresh_nil(xs))
