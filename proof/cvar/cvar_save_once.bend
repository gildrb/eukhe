# eukhe: the proof of LAW cvar_save_once
# The sets of x in the dropped store, then in the write (LS.sv.sets_app):
# none left (LS.sv.sets_drop), then the write itself.

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ./base.bend as LA
import ./base/save.bend as LS

def Cvar.cvar_save_once(g, x, v):
  +b = {Cv.Bind{x, v} : Cv.Bind}
  %Equal.sym(List<&2, Cv.Bind>, Cvar.spec_sets_of(Cv.save(g, b), x), List.append(&2, Cv.Bind, Cvar.spec_sets_of(Cv.drop(g, x), x), Cvar.spec_sets_of([b], x)), LS.sv.sets_app(Cv.drop(g, x), [b], x)) : {_ == [b] : List<&2, Cv.Bind>}
  %Equal.sym(List<&2, Cv.Bind>, Cvar.spec_sets_of(Cv.drop(g, x), x), Nil{}, LS.sv.sets_drop(g, x)) : {List.append(&2, Cv.Bind, _, Cvar.spec_sets_of([b], x)) == [b] : List<&2, Cv.Bind>}
  %LA.cvar.pv.eq_refl(x) : {Cvar.spec_sets_of.pick(_, b, Nil{}) == [b] : List<&2, Cv.Bind>}
  {==}
