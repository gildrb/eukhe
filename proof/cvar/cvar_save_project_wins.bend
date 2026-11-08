# eukhe: the proof of LAW cvar_save_project_wins
# As cvar_save_reads_back, but the project's layer sets w, which it
# answers from any current value (LS.sv.or).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ./base.bend as LA
import ./base/save.bend as LS

def Cvar.cvar_save_project_wins(ds, doc, g, p, x, v, w, ok, set):
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layered(ds, Cv.stores(doc, Cv.save(g, Cv.Bind{x, v}), p), Nil{}, x), Cv.layer(p, ds, Cv.Config{}, x, Some{v}), LS.sv.read(ds, doc, g, p, x, v, ok)) : {_ == Some{w} : Maybe<&2, Cv.Val>}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(p, ds, Cv.Config{}, x, Some{v}), LS.sv.orm(Cv.layer(p, ds, Cv.Config{}, x, None{}), Some{v}), LS.sv.or(p, ds, Cv.Config{}, x, Some{v})) : {_ == Some{w} : Maybe<&2, Cv.Val>}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(p, ds, Cv.Config{}, x, None{}), Some{w}, set) : {LS.sv.orm(_, Some{v}) == Some{w} : Maybe<&2, Cv.Val>}
  {==}
