# eukhe: the proof of LAW cvar_cfg_project_wins
# The stores read x as the project's layer on the lower stores'
# (LS.sv.stores); the project's layer sets w, which it answers from any
# current value (LS.sv.or).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ./base/save.bend as LS

def Cvar.cvar_cfg_project_wins(ds, doc, g, p, x, w, set):
  +c1 = Cv.layer(g, ds, Cv.Config{}, x, Cv.layer(doc, ds, Cv.Config{}, x, None{}))
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layered(ds, Cv.stores(doc, g, p), Nil{}, x), Cv.layer(p, ds, Cv.Config{}, x, c1), LS.sv.stores(ds, doc, g, p, x)) : {_ == Some{w} : Maybe<&2, Cv.Val>}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(p, ds, Cv.Config{}, x, c1), LS.sv.orm(Cv.layer(p, ds, Cv.Config{}, x, None{}), c1), LS.sv.or(p, ds, Cv.Config{}, x, c1)) : {_ == Some{w} : Maybe<&2, Cv.Val>}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(p, ds, Cv.Config{}, x, None{}), Some{w}, set) : {LS.sv.orm(_, c1) == Some{w} : Maybe<&2, Cv.Val>}
  {==}
