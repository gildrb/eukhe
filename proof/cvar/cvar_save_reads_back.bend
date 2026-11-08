# eukhe: the proof of LAW cvar_save_reads_back
# The stores after the write read x as the project's layer on the
# written value (LS.sv.read); the project's layer sets nothing, so it
# keeps that value (LS.sv.or).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ./base.bend as LA
import ./base/save.bend as LS

def Cvar.cvar_save_reads_back(ds, doc, g, p, x, v, ok, quiet):
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layered(ds, Cv.stores(doc, Cv.save(g, Cv.Bind{x, v}), p), Nil{}, x), Cv.layer(p, ds, Cv.Config{}, x, Some{v}), LS.sv.read(ds, doc, g, p, x, v, ok)) : {_ == Some{v} : Maybe<&2, Cv.Val>}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(p, ds, Cv.Config{}, x, Some{v}), LS.sv.orm(Cv.layer(p, ds, Cv.Config{}, x, None{}), Some{v}), LS.sv.or(p, ds, Cv.Config{}, x, Some{v})) : {_ == Some{v} : Maybe<&2, Cv.Val>}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(p, ds, Cv.Config{}, x, None{}), None{}, quiet) : {LS.sv.orm(_, Some{v}) == Some{v} : Maybe<&2, Cv.Val>}
  {==}
