# eukhe: the proof of LAW cvar_cfg_written_reads_back
# The stores read x as the project's layer on the global file's on
# settings.json's (LS.sv.stores); the global file's layer of x reads its
# sets of x alone (LS.sv.only), the one valid set of v, a hit; the
# project's layer sets nothing, so it keeps v (LS.sv.or).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ./base.bend as LA
import ./base/save.bend as LS

def Cvar.cvar_cfg_written_reads_back(ds, doc, g, p, x, v, once, ok, quiet):
  +b = {Cv.Bind{x, v} : Cv.Bind}
  +c0 = Cv.layer(doc, ds, Cv.Config{}, x, None{})
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layered(ds, Cv.stores(doc, g, p), Nil{}, x), Cv.layer(p, ds, Cv.Config{}, x, Cv.layer(g, ds, Cv.Config{}, x, c0)), LS.sv.stores(ds, doc, g, p, x)) : {_ == Some{v} : Maybe<&2, Cv.Val>}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(g, ds, Cv.Config{}, x, c0), Cv.layer(Cvar.spec_sets_of(g, x), ds, Cv.Config{}, x, c0), LS.sv.only(g, ds, Cv.Config{}, x, c0)) : {Cv.layer(p, ds, Cv.Config{}, x, _) == Some{v} : Maybe<&2, Cv.Val>}
  %Equal.sym(List<&2, Cv.Bind>, Cvar.spec_sets_of(g, x), [b], once) : {Cv.layer(p, ds, Cv.Config{}, x, Cv.layer(_, ds, Cv.Config{}, x, c0)) == Some{v} : Maybe<&2, Cv.Val>}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer([b], ds, Cv.Config{}, x, c0), Some{v}, LA.pv.layer_hit(b, ds, Cv.Config{}, x, c0, LS.sv.hit_self(ds, Cv.Config{}, x, v, ok))) : {Cv.layer(p, ds, Cv.Config{}, x, _) == Some{v} : Maybe<&2, Cv.Val>}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(p, ds, Cv.Config{}, x, Some{v}), LS.sv.orm(Cv.layer(p, ds, Cv.Config{}, x, None{}), Some{v}), LS.sv.or(p, ds, Cv.Config{}, x, Some{v})) : {_ == Some{v} : Maybe<&2, Cv.Val>}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(p, ds, Cv.Config{}, x, None{}), None{}, quiet) : {LS.sv.orm(_, Some{v}) == Some{v} : Maybe<&2, Cv.Val>}
  {==}
