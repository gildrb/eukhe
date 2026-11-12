# eukhe: the proof of LAW cvar_cfg_written_keeps_others
# Both sides read y as the project's layer on the global file's on
# settings.json's (LS.sv.stores); each global file's layer of y reads its
# sets of y alone (LS.sv.only), and those are the same.

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ./base/save.bend as LS

def Cvar.cvar_cfg_written_keeps_others(ds, doc, g, g2, p, y, same):
  +c0 = Cv.layer(doc, ds, Cv.Config{}, y, None{})
  +rhs = Cv.layer(p, ds, Cv.Config{}, y, Cv.layer(g, ds, Cv.Config{}, y, c0))
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layered(ds, Cv.stores(doc, g2, p), Nil{}, y), Cv.layer(p, ds, Cv.Config{}, y, Cv.layer(g2, ds, Cv.Config{}, y, c0)), LS.sv.stores(ds, doc, g2, p, y)) : {_ == Cv.layered(ds, Cv.stores(doc, g, p), Nil{}, y) : Maybe<&2, Cv.Val>}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layered(ds, Cv.stores(doc, g, p), Nil{}, y), rhs, LS.sv.stores(ds, doc, g, p, y)) : {Cv.layer(p, ds, Cv.Config{}, y, Cv.layer(g2, ds, Cv.Config{}, y, c0)) == _ : Maybe<&2, Cv.Val>}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(g2, ds, Cv.Config{}, y, c0), Cv.layer(Cvar.spec_sets_of(g2, y), ds, Cv.Config{}, y, c0), LS.sv.only(g2, ds, Cv.Config{}, y, c0)) : {Cv.layer(p, ds, Cv.Config{}, y, _) == rhs : Maybe<&2, Cv.Val>}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(g, ds, Cv.Config{}, y, c0), Cv.layer(Cvar.spec_sets_of(g, y), ds, Cv.Config{}, y, c0), LS.sv.only(g, ds, Cv.Config{}, y, c0)) : {Cv.layer(p, ds, Cv.Config{}, y, Cv.layer(Cvar.spec_sets_of(g2, y), ds, Cv.Config{}, y, c0)) == Cv.layer(p, ds, Cv.Config{}, y, _) : Maybe<&2, Cv.Val>}
  %Equal.sym(List<&2, Cv.Bind>, Cvar.spec_sets_of(g2, y), Cvar.spec_sets_of(g, y), same) : {Cv.layer(p, ds, Cv.Config{}, y, Cv.layer(_, ds, Cv.Config{}, y, c0)) == Cv.layer(p, ds, Cv.Config{}, y, Cv.layer(Cvar.spec_sets_of(g, y), ds, Cv.Config{}, y, c0)) : Maybe<&2, Cv.Val>}
  {==}
