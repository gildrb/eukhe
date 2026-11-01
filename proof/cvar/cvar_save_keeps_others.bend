# eukhe: the proof of LAW cvar_save_keeps_others
# Both sides read y through settings.json, the global store and the
# project's in a row (LS.sv.app); the write leaves the global store's
# layer of y (LS.sv.save_keeps).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar.bend as Cvar
import ./base.bend as LA
import ./base/save.bend as LS

def Cvar.cvar_save_keeps_others(ds, doc, g, p, x, v, y, ne):
  +gs = Cv.save(g, Cv.Bind{x, v})
  +c0 = Cv.layer(doc, ds, Cv.Config{}, y, None{})
  +rhs = Cv.layer(List.append(&2, Cv.Bind, doc, List.append(&2, Cv.Bind, g, p)), ds, Cv.Config{}, y, None{})
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(List.append(&2, Cv.Bind, doc, List.append(&2, Cv.Bind, gs, p)), ds, Cv.Config{}, y, None{}), Cv.layer(List.append(&2, Cv.Bind, gs, p), ds, Cv.Config{}, y, c0), LS.sv.app(doc, List.append(&2, Cv.Bind, gs, p), ds, Cv.Config{}, y, None{})) : {_ == rhs : Maybe<&2, Cv.Val>}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(List.append(&2, Cv.Bind, gs, p), ds, Cv.Config{}, y, c0), Cv.layer(p, ds, Cv.Config{}, y, Cv.layer(gs, ds, Cv.Config{}, y, c0)), LS.sv.app(gs, p, ds, Cv.Config{}, y, c0)) : {_ == rhs : Maybe<&2, Cv.Val>}
  %Equal.sym(Maybe<&2, Cv.Val>, rhs, Cv.layer(List.append(&2, Cv.Bind, g, p), ds, Cv.Config{}, y, c0), LS.sv.app(doc, List.append(&2, Cv.Bind, g, p), ds, Cv.Config{}, y, None{})) : {Cv.layer(p, ds, Cv.Config{}, y, Cv.layer(gs, ds, Cv.Config{}, y, c0)) == _ : Maybe<&2, Cv.Val>}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(List.append(&2, Cv.Bind, g, p), ds, Cv.Config{}, y, c0), Cv.layer(p, ds, Cv.Config{}, y, Cv.layer(g, ds, Cv.Config{}, y, c0)), LS.sv.app(g, p, ds, Cv.Config{}, y, c0)) : {Cv.layer(p, ds, Cv.Config{}, y, Cv.layer(gs, ds, Cv.Config{}, y, c0)) == _ : Maybe<&2, Cv.Val>}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(gs, ds, Cv.Config{}, y, c0), Cv.layer(g, ds, Cv.Config{}, y, c0), LS.sv.save_keeps(g, x, v, y, ds, c0, ne)) : {Cv.layer(p, ds, Cv.Config{}, y, _) == Cv.layer(p, ds, Cv.Config{}, y, Cv.layer(g, ds, Cv.Config{}, y, c0)) : Maybe<&2, Cv.Val>}
  {==}
