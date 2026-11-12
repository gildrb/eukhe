# eukhe: the proof of LAW glob_allow_list
#
# PROOF: by induction on ps: the list's verdict is the first pattern's or
# the rest's (or_else is or, GS.gs.af_or).

import Base
import ../../bend/glob/queries.bend as GQuery
import ../../laws/glob.bend as Glob
import ./base/logic.bend as GL
import ./base/seq.bend as GS

def gal.go(+sel: String, ps: List<&2, String>, +qs: List<&2, String>) -> {GQuery.allowed(sel, List.append(&2, String, ps, qs)) == Bool.or(GQuery.allowed(sel, ps), GQuery.allowed(sel, qs)) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +r:
      +a = GQuery.allow1(sel, p)
      +ar = GQuery.allowed(sel, r)
      +aq = GQuery.allowed(sel, qs)
      %Equal.sym(Bool, GQuery.allowed(sel, p <> List.append(&2, String, r, qs)), Bool.or(a, GQuery.allowed(sel, List.append(&2, String, r, qs))), GS.gs.af_or(a, GQuery.allowed(sel, List.append(&2, String, r, qs)))) : {_ == Bool.or(GQuery.allowed(sel, p <> r), aq) : Bool}
      %Equal.sym(Bool, GQuery.allowed(sel, p <> r), Bool.or(a, ar), GS.gs.af_or(a, ar)) : {Bool.or(a, GQuery.allowed(sel, List.append(&2, String, r, qs))) == Bool.or(_, aq) : Bool}
      %Equal.sym(Bool, GQuery.allowed(sel, List.append(&2, String, r, qs)), Bool.or(ar, aq), gal.go(sel, r, qs)) : {Bool.or(a, _) == Bool.or(Bool.or(a, ar), aq) : Bool}
      Equal.sym(Bool, Bool.or(Bool.or(a, ar), aq), Bool.or(a, Bool.or(ar, aq)), GL.gl.or_assoc(a, ar, aq))

def Glob.glob_allow_list(sel, ps, qs):
  %Equal.sym(Bool, GQuery.allowed(sel, List.append(&2, String, ps, qs)), Bool.or(GQuery.allowed(sel, ps), GQuery.allowed(sel, qs)), gal.go(sel, ps, qs)) : {(_, GQuery.allowed(sel, Nil{})) == (Bool.or(GQuery.allowed(sel, ps), GQuery.allowed(sel, qs)), False{}) : Bool & Bool}
  {==}
