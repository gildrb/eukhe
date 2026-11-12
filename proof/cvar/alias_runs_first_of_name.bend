# eukhe: the proof of LAW alias_runs_first_of_name
# The run takes the body of the first alias named n (LE.ex.body_first);
# that body only sets or toggles, so it expands to itself (PRB.pv.flat),
# reversed back by fin.

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/entry.bend as CvarEntry
import ./alias_runs_body.bend as PRB
import ./base/expand.bend as LE

def CvarEntry.alias_runs_first_of_name(pre, n, b, post, fresh, only):
  +t = {List.append(&2, Cv.Alias, pre, Cv.Alias{n, b} <> post) : List<&2, Cv.Alias>}
  +k = List.length(&2, Cv.Alias, t)
  %Equal.sym(List<&2, Cv.Cmd>, Cv.body(t, n), b, LE.ex.body_first(pre, n, b, post, fresh)) : {Cv.fin(Cv.expand.go(k, _, t, Cv.Flat{Nil{}})) == Cv.Flat{b} : Cv.Exp}
  %Equal.sym(Cv.Exp, Cv.expand.go(k, b, t, Cv.Flat{Nil{}}), Cv.Flat{Cv.rev(b, Nil{})}, PRB.pv.flat(b, k, t, Nil{}, LE.ex.plain(b, only))) : {Cv.fin(_) == Cv.Flat{b} : Cv.Exp}
  Equal.cong(List<&2, Cv.Cmd>, Cv.Exp, l => Cv.Flat{l}, Cv.rev(Cv.rev(b, Nil{}), Nil{}), b, Equal.trans(List<&2, Cv.Cmd>, Cv.rev(Cv.rev(b, Nil{}), Nil{}), List.append(&2, Cv.Cmd, b, Nil{}), b, PRB.pv.rev_rev(b, Nil{}, Nil{}), PRB.pv.app_nil(b)))
