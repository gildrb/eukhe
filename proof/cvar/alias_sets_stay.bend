# eukhe: the proof of LAW alias_sets_stay
# A list that only sets or toggles is plain (LE.ex.plain); a plain list
# expands to itself reversed onto the accumulator at any depth
# (PRB.pv.flat), and fin reverses it back.

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/entry.bend as CvarEntry
import ./alias_runs_body.bend as PRB
import ./base/expand.bend as LE

def CvarEntry.alias_sets_stay(cs, as, only):
  +k = {1n+List.length(&2, Cv.Alias, as) : Nat}
  %Equal.sym(Cv.Exp, Cv.expand.go(k, cs, as, Cv.Flat{Nil{}}), Cv.Flat{Cv.rev(cs, Nil{})}, PRB.pv.flat(cs, k, as, Nil{}, LE.ex.plain(cs, only))) : {Cv.fin(_) == Cv.Flat{cs} : Cv.Exp}
  Equal.cong(List<&2, Cv.Cmd>, Cv.Exp, l => Cv.Flat{l}, Cv.rev(Cv.rev(cs, Nil{}), Nil{}), cs, Equal.trans(List<&2, Cv.Cmd>, Cv.rev(Cv.rev(cs, Nil{}), Nil{}), List.append(&2, Cv.Cmd, cs, Nil{}), cs, PRB.pv.rev_rev(cs, Nil{}, Nil{}), PRB.pv.app_nil(cs)))
