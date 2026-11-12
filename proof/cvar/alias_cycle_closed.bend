# eukhe: the proof of LAW alias_cycle_closed
# By induction on the nesting level left (LE.ex.inv): the alias of a name
# of ns (LE.ex.closed_at) is the laws' body (LE.ex.body_of), whose sets go
# onto the accumulator and whose run of an alias of ns is a cycle with no
# level left, else that alias one level down, a cycle named in ns by the
# hypothesis (LE.ex.walk); a cycle stops the rest (LE.ex.keep_in), and fin
# keeps it (LE.ex.fin_in).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/entry.bend as CvarEntry
import ./base/expand.bend as LE

def CvarEntry.alias_cycle_closed(as, ns, n, one, closed):
  +k = List.length(&2, Cv.Alias, as)
  +r = Cv.expand.go(k, Cv.body(as, n), as, Cv.Flat{Nil{}})
  %Equal.sym(Bool, CvarEntry.spec_cycle_in(Cv.fin(r), ns), CvarEntry.spec_cycle_in(r, ns), LE.ex.fin_in(r, ns)) : {_ == True{} : Bool}
  LE.ex.inv(k, as, ns, n, Nil{}, closed, one)
