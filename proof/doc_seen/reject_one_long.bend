# eukhe: the proof of LAW reject_one_long
#
# PROOF: the anchor is the one unseen anchor; its width is past 512, so it
# is shown cut to 512 and the verdict is not whole.

import Base
import ../../bend/doc_seen.bend as Ds
import ../../laws/doc_seen.bend as DocSeen
import ./base.bend as LA

def DocSeen.reject_one_long(seen, n, x, u, long):
  %Equal.sym(Bool, Ds.mem(n, seen), False{}, LA.dsr.mem_is(n, seen, False{}, u)) : {Ds.check.go(Ds.unseen.put(Ds.At{n, Some{x}}, Nil{}, _)) == Ds.Check{[n], [Ds.Show{n, Some{512n}}], False{}} : Ds.Check}
  %Equal.sym(Bool, Nat.is_le(x, 512n), False{}, long) : {Ds.Check{[n], [Ds.Show{n, Ds.shows.cut(_)}], Bool.and(_, True{})} == Ds.Check{[n], [Ds.Show{n, Some{512n}}], False{}} : Ds.Check}
  {==}
