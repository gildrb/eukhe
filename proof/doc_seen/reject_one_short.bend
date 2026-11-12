# eukhe: the proof of LAW reject_one_short
#
# PROOF: the anchor is the one unseen anchor; its width is at most 512, so
# it is shown whole and the verdict is whole.

import Base
import ../../bend/doc_seen.bend as Ds
import ../../laws/doc_seen.bend as DocSeen
import ./base.bend as LA

def DocSeen.reject_one_short(seen, n, x, u, short):
  %Equal.sym(Bool, Ds.mem(n, seen), False{}, LA.dsr.mem_is(n, seen, False{}, u)) : {Ds.check.go(Ds.unseen.put(Ds.At{n, Some{x}}, Nil{}, _)) == Ds.Check{[n], [Ds.Show{n, None{}}], True{}} : Ds.Check}
  %Equal.sym(Bool, Nat.is_le(x, 512n), True{}, short) : {Ds.Check{[n], [Ds.Show{n, Ds.shows.cut(_)}], Bool.and(_, True{})} == Ds.Check{[n], [Ds.Show{n, None{}}], True{}} : Ds.Check}
  {==}
