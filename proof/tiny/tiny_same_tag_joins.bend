# eukhe: the proof of LAW tiny_same_tag_joins

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny/pick.bend as Tiny
import ./base.bend as LA

def pn.tiny_same_tag_joins(+o: Nat, +t: Nat, +p: Nat) -> {Tn.got(Tn.Worker{o, t}, Tn.Need{p, t}) == [Tn.Joined{}] : List<&2, Tn.Got>}:
  %LA.pn.eq_refl(t) : {[Tn.need.g(_)] == [Tn.Joined{}] : List<&2, Tn.Got>}
  {==}

def Tiny.tiny_same_tag_joins(o, t, p):
  pn.tiny_same_tag_joins(o, t, p)
