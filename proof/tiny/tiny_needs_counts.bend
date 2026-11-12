# eukhe: the proof of LAW tiny_needs_counts
#
# PROOF: by induction on the first run of events: a need adds one to both
# sides (Nat.add steps on its first argument), an exit nothing; the two
# single events compute.

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny/pick.bend as Tiny

def tnc.app(a: List<&2, Tn.Ev>, +b: List<&2, Tn.Ev>) -> {Tn.needs(List.append(&2, Tn.Ev, a, b)) == Nat.add(Tn.needs(a), Tn.needs(b)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case Tn.Need{p, t}:
          %tnc.app(rest, b) : {1n+Tn.needs(List.append(&2, Tn.Ev, rest, b)) == 1n+_ : Nat}
          {==}
        case Tn.Gone{}:
          tnc.app(rest, b)

def Tiny.tiny_needs_counts(a, b, p, t):
  (tnc.app(a, b), {==})
