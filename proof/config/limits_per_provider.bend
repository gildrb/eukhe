# eukhe: the proof of LAW limits_per_provider
# An induction on the providers asked.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config

def plp.snoc(+s: Cf.InFlight, qs: List<&2, Nat>, +q: Nat) -> {Cf.limits(s, List.append(&2, Nat, qs, [q])) == List.append(&2, Cf.Lim, Cf.limits(s, qs), [Cf.limit(s, q)]) : List<&2, Cf.Lim>}:
  match qs:
    case Nil{}:
      {==}
    case +x <> t:
      %plp.snoc(s, t, q) : {Cf.limit(s, x) <> Cf.limits(s, List.append(&2, Nat, t, [q])) == Cf.limit(s, x) <> _ : List<&2, Cf.Lim>}
      {==}

def Config.limits_per_provider(s, qs, q):
  ({==}, plp.snoc(s, qs, q))
