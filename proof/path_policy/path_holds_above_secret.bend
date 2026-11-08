# eukhe: the proof of LAW path_holds_above_secret
#
# PROOF: the judgment's holds is the secret test or the ancestor test of
# the secret entries; at is a strict ancestor of the entry m/k/at
# (pce.strict), so the ancestor test holds (pha.anc, by induction on the
# entries before it).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base.bend as LA
import ./path_entry_ancestor_protects.bend as PPathEntryAncestorProtects

# at is a strict ancestor of an entry of se1 ++ (m/k/at) :: se2
def pha.anc(se1: List<&2, List<&2, Nat>>, +m: Nat, +k: List<&2, Nat>, +at: List<&2, Nat>, +se2: List<&2, List<&2, Nat>>) -> {Pp.any_ancestor(List.append(&2, List<&2, Nat>, se1, (m <> List.append(&2, Nat, k, at)) <> se2), at) == True{} : Bool}:
  match se1:
    case Nil{}:
      %Equal.sym(Bool, Bool.and(Pp.under(at, m <> List.append(&2, Nat, k, at)), Bool.not(Tl.ids.eq(at, m <> List.append(&2, Nat, k, at)))), True{}, PPathEntryAncestorProtects.pce.strict(at, m, k)) : {Bool.or(_, Pp.any_ancestor(se2, at)) == True{} : Bool}
      {==}
    case +p <> +rest:
      LA.pp.or_tr(Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))), Pp.any_ancestor(List.append(&2, List<&2, Nat>, rest, (m <> List.append(&2, Nat, k, at)) <> se2), at), pha.anc(rest, m, k, at, se2))

def PathPolicy.path_holds_above_secret(ro, ru, se1, m, k, at, se2, l):
  +se = List.append(&2, List<&2, Nat>, se1, (m <> List.append(&2, Nat, k, at)) <> se2)
  LA.pp.or_tr(Pp.any_under(se, at), Pp.any_ancestor(se, at), pha.anc(se1, m, k, at, se2))
