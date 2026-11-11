# eukhe: the proof of LAW path_judge_guards_secret_ancestor
#
# PROOF: at is a strict ancestor of the entry m/k/at, so the model's
# ancestor test holds over the secret entries (pha.anc) and over the rules'
# entries followed by them (pp.ancestor_append); the class is then guarded
# (pp.anc_res).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base.bend as LA
import ./path_ancestor_guarded.bend as PPathAncestorGuarded
import ./path_holds_above_secret.bend as PPathHoldsAboveSecret

# an ancestor of an entry of ys is an ancestor of an entry of xs ++ ys
def pp.ancestor_append(xs: List<&2, List<&2, Nat>>, +ys: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, h: {Pp.any_ancestor(ys, at) == True{} : Bool}) -> {Pp.any_ancestor(List.append(&2, List<&2, Nat>, xs, ys), at) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +p <> +rest:
      LA.pp.or_tr(Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))), Pp.any_ancestor(List.append(&2, List<&2, Nat>, rest, ys), at), pp.ancestor_append(rest, ys, at, h))

def PathPolicy.path_judge_guards_secret_ancestor(ro, ru, se1, m, k, at, se2, l):
  +se = List.append(&2, List<&2, Nat>, se1, (m <> List.append(&2, Nat, k, at)) <> se2)
  PPathAncestorGuarded.pp.anc_res(Pp.Pol{ro, ru, se}, Pp.Res{at, l}, pp.ancestor_append(Pp.entries(ru), se, at, PPathHoldsAboveSecret.pha.anc(se1, m, k, at, se2)))
