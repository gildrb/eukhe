# eukhe: the proof of LAW path_judge_guards_secret_ancestor

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base.bend as LA
import ./path_ancestor_guarded.bend as PPathAncestorGuarded

# an ancestor of an entry of ys is an ancestor of an entry of xs ++ ys
def pp.ancestor_append(xs: List<&2, List<&2, Nat>>, +ys: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, h: {Pp.any_ancestor(ys, at) == True{} : Bool}) -> {Pp.any_ancestor(List.append(&2, List<&2, Nat>, xs, ys), at) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +p <> +rest:
      LA.pp.or_tr(Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))), Pp.any_ancestor(List.append(&2, List<&2, Nat>, rest, ys), at), pp.ancestor_append(rest, ys, at, h))

def PathPolicy.path_judge_guards_secret_ancestor(ro, ru, se, at, l, anc):
  PPathAncestorGuarded.pp.anc_res(Pp.Pol{ro, ru, se}, Pp.Res{at, l}, pp.ancestor_append(Pp.entries(ru), se, at, Equal.trans(Bool, Pp.any_ancestor(se, at), PathPolicy.pp_above_any(se, at), True{}, LA.pp.any_ancestor_spec(se, at), anc)))
