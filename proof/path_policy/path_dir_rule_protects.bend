# eukhe: the proof of LAW path_dir_rule_protects
#
# PROOF: a Dir rule on p covers p (the same path) and x/p (its parent is
# p), the k ++ p with at most one name k (pcd.cov); so the rules cover it
# (pcc.covers_app), the policy protects it and, not Secret, it is
# Protected (pcc.protects_class).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base.bend as LA
import ./base/root.bend as LAR
import ./base/class.bend as LAC

# nothing is below 0
def pcd.lt0(n: Nat) -> {Nat.is_lt(n, 0n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      {==}

def pcd.cov(k: List<&2, Nat>, +p: List<&2, Nat>, +low: List<&2, Nat>, one: {Nat.is_lt(List.length(&2, Nat, k), 2n) == True{} : Bool}) -> {Pp.covers(Pp.Dir{p}, List.append(&2, Nat, k, p), low) == True{} : Bool}:
  match k:
    case Nil{}:
      %Equal.sym(Bool, Tl.ids.eq(p, p), True{}, LAR.pc.ids_refl(p)) : {Bool.or(_, Pp.parent_is(p, p)) == True{} : Bool}
      {==}
    case +x <> r:
      match r:
        case Nil{}:
          LA.pp.or_tr(Tl.ids.eq(x <> p, p), Pp.parent_is(x <> p, p), LAR.pc.ids_refl(p))
        case y <> t:
          LA.pp.absurdF({Pp.covers(Pp.Dir{p}, List.append(&2, Nat, x <> y <> t, p), low) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(List.length(&2, Nat, t), 0n), True{}, Equal.sym(Bool, Nat.is_lt(List.length(&2, Nat, t), 0n), False{}, pcd.lt0(List.length(&2, Nat, t))), one))

def PathPolicy.path_dir_rule_protects(ro, ru1, p, ru2, se, ls, segs, k, l, one, res, ns):
  +at = List.append(&2, Nat, k, p)
  +ru = List.append(&2, Pp.Rule, ru1, Pp.Dir{p} <> ru2)
  +low = Pp.below(at, Pp.root.of(ro, at))
  +hc = LAC.pcc.covers_app(ru1, Pp.Dir{p}, ru2, at, low, pcd.cov(k, p, low, one))
  LAC.pcc.protects_class(ro, ru, se, ls, segs, at, l, res, ns, LAC.pcc.prot_cover(ro, ru, se, at, hc))
