# eukhe: the proof of LAW path_root_inside
#
# PROOF: the root q is at or above k ++ q (pcc.under_app), so some root is
# (pri.any), so the model finds a root (pc.has_root); with no loop, not
# Secret and not Protected, the class picked is Inside (pri.pick).

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base.bend as LA
import ./base/root.bend as LAR
import ./base/class.bend as LAC

# a root at or above the path is among the roots
def pri.any(ro1: List<&2, List<&2, Nat>>, +q: List<&2, Nat>, +ro2: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, h: {Pp.under(q, at) == True{} : Bool}) -> {Pp.any_under(List.append(&2, List<&2, Nat>, ro1, q <> ro2), at) == True{} : Bool}:
  match ro1:
    case Nil{}:
      %Equal.sym(Bool, Pp.under(q, at), True{}, h) : {Bool.or(_, Pp.any_under(ro2, at)) == True{} : Bool}
      {==}
    case +p <> +rest:
      LA.pp.or_tr(Pp.under(p, at), Pp.any_under(List.append(&2, List<&2, Nat>, rest, q <> ro2), at), pri.any(rest, q, ro2, at, h))

# held by a root, no loop, not Protected, not Secret: Inside
def pri.pick(s: Bool, p: Bool, np: {Pp.demote(Pp.cls.pick(s, p, True{}), False{}) != Pp.Protected{} : Pp.Cls}, ns: {Pp.demote(Pp.cls.pick(s, p, True{}), False{}) != Pp.Secret{} : Pp.Cls}) -> {Pp.demote(Pp.cls.pick(s, p, True{}), False{}) == Pp.Inside{} : Pp.Cls}:
  match s:
    case True{}:
      LAC.pcc.never({Pp.Secret{} == Pp.Inside{} : Pp.Cls}, ns({==}))
    case False{}:
      match p:
        case True{}:
          LAC.pcc.never({Pp.Protected{} == Pp.Inside{} : Pp.Cls}, np({==}))
        case False{}:
          {==}

def PathPolicy.path_root_inside(ro1, q, ro2, ru, se, ls, segs, k, res, np, ns):
  +ro = List.append(&2, List<&2, Nat>, ro1, q <> ro2)
  +at = List.append(&2, Nat, k, q)
  +pol = {Pp.Pol{ro, ru, se} : Pp.Pol}
  +s = Pp.any_under(se, at)
  +p = Pp.protects(pol, at)
  +hi = Equal.trans(Bool, Maybe.is_some(&2, List<&2, Nat>, Pp.root.of(ro, at)), Pp.any_under(ro, at), True{}, LAR.pc.has_root(ro, at), pri.any(ro1, q, ro2, at, LAC.pcc.under_app(q, k)))
  +eq = Equal.trans(Pp.Cls, Pp.class(pol, ls, segs), Pp.demote(Pp.class_of(pol, at), False{}), Pp.demote(Pp.cls.pick(s, p, True{}), False{}), LAC.pcc.cls_eq(pol, ls, segs, at, False{}, res), Equal.cong(Bool, Pp.Cls, z => Pp.demote(Pp.cls.pick(s, p, z), False{}), Maybe.is_some(&2, List<&2, Nat>, Pp.root.of(ro, at)), True{}, hi))
  Equal.trans(Pp.Cls, Pp.class(pol, ls, segs), Pp.demote(Pp.cls.pick(s, p, True{}), False{}), Pp.Inside{}, eq, pri.pick(s, p, h => np(Equal.trans(Pp.Cls, Pp.class(pol, ls, segs), Pp.demote(Pp.cls.pick(s, p, True{}), False{}), Pp.Protected{}, eq, h)), h => ns(Equal.trans(Pp.Cls, Pp.class(pol, ls, segs), Pp.demote(Pp.cls.pick(s, p, True{}), False{}), Pp.Secret{}, eq, h))))
