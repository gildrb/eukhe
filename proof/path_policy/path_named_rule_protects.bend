# eukhe: the proof of LAW path_named_rule_protects
#
# PROOF: the names a Named rule reads are the names of the path below its
# deepest root (pc.below_root); n is among xs ++ n::ys (pcn.elem); so the
# Named rule covers the path, the rules cover it (pcc.covers_app), the
# policy protects it and, not Secret, it is Protected
# (pcc.protects_class).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base.bend as LA
import ./base/root.bend as LAR
import ./base/class.bend as LAC

# n is among xs ++ n::ys
def pcn.elem(xs: List<&2, Nat>, +n: Nat, +ys: List<&2, Nat>) -> {Tl.elem(List.append(&2, Nat, xs, n <> ys), n) == True{} : Bool}:
  match xs:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(n, n), True{}, LAR.pc.nat_eq_refl(n)) : {Bool.or(_, Tl.elem(ys, n)) == True{} : Bool}
      {==}
    case +x <> +rest:
      LA.pp.or_tr(Nat.is_eq(x, n), Tl.elem(List.append(&2, Nat, rest, n <> ys), n), pcn.elem(rest, n, ys))

def PathPolicy.path_named_rule_protects(ro, ru1, n, ru2, se, ls, segs, at, l, xs, ys, res, named, ns):
  +ru = List.append(&2, Pp.Rule, ru1, Pp.Named{n} <> ru2)
  +low = Pp.below(at, Pp.root.of(ro, at))
  +el = Equal.trans(List<&2, Nat>, low, PathPolicy.pp_below_root(ro, at), List.append(&2, Nat, xs, n <> ys), LAR.pc.below_root(ro, at), named)
  +cv = Equal.trans(Bool, Tl.elem(low, n), Tl.elem(List.append(&2, Nat, xs, n <> ys), n), True{}, Equal.cong(List<&2, Nat>, Bool, z => Tl.elem(z, n), low, List.append(&2, Nat, xs, n <> ys), el), pcn.elem(xs, n, ys))
  +hc = LAC.pcc.covers_app(ru1, Pp.Named{n}, ru2, at, low, cv)
  LAC.pcc.protects_class(ro, ru, se, ls, segs, at, l, res, ns, LAC.pcc.prot_cover(ro, ru, se, at, hc))
