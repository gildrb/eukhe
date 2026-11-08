# eukhe: the proof of LAW path_safe_is_inside
#
# PROOF: safe and the class of a resolved path read the same loop flag
# and the same three tests (secret, protected, a root); for each value of
# them, safe holds only where the class picked is Inside (psi.pick).

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base.bend as LA

def psi.pick(l: Bool, s: Bool, p: Bool, i: Bool, h: {Bool.and(Bool.not(l), Pp.inside_ok(s, p, i)) == True{} : Bool}) -> {Pp.demote(Pp.cls.pick(s, p, i), l) == Pp.Inside{} : Pp.Cls}:
  match l:
    case True{}:
      LA.pp.absurdF({Pp.demote(Pp.cls.pick(s, p, i), True{}) == Pp.Inside{} : Pp.Cls}, h)
    case False{}:
      match s:
        case True{}:
          LA.pp.absurdF({Pp.demote(Pp.cls.pick(True{}, p, i), False{}) == Pp.Inside{} : Pp.Cls}, h)
        case False{}:
          match p:
            case True{}:
              LA.pp.absurdF({Pp.demote(Pp.cls.pick(False{}, True{}, i), False{}) == Pp.Inside{} : Pp.Cls}, h)
            case False{}:
              match i:
                case True{}:
                  {==}
                case False{}:
                  LA.pp.absurdF({Pp.demote(Pp.cls.pick(False{}, False{}, False{}), False{}) == Pp.Inside{} : Pp.Cls}, h)

def psi.res(+pol: Pp.Pol, r: Pp.Res, h: {Pp.safe(pol, r) == True{} : Bool}) -> {Pp.class_res(pol, r) == Pp.Inside{} : Pp.Cls}:
  match r:
    case Pp.Res{+at, +l}:
      psi.pick(l, Pp.any_under(Pp.Pol.secret(pol), at), Pp.protects(pol, at), Maybe.is_some(&2, List<&2, Nat>, Pp.root.of(Pp.Pol.roots(pol), at)), h)

def PathPolicy.path_safe_is_inside(pol, ls, segs, safe):
  psi.res(pol, Pp.real(ls, segs), safe)
