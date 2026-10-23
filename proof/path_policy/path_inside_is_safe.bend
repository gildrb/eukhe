# eukhe: the proof of LAW path_inside_is_safe

import Base
import ../../bend/tools.bend as Tl
import ../../bend/path_policy.bend as Pp
import ../../LAWS.bend as Laws
import ./base.bend as LA

# Inside exactly when no secret, nothing protects, and a root holds it
def pp.pick_inside(sec: Bool, prot: Bool, ins: Bool) -> {Pp.Cls.inside(Pp.cls.pick(sec, prot, ins)) == Pp.inside_ok(sec, prot, ins) : Bool}:
  match sec:
    case True{}:
      {==}
    case False{}:
      match prot:
        case True{}:
          {==}
        case False{}:
          match ins:
            case True{}:
              {==}
            case False{}:
              {==}

def pp.inside_safe(+pol: Pp.Pol, r: Pp.Res, h: {Pp.class_res(pol, r) == Pp.Inside{} : Pp.Cls}) -> {Pp.safe(pol, r) == True{} : Bool}:
  match r:
    case Pp.Res{+at, +looped}:
      %pp.pick_inside(Pp.any_under(Pp.Pol.secret(pol), at), Pp.protects(pol, at), Maybe.is_some(&2, List<&2, Nat>, Pp.root.of(Pp.Pol.roots(pol), at))) : {Bool.and(Bool.not(looped), _) == True{} : Bool}
      LA.pp.demote_inside(Pp.class_of(pol, at), looped, h)

def pp.path_inside_is_safe(+pol: Pp.Pol, +ls: List<&2, Pp.Link>, +segs: List<&2, Tl.Seg>, inside: {Pp.class(pol, ls, segs) == Pp.Inside{} : Pp.Cls}) -> {Pp.safe(pol, Pp.real(ls, segs)) == True{} : Bool}:
  pp.inside_safe(pol, Pp.real(ls, segs), inside)

def Laws.path_inside_is_safe(pol, ls, segs, inside):
  pp.path_inside_is_safe(pol, ls, segs, inside)
