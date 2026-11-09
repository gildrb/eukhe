# eukhe: the proof of LAW path_real_here_stays
#
# PROOF: both paths walk p first, to one state (LAReal.prw.real_split);
# from any state, `.` then r walks as r (prh.here).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base/real.bend as LAReal

# from any state, `.` then r walks as r
def prh.here(t: Nat & Pp.Res, +r: List<&2, Tl.Seg>, +ls: List<&2, Pp.Link>) -> {LAReal.prw.cont(t, Tl.Here{} <> r, ls) == LAReal.prw.cont(t, r, ls) : Pp.Res}:
  match t:
    case (f, q):
      match f:
        case 0n:
          match q:
            case Pp.Res{a, b}:
              {==}
        case 1n+g:
          match q:
            case Pp.Res{a, b}:
              {==}

def PathPolicy.path_real_here_stays(ls, p, r):
  Equal.trans(Pp.Res, Pp.real(ls, List.append(&2, Tl.Seg, p, Tl.Here{} <> r)), LAReal.prw.cont(LAReal.prw.T(ls, p), r, ls), Pp.real(ls, List.append(&2, Tl.Seg, p, r)),
    Equal.trans(Pp.Res, Pp.real(ls, List.append(&2, Tl.Seg, p, Tl.Here{} <> r)), LAReal.prw.cont(LAReal.prw.T(ls, p), Tl.Here{} <> r, ls), LAReal.prw.cont(LAReal.prw.T(ls, p), r, ls), LAReal.prw.real_split(ls, p, Tl.Here{} <> r), prh.here(LAReal.prw.T(ls, p), r, ls)),
    Equal.sym(Pp.Res, Pp.real(ls, List.append(&2, Tl.Seg, p, r)), LAReal.prw.cont(LAReal.prw.T(ls, p), r, ls), LAReal.prw.real_split(ls, p, r)))
