# eukhe: the proof of LAW path_real_up_at_root
#
# PROOF: both paths walk p first, to one state (LAReal.prw.real_split),
# whose directory is `/` (p resolves there: LAReal.prw.real_end); from
# `/`, `..` stays at `/` (pua.root).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base/real.bend as LAReal

# from a state at `/`, `..` then r walks as r
def pua.root(t: Nat & Pp.Res, +r: List<&2, Tl.Seg>, +ls: List<&2, Pp.Link>, -l: Bool, e: {LAReal.prw.cont(t, Nil{}, ls) == Pp.Res{Nil{}, l} : Pp.Res}) -> {LAReal.prw.cont(t, Tl.Up{} <> r, ls) == LAReal.prw.cont(t, r, ls) : Pp.Res}:
  match t:
    case (f, q):
      match f:
        case 0n:
          match q:
            case Pp.Res{+a, b}:
              +ea = Equal.cong(Pp.Res, List<&2, Nat>, z => Pp.Res.at(z), Pp.Res{a, b}, Pp.Res{Nil{}, l}, e)
              %Equal.sym(List<&2, Nat>, a, Nil{}, ea) : {Pp.go(0n, Tl.Up{} <> r, ls, _, b, Pp.look.at(ls, Tl.Up{} <> r, _)) == Pp.go(0n, r, ls, _, b, Pp.look.at(ls, r, _)) : Pp.Res}
              {==}
        case 1n+g:
          match q:
            case Pp.Res{+a, b}:
              +ea = Equal.cong(Pp.Res, List<&2, Nat>, z => Pp.Res.at(z), Pp.Res{a, b}, Pp.Res{Nil{}, l}, e)
              %Equal.sym(List<&2, Nat>, a, Nil{}, ea) : {Pp.go(1n+g, Tl.Up{} <> r, ls, _, b, Pp.look.at(ls, Tl.Up{} <> r, _)) == Pp.go(1n+g, r, ls, _, b, Pp.look.at(ls, r, _)) : Pp.Res}
              {==}

def PathPolicy.path_real_up_at_root(ls, p, r, l, reach):
  +e = Equal.trans(Pp.Res, LAReal.prw.cont(LAReal.prw.T(ls, p), Nil{}, ls), Pp.real(ls, p), Pp.Res{Nil{}, l}, Equal.sym(Pp.Res, Pp.real(ls, p), LAReal.prw.cont(LAReal.prw.T(ls, p), Nil{}, ls), LAReal.prw.real_end(ls, p)), reach)
  Equal.trans(Pp.Res, Pp.real(ls, List.append(&2, Tl.Seg, p, Tl.Up{} <> r)), LAReal.prw.cont(LAReal.prw.T(ls, p), r, ls), Pp.real(ls, List.append(&2, Tl.Seg, p, r)),
    Equal.trans(Pp.Res, Pp.real(ls, List.append(&2, Tl.Seg, p, Tl.Up{} <> r)), LAReal.prw.cont(LAReal.prw.T(ls, p), Tl.Up{} <> r, ls), LAReal.prw.cont(LAReal.prw.T(ls, p), r, ls), LAReal.prw.real_split(ls, p, Tl.Up{} <> r), pua.root(LAReal.prw.T(ls, p), r, ls, l, e)),
    Equal.sym(Pp.Res, Pp.real(ls, List.append(&2, Tl.Seg, p, r)), LAReal.prw.cont(LAReal.prw.T(ls, p), r, ls), LAReal.prw.real_split(ls, p, r)))
