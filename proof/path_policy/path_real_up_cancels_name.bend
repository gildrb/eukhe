# eukhe: the proof of LAW path_real_up_cancels_name
#
# PROOF: both paths walk p first, to one state (LAReal.prw.real_split),
# whose directory is at (p resolves there: LAReal.prw.real_end); no link
# sits at n/at (LAReal.prw.find_none), so from there n enters n/at and `..`
# goes back to at, with no link met (ucn.back).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base/real.bend as LAReal

# from a state at at, a name n with no link at n/at, then `..`, then r
# walks as r
def ucn.back(t: Nat & Pp.Res, +n: Nat, +r: List<&2, Tl.Seg>, +ls: List<&2, Pp.Link>, +at: List<&2, Nat>, -l: Bool, e: {LAReal.prw.cont(t, Nil{}, ls) == Pp.Res{at, l} : Pp.Res}, fn: {Pp.link.find(ls, n <> at) == None{} : Maybe<&2, Pp.Link>}) -> {LAReal.prw.cont(t, Tl.Name{n} <> Tl.Up{} <> r, ls) == LAReal.prw.cont(t, r, ls) : Pp.Res}:
  match t:
    case (f, q):
      match f:
        case 0n:
          match q:
            case Pp.Res{+a, b}:
              match b:
                case True{}:
                  +ea = Equal.cong(Pp.Res, List<&2, Nat>, z => Pp.Res.at(z), Pp.Res{a, True{}}, Pp.Res{at, l}, e)
                  %Equal.sym(List<&2, Nat>, a, at, ea) : {Pp.go(0n, Tl.Name{n} <> Tl.Up{} <> r, ls, _, True{}, Pp.look.at(ls, Tl.Name{n} <> Tl.Up{} <> r, _)) == Pp.go(0n, r, ls, _, True{}, Pp.look.at(ls, r, _)) : Pp.Res}
                  %Equal.sym(Maybe<&2, Pp.Link>, Pp.link.find(ls, n <> at), None{}, fn) : {Pp.go(0n, Tl.Name{n} <> Tl.Up{} <> r, ls, at, True{}, _) == Pp.go(0n, r, ls, at, True{}, Pp.look.at(ls, r, at)) : Pp.Res}
                  {==}
                case False{}:
                  +ea = Equal.cong(Pp.Res, List<&2, Nat>, z => Pp.Res.at(z), Pp.Res{a, False{}}, Pp.Res{at, l}, e)
                  %Equal.sym(List<&2, Nat>, a, at, ea) : {Pp.go(0n, Tl.Name{n} <> Tl.Up{} <> r, ls, _, False{}, Pp.look.at(ls, Tl.Name{n} <> Tl.Up{} <> r, _)) == Pp.go(0n, r, ls, _, False{}, Pp.look.at(ls, r, _)) : Pp.Res}
                  %Equal.sym(Maybe<&2, Pp.Link>, Pp.link.find(ls, n <> at), None{}, fn) : {Pp.go(0n, Tl.Name{n} <> Tl.Up{} <> r, ls, at, False{}, _) == Pp.go(0n, r, ls, at, False{}, Pp.look.at(ls, r, at)) : Pp.Res}
                  {==}
        case 1n+g:
          match q:
            case Pp.Res{+a, b}:
              +ea = Equal.cong(Pp.Res, List<&2, Nat>, z => Pp.Res.at(z), Pp.Res{a, b}, Pp.Res{at, l}, e)
              %Equal.sym(List<&2, Nat>, a, at, ea) : {Pp.go(1n+g, Tl.Name{n} <> Tl.Up{} <> r, ls, _, b, Pp.look.at(ls, Tl.Name{n} <> Tl.Up{} <> r, _)) == Pp.go(1n+g, r, ls, _, b, Pp.look.at(ls, r, _)) : Pp.Res}
              %Equal.sym(Maybe<&2, Pp.Link>, Pp.link.find(ls, n <> at), None{}, fn) : {Pp.go(1n+g, Tl.Name{n} <> Tl.Up{} <> r, ls, at, b, _) == Pp.go(1n+g, r, ls, at, b, Pp.look.at(ls, r, at)) : Pp.Res}
              {==}

def PathPolicy.path_real_up_cancels_name(ls, p, n, r, at, l, reach, plain):
  +e = Equal.trans(Pp.Res, LAReal.prw.cont(LAReal.prw.T(ls, p), Nil{}, ls), Pp.real(ls, p), Pp.Res{at, l}, Equal.sym(Pp.Res, Pp.real(ls, p), LAReal.prw.cont(LAReal.prw.T(ls, p), Nil{}, ls), LAReal.prw.real_end(ls, p)), reach)
  Equal.trans(Pp.Res, Pp.real(ls, List.append(&2, Tl.Seg, p, Tl.Name{n} <> Tl.Up{} <> r)), LAReal.prw.cont(LAReal.prw.T(ls, p), r, ls), Pp.real(ls, List.append(&2, Tl.Seg, p, r)),
    Equal.trans(Pp.Res, Pp.real(ls, List.append(&2, Tl.Seg, p, Tl.Name{n} <> Tl.Up{} <> r)), LAReal.prw.cont(LAReal.prw.T(ls, p), Tl.Name{n} <> Tl.Up{} <> r, ls), LAReal.prw.cont(LAReal.prw.T(ls, p), r, ls), LAReal.prw.real_split(ls, p, Tl.Name{n} <> Tl.Up{} <> r), ucn.back(LAReal.prw.T(ls, p), n, r, ls, at, l, e, LAReal.prw.find_none(ls, n <> at, plain))),
    Equal.sym(Pp.Res, Pp.real(ls, List.append(&2, Tl.Seg, p, r)), LAReal.prw.cont(LAReal.prw.T(ls, p), r, ls), LAReal.prw.real_split(ls, p, r)))
