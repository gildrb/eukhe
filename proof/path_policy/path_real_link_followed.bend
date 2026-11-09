# eukhe: the proof of LAW path_real_link_followed
#
# PROOF: p n r walks p first, to the state p reaches (LAReal.prw.split):
# at at, unlooped (p resolves there). The first link at n/at is the one of
# the law (LAReal.prw.find_first); had no link been left there, the walk
# would end looped (LAReal.prw.no_loop), so it follows the link with one
# link fewer: the target then r, from `/` (absolute) or from at
# (relative). From `/` that is the resolution of the target then r with
# 40 links, at least as many (LAReal.prw.le_T, LAReal.prw.up_to); from at
# it is the walk of p then the target then r, one link more
# (LAReal.prw.more); a walk that ends unlooped ends the same with more
# links left.

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base/real.bend as LAReal

# the links of the law
def plf.L(ls1: List<&2, Pp.Link>, n: Nat, at: List<&2, Nat>, abs: Bool, to: List<&2, Tl.Seg>, ls2: List<&2, Pp.Link>) -> List<&2, Pp.Link>:
  List.append(&2, Pp.Link, ls1, Pp.Link{n <> at, abs, to} <> ls2)

# p resolves to at, unlooped: the state it reaches is at at, unlooped
def plf.at_end(+L: List<&2, Pp.Link>, +p: List<&2, Tl.Seg>, +at: List<&2, Nat>, reach: {Pp.real(L, p) == Pp.Res{at, False{}} : Pp.Res}) -> {LAReal.prw.cont(LAReal.prw.T(L, p), Nil{}, L) == Pp.Res{at, False{}} : Pp.Res}:
  Equal.trans(Pp.Res, LAReal.prw.cont(LAReal.prw.T(L, p), Nil{}, L), Pp.real(L, p), Pp.Res{at, False{}}, Equal.sym(Pp.Res, Pp.real(L, p), LAReal.prw.cont(LAReal.prw.T(L, p), Nil{}, L), LAReal.prw.real_end(L, p)), reach)

# p n r resolves to x, unlooped: from that state, n r ends at x, unlooped
def plf.name_end(+L: List<&2, Pp.Link>, +p: List<&2, Tl.Seg>, +n: Nat, +r: List<&2, Tl.Seg>, +x: List<&2, Nat>, ok: {Pp.real(L, List.append(&2, Tl.Seg, p, Tl.Name{n} <> r)) == Pp.Res{x, False{}} : Pp.Res}) -> {LAReal.prw.cont(LAReal.prw.T(L, p), Tl.Name{n} <> r, L) == Pp.Res{x, False{}} : Pp.Res}:
  Equal.trans(Pp.Res, LAReal.prw.cont(LAReal.prw.T(L, p), Tl.Name{n} <> r, L), Pp.real(L, List.append(&2, Tl.Seg, p, Tl.Name{n} <> r)), Pp.Res{x, False{}}, Equal.sym(Pp.Res, Pp.real(L, List.append(&2, Tl.Seg, p, Tl.Name{n} <> r)), LAReal.prw.cont(LAReal.prw.T(L, p), Tl.Name{n} <> r, L), LAReal.prw.real_split(L, p, Tl.Name{n} <> r)), ok)

# an absolute link: from a state at at, unlooped, with at most 40 links
# left, n r ends where the target then r resolves from `/`
def plf.abs(t: Nat & Pp.Res, +n: Nat, +at: List<&2, Nat>, +to: List<&2, Tl.Seg>, +r: List<&2, Tl.Seg>, +L: List<&2, Pp.Link>, +x: List<&2, Nat>, le: {Nat.is_le(LAReal.prw.fuel(t), 40n) == True{} : Bool}, +e: {LAReal.prw.cont(t, Nil{}, L) == Pp.Res{at, False{}} : Pp.Res}, fs: {Pp.link.find(L, n <> at) == Some{Pp.Link{n <> at, True{}, to}} : Maybe<&2, Pp.Link>}) -> {LAReal.prw.cont(t, Tl.Name{n} <> r, L) == Pp.Res{x, False{}} : Pp.Res} -> {Pp.go(40n, List.append(&2, Tl.Seg, to, r), L, Nil{}, False{}, Pp.look.at(L, List.append(&2, Tl.Seg, to, r), Nil{})) == Pp.Res{x, False{}} : Pp.Res}:
  match t:
    case (f, q):
      match f:
        case 0n:
          match q:
            case Pp.Res{+a, +b}:
              +ea = Equal.cong(Pp.Res, List<&2, Nat>, z => Pp.Res.at(z), Pp.Res{a, b}, Pp.Res{at, False{}}, e)
              +eb = Equal.cong(Pp.Res, Bool, z => Pp.Res.looped(z), Pp.Res{a, b}, Pp.Res{at, False{}}, e)
              %Equal.sym(List<&2, Nat>, a, at, ea) : {Pp.go(0n, Tl.Name{n} <> r, L, _, b, Pp.look.at(L, Tl.Name{n} <> r, _)) == Pp.Res{x, False{}} : Pp.Res} -> {Pp.go(40n, List.append(&2, Tl.Seg, to, r), L, Nil{}, False{}, Pp.look.at(L, List.append(&2, Tl.Seg, to, r), Nil{})) == Pp.Res{x, False{}} : Pp.Res}
              %Equal.sym(Bool, b, False{}, eb) : {Pp.go(0n, Tl.Name{n} <> r, L, at, _, Pp.look.at(L, Tl.Name{n} <> r, at)) == Pp.Res{x, False{}} : Pp.Res} -> {Pp.go(40n, List.append(&2, Tl.Seg, to, r), L, Nil{}, False{}, Pp.look.at(L, List.append(&2, Tl.Seg, to, r), Nil{})) == Pp.Res{x, False{}} : Pp.Res}
              %Equal.sym(Maybe<&2, Pp.Link>, Pp.link.find(L, n <> at), Some{Pp.Link{n <> at, True{}, to}}, fs) : {Pp.go(0n, Tl.Name{n} <> r, L, at, False{}, _) == Pp.Res{x, False{}} : Pp.Res} -> {Pp.go(40n, List.append(&2, Tl.Seg, to, r), L, Nil{}, False{}, Pp.look.at(L, List.append(&2, Tl.Seg, to, r), Nil{})) == Pp.Res{x, False{}} : Pp.Res}
              h => LAReal.prw.no_loop({Pp.go(40n, List.append(&2, Tl.Seg, to, r), L, Nil{}, False{}, Pp.look.at(L, List.append(&2, Tl.Seg, to, r), Nil{})) == Pp.Res{x, False{}} : Pp.Res}, 0n, r, L, n <> at, Pp.look.at(L, r, n <> at), x, h)
        case 1n++g:
          match q:
            case Pp.Res{+a, +b}:
              +ea = Equal.cong(Pp.Res, List<&2, Nat>, z => Pp.Res.at(z), Pp.Res{a, b}, Pp.Res{at, False{}}, e)
              +eb = Equal.cong(Pp.Res, Bool, z => Pp.Res.looped(z), Pp.Res{a, b}, Pp.Res{at, False{}}, e)
              %Equal.sym(List<&2, Nat>, a, at, ea) : {Pp.go(1n+g, Tl.Name{n} <> r, L, _, b, Pp.look.at(L, Tl.Name{n} <> r, _)) == Pp.Res{x, False{}} : Pp.Res} -> {Pp.go(40n, List.append(&2, Tl.Seg, to, r), L, Nil{}, False{}, Pp.look.at(L, List.append(&2, Tl.Seg, to, r), Nil{})) == Pp.Res{x, False{}} : Pp.Res}
              %Equal.sym(Bool, b, False{}, eb) : {Pp.go(1n+g, Tl.Name{n} <> r, L, at, _, Pp.look.at(L, Tl.Name{n} <> r, at)) == Pp.Res{x, False{}} : Pp.Res} -> {Pp.go(40n, List.append(&2, Tl.Seg, to, r), L, Nil{}, False{}, Pp.look.at(L, List.append(&2, Tl.Seg, to, r), Nil{})) == Pp.Res{x, False{}} : Pp.Res}
              %Equal.sym(Maybe<&2, Pp.Link>, Pp.link.find(L, n <> at), Some{Pp.Link{n <> at, True{}, to}}, fs) : {Pp.go(1n+g, Tl.Name{n} <> r, L, at, False{}, _) == Pp.Res{x, False{}} : Pp.Res} -> {Pp.go(40n, List.append(&2, Tl.Seg, to, r), L, Nil{}, False{}, Pp.look.at(L, List.append(&2, Tl.Seg, to, r), Nil{})) == Pp.Res{x, False{}} : Pp.Res}
              h => LAReal.prw.up_to(40n, g, List.append(&2, Tl.Seg, to, r), L, Nil{}, Pp.look.at(L, List.append(&2, Tl.Seg, to, r), Nil{}), x)(LAReal.prw.le_pred(g, 40n, le))(h)

# a relative link: from a state at at, unlooped, n r ends where the
# target then r ends from there
def plf.rel(t: Nat & Pp.Res, +n: Nat, +at: List<&2, Nat>, +to: List<&2, Tl.Seg>, +r: List<&2, Tl.Seg>, +L: List<&2, Pp.Link>, +x: List<&2, Nat>, +e: {LAReal.prw.cont(t, Nil{}, L) == Pp.Res{at, False{}} : Pp.Res}, fs: {Pp.link.find(L, n <> at) == Some{Pp.Link{n <> at, False{}, to}} : Maybe<&2, Pp.Link>}) -> {LAReal.prw.cont(t, Tl.Name{n} <> r, L) == Pp.Res{x, False{}} : Pp.Res} -> {LAReal.prw.cont(t, List.append(&2, Tl.Seg, to, r), L) == Pp.Res{x, False{}} : Pp.Res}:
  match t:
    case (f, q):
      match f:
        case 0n:
          match q:
            case Pp.Res{+a, +b}:
              +ea = Equal.cong(Pp.Res, List<&2, Nat>, z => Pp.Res.at(z), Pp.Res{a, b}, Pp.Res{at, False{}}, e)
              +eb = Equal.cong(Pp.Res, Bool, z => Pp.Res.looped(z), Pp.Res{a, b}, Pp.Res{at, False{}}, e)
              %Equal.sym(List<&2, Nat>, a, at, ea) : {Pp.go(0n, Tl.Name{n} <> r, L, _, b, Pp.look.at(L, Tl.Name{n} <> r, _)) == Pp.Res{x, False{}} : Pp.Res} -> {Pp.go(0n, List.append(&2, Tl.Seg, to, r), L, _, b, Pp.look.at(L, List.append(&2, Tl.Seg, to, r), _)) == Pp.Res{x, False{}} : Pp.Res}
              %Equal.sym(Bool, b, False{}, eb) : {Pp.go(0n, Tl.Name{n} <> r, L, at, _, Pp.look.at(L, Tl.Name{n} <> r, at)) == Pp.Res{x, False{}} : Pp.Res} -> {Pp.go(0n, List.append(&2, Tl.Seg, to, r), L, at, _, Pp.look.at(L, List.append(&2, Tl.Seg, to, r), at)) == Pp.Res{x, False{}} : Pp.Res}
              %Equal.sym(Maybe<&2, Pp.Link>, Pp.link.find(L, n <> at), Some{Pp.Link{n <> at, False{}, to}}, fs) : {Pp.go(0n, Tl.Name{n} <> r, L, at, False{}, _) == Pp.Res{x, False{}} : Pp.Res} -> {Pp.go(0n, List.append(&2, Tl.Seg, to, r), L, at, False{}, Pp.look.at(L, List.append(&2, Tl.Seg, to, r), at)) == Pp.Res{x, False{}} : Pp.Res}
              h => LAReal.prw.no_loop({Pp.go(0n, List.append(&2, Tl.Seg, to, r), L, at, False{}, Pp.look.at(L, List.append(&2, Tl.Seg, to, r), at)) == Pp.Res{x, False{}} : Pp.Res}, 0n, r, L, n <> at, Pp.look.at(L, r, n <> at), x, h)
        case 1n+g:
          match q:
            case Pp.Res{+a, +b}:
              +ea = Equal.cong(Pp.Res, List<&2, Nat>, z => Pp.Res.at(z), Pp.Res{a, b}, Pp.Res{at, False{}}, e)
              +eb = Equal.cong(Pp.Res, Bool, z => Pp.Res.looped(z), Pp.Res{a, b}, Pp.Res{at, False{}}, e)
              %Equal.sym(List<&2, Nat>, a, at, ea) : {Pp.go(1n+g, Tl.Name{n} <> r, L, _, b, Pp.look.at(L, Tl.Name{n} <> r, _)) == Pp.Res{x, False{}} : Pp.Res} -> {Pp.go(1n+g, List.append(&2, Tl.Seg, to, r), L, _, b, Pp.look.at(L, List.append(&2, Tl.Seg, to, r), _)) == Pp.Res{x, False{}} : Pp.Res}
              %Equal.sym(Bool, b, False{}, eb) : {Pp.go(1n+g, Tl.Name{n} <> r, L, at, _, Pp.look.at(L, Tl.Name{n} <> r, at)) == Pp.Res{x, False{}} : Pp.Res} -> {Pp.go(1n+g, List.append(&2, Tl.Seg, to, r), L, at, _, Pp.look.at(L, List.append(&2, Tl.Seg, to, r), at)) == Pp.Res{x, False{}} : Pp.Res}
              %Equal.sym(Maybe<&2, Pp.Link>, Pp.link.find(L, n <> at), Some{Pp.Link{n <> at, False{}, to}}, fs) : {Pp.go(1n+g, Tl.Name{n} <> r, L, at, False{}, _) == Pp.Res{x, False{}} : Pp.Res} -> {Pp.go(1n+g, List.append(&2, Tl.Seg, to, r), L, at, False{}, Pp.look.at(L, List.append(&2, Tl.Seg, to, r), at)) == Pp.Res{x, False{}} : Pp.Res}
              h => LAReal.prw.more(g, List.append(&2, Tl.Seg, to, r), L, at, Pp.look.at(L, List.append(&2, Tl.Seg, to, r), at), x, h)

def PathPolicy.path_real_link_followed(ls1, n, at, abs, to, ls2, p, r, x, first, reach, ok):
  match abs:
    case True{}:
      plf.abs(LAReal.prw.T(plf.L(ls1, n, at, True{}, to, ls2), p), n, at, to, r, plf.L(ls1, n, at, True{}, to, ls2), x, LAReal.prw.le_T(plf.L(ls1, n, at, True{}, to, ls2), p), plf.at_end(plf.L(ls1, n, at, True{}, to, ls2), p, at, reach), LAReal.prw.find_first(ls1, n <> at, True{}, to, ls2, first))(plf.name_end(plf.L(ls1, n, at, True{}, to, ls2), p, n, r, x, ok))
    case False{}:
      Equal.trans(Pp.Res, Pp.real(plf.L(ls1, n, at, False{}, to, ls2), List.append(&2, Tl.Seg, p, List.append(&2, Tl.Seg, to, r))), LAReal.prw.cont(LAReal.prw.T(plf.L(ls1, n, at, False{}, to, ls2), p), List.append(&2, Tl.Seg, to, r), plf.L(ls1, n, at, False{}, to, ls2)), Pp.Res{x, False{}},
        LAReal.prw.real_split(plf.L(ls1, n, at, False{}, to, ls2), p, List.append(&2, Tl.Seg, to, r)),
        plf.rel(LAReal.prw.T(plf.L(ls1, n, at, False{}, to, ls2), p), n, at, to, r, plf.L(ls1, n, at, False{}, to, ls2), x, plf.at_end(plf.L(ls1, n, at, False{}, to, ls2), p, at, reach), LAReal.prw.find_first(ls1, n <> at, False{}, to, ls2, first))(plf.name_end(plf.L(ls1, n, at, False{}, to, ls2), p, n, r, x, ok)))
