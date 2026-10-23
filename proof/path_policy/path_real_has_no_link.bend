# eukhe: the proof of LAW path_real_has_no_link

import Base
import ../../bend/tools.bend as Tl
import ../../bend/path_policy.bend as Pp
import ../../LAWS.bend as Laws
import ./base.bend as LA

# 1. The real path
# ----------------

# the invariant of a resolution's result
def pp.ok(+ls: List<&2, Pp.Link>, +r: Pp.Res) -> Bool:
  Bool.or(Pp.Res.looped(r), Pp.linkfree(ls, Pp.Res.at(r)))

# `..` keeps a link-free prefix link-free
def pp.lf_up(+ls: List<&2, Pp.Link>, at: List<&2, Nat>, h: {Pp.linkfree(ls, at) == True{} : Bool}) -> {Pp.linkfree(ls, Pp.up(at)) == True{} : Bool}:
  match at:
    case Nil{}:
      {==}
    case a <> +above:
      LA.pp.and_r(Maybe.is_none(&2, Pp.Link, Pp.link.find(ls, a <> above)), Pp.linkfree(ls, above), h)

def pp.inv_up(looped: Bool, +ls: List<&2, Pp.Link>, +at: List<&2, Nat>, h: {Bool.or(looped, Pp.linkfree(ls, at)) == True{} : Bool}) -> {Bool.or(looped, Pp.linkfree(ls, Pp.up(at))) == True{} : Bool}:
  match looped:
    case True{}:
      {==}
    case False{}:
      pp.lf_up(ls, at, h)

# a name pushed while looped or with no link at it keeps the invariant
def pp.inv_name(looped: Bool, m: Maybe<&2, Pp.Link>, +lf: Bool, h: {Bool.or(looped, lf) == True{} : Bool}) -> {Bool.or(Bool.or(looped, Maybe.is_some(&2, Pp.Link, m)), Bool.and(Maybe.is_none(&2, Pp.Link, m), lf)) == True{} : Bool}:
  match looped:
    case True{}:
      {==}
    case False{}:
      match m:
        case None{}:
          h
        case Some{l}:
          {==}

# a name with no link at it keeps a link-free prefix link-free
def pp.inv_none(+ls: List<&2, Pp.Link>, +n: Nat, +at: List<&2, Nat>, +looped: Bool, e: {None{} == Pp.link.find(ls, n <> at) : Maybe<&2, Pp.Link>}, h: {Bool.or(looped, Pp.linkfree(ls, at)) == True{} : Bool}) -> {Bool.or(looped, Pp.linkfree(ls, n <> at)) == True{} : Bool}:
  %e : {Bool.or(looped, Bool.and(Maybe.is_none(&2, Pp.Link, _), Pp.linkfree(ls, at))) == True{} : Bool}
  h

def pp.go_lf(fuel: Nat, segs: List<&2, Tl.Seg>, +ls: List<&2, Pp.Link>, +at: List<&2, Nat>, +looped: Bool, +look: Maybe<&2, Pp.Link>, +lk: {look == Pp.look.at(ls, segs, at) : Maybe<&2, Pp.Link>}, +h: {Bool.or(looped, Pp.linkfree(ls, at)) == True{} : Bool}) -> {pp.ok(ls, Pp.go(fuel, segs, ls, at, looped, look)) == True{} : Bool}:
  match fuel:
    case 0n:
      match segs:
        case Nil{}:
          h
        case s <> +rest:
          match s:
            case Tl.Name{+n}:
              %Equal.sym(Maybe<&2, Pp.Link>, look, Pp.link.find(ls, n <> at), lk) : {pp.ok(ls, Pp.go(0n, Tl.Name{n} <> rest, ls, at, looped, _)) == True{} : Bool}
              pp.go_lf(0n, rest, ls, n <> at, Bool.or(looped, Maybe.is_some(&2, Pp.Link, Pp.link.find(ls, n <> at))), Pp.look.at(ls, rest, n <> at), {==}, pp.inv_name(looped, Pp.link.find(ls, n <> at), Pp.linkfree(ls, at), h))
            case Tl.Up{}:
              pp.go_lf(0n, rest, ls, Pp.up(at), looped, Pp.look.at(ls, rest, Pp.up(at)), {==}, pp.inv_up(looped, ls, at, h))
            case Tl.Here{}:
              pp.go_lf(0n, rest, ls, at, looped, Pp.look.at(ls, rest, at), {==}, h)
    case 1n+f:
      match segs:
        case Nil{}:
          h
        case s <> +rest:
          match s:
            case Tl.Name{+n}:
              match look:
                case None{}:
                  pp.go_lf(1n+f, rest, ls, n <> at, looped, Pp.look.at(ls, rest, n <> at), {==}, pp.inv_none(ls, n, at, looped, lk, h))
                case Some{l}:
                  match l:
                    case Pp.Link{la, abs, +to}:
                      match abs:
                        case True{}:
                          pp.go_lf(f, List.append(&2, Tl.Seg, to, rest), ls, Nil{}, looped, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), Nil{}), {==}, LA.pp.or_tr(looped, True{}, {==}))
                        case False{}:
                          pp.go_lf(f, List.append(&2, Tl.Seg, to, rest), ls, at, looped, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), at), {==}, h)
            case Tl.Up{}:
              pp.go_lf(1n+f, rest, ls, Pp.up(at), looped, Pp.look.at(ls, rest, Pp.up(at)), {==}, pp.inv_up(looped, ls, at, h))
            case Tl.Here{}:
              pp.go_lf(1n+f, rest, ls, at, looped, Pp.look.at(ls, rest, at), {==}, h)

def pp.path_real_has_no_link(+ls: List<&2, Pp.Link>, +segs: List<&2, Tl.Seg>) -> {Bool.or(Pp.Res.looped(Pp.real(ls, segs)), Pp.linkfree(ls, Pp.Res.at(Pp.real(ls, segs)))) == True{} : Bool}:
  pp.go_lf(Pp.max_links(), segs, ls, Nil{}, False{}, Pp.look.at(ls, segs, Nil{}), {==}, {==})

# (G1) Path policy

def Laws.path_real_has_no_link(ls, segs):
  pp.path_real_has_no_link(ls, segs)
