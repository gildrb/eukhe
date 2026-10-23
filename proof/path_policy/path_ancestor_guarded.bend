# eukhe: the proof of LAW path_ancestor_guarded

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy.bend as PathPolicy
import ./base.bend as LA

def pp.pick_guarded(sec: Bool, ins: Bool) -> {Pp.Cls.guarded(Pp.cls.pick(sec, True{}, ins)) == True{} : Bool}:
  match sec:
    case True{}:
      {==}
    case False{}:
      {==}

def pp.demote_guarded(c: Pp.Cls, looped: Bool, h: {Pp.Cls.guarded(c) == True{} : Bool}) -> {Pp.Cls.guarded(Pp.demote(c, looped)) == True{} : Bool}:
  match c:
    case Pp.Inside{}:
      LA.pp.absurdF({Pp.Cls.guarded(Pp.demote(Pp.Inside{}, looped)) == True{} : Bool}, h)
    case Pp.Outside{}:
      LA.pp.absurdF({Pp.Cls.guarded(Pp.demote(Pp.Outside{}, looped)) == True{} : Bool}, h)
    case Pp.Protected{}:
      {==}
    case Pp.Secret{}:
      {==}

def pp.anc_res(+pol: Pp.Pol, r: Pp.Res, anc: {Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(Pp.Pol.rules(pol)), Pp.Pol.secret(pol)), Pp.Res.at(r)) == True{} : Bool}) -> {Pp.Cls.guarded(Pp.class_res(pol, r)) == True{} : Bool}:
  match r:
    case Pp.Res{+at, looped}:
      +sec = Pp.any_under(Pp.Pol.secret(pol), at)
      +ins = Maybe.is_some(&2, List<&2, Nat>, Pp.root.of(Pp.Pol.roots(pol), at))
      +hp = LA.pp.or_tr(Pp.any_covers(Pp.Pol.rules(pol), at, Pp.below(at, Pp.root.of(Pp.Pol.roots(pol), at))), Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(Pp.Pol.rules(pol)), Pp.Pol.secret(pol)), at), anc)
      +g = pp.pick_guarded(sec, ins)
      %Equal.sym(Bool, Pp.protects(pol, at), True{}, hp) : {Pp.Cls.guarded(Pp.demote(Pp.cls.pick(sec, _, ins), looped)) == True{} : Bool}
      pp.demote_guarded(Pp.cls.pick(sec, True{}, ins), looped, g)

def pp.path_ancestor_guarded(+pol: Pp.Pol, +ls: List<&2, Pp.Link>, +segs: List<&2, Tl.Seg>, anc: {Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(Pp.Pol.rules(pol)), Pp.Pol.secret(pol)), Pp.Res.at(Pp.real(ls, segs))) == True{} : Bool}) -> {Pp.Cls.guarded(Pp.class(pol, ls, segs)) == True{} : Bool}:
  pp.anc_res(pol, Pp.real(ls, segs), anc)

def PathPolicy.path_ancestor_guarded(pol, ls, segs, anc):
  pp.path_ancestor_guarded(pol, ls, segs, anc)
