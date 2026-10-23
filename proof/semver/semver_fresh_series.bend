# eukhe: the proof of LAW semver_fresh_series

import Base
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver
import ../base/bool/and.bend as LBoolAnd
import ../base/bool/misc.bend as LBoolMisc
import ./base.bend as LA

def semver.ps.not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      LBoolMisc.semver.ps.absurdF({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def ps.top_none(+s: Sv.Ver, tags: List<&2, String>, +h: {Sv.Rel.none(s, tags) == True{} : Bool}) -> {None{} == Sv.Rel.top(s, tags) : Maybe<&2, Nat>}:
  match tags:
    case Nil{}:
      {==}
    case +t <> +r:
      %ps.top_none(s, r, LBoolAnd.semver.ps.and_r(Bool.not(Sv.Rel.ofs(s, t)), Sv.Rel.none(s, r), h)) : {None{} == Sv.Rel.add(s, Sv.Tag.ver(t), _) : Maybe<&2, Nat>}
      LA.ps.add_skip(s, Sv.Tag.ver(t), None{}, semver.ps.not_t(Sv.Rel.ofs(s, t), LBoolAnd.semver.ps.and_l(Bool.not(Sv.Rel.ofs(s, t)), Sv.Rel.none(s, r), h)))

def ps.fresh(+a: Nat, +b: Nat, +c: Nat, +tags: List<&2, String>, none: {Sv.Rel.none(Sv.Ver{a, b, c}, tags) == True{} : Bool}) -> {Sv.Rel.next(Sv.Ver{a, b, c}, tags) == Sv.Ver{a, b, 0n} : Sv.Ver}:
  %ps.top_none(Sv.Ver{a, b, c}, tags, none) : {Sv.Ver{a, b, Sv.Rel.after(_)} == Sv.Ver{a, b, 0n} : Sv.Ver}
  {==}

def Semver.semver_fresh_series(a, b, c, tags, none):
  ps.fresh(a, b, c, tags, none)
