# eukhe: the proof of LAW semver_release_progress

import Base
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver
import ../base/logic/bool.bend as LLogicBool
import ./base.bend as LA

# The next release
# ----------------

def ps.app_snoc(xs: List<&2, String>, +a: String, +ys: List<&2, String>) -> {List.append(&2, String, List.append(&2, String, xs, [a]), ys) == List.append(&2, String, xs, a <> ys) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      Equal.cong(List<&2, String>, List<&2, String>, zs => x <> zs, List.append(&2, String, List.append(&2, String, r, [a]), ys), List.append(&2, String, r, a <> ys), ps.app_snoc(r, a, ys))

def ps.older_of(+s: Sv.Ver, +pre: List<&2, String>, +t: String, +r: List<&2, String>, m: Maybe<&2, Sv.Ver>, em: {Sv.Tag.ver(t) == m : Maybe<&2, Sv.Ver>}, h: {Sv.Rel.only.of(s, m) == True{} : Bool}) -> {True{} == Sv.Rel.older(Sv.Rel.next(s, List.append(&2, String, pre, t <> r)), m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+v}:
      Equal.sym(Bool, Sv.Ver.lt(v, Sv.Rel.next(s, List.append(&2, String, pre, t <> r))), True{}, LA.ps.next_newer(s, pre, t, r, v, em, h))

def ps.newest_only(rest: List<&2, String>, +s: Sv.Ver, +pre: List<&2, String>, +h: {Sv.Rel.only(s, rest) == True{} : Bool}) -> {True{} == Sv.Rel.newest(Sv.Rel.next(s, List.append(&2, String, pre, rest)), rest) : Bool}:
  match rest:
    case Nil{}:
      {==}
    case +t <> +r:
      %ps.older_of(s, pre, t, r, Sv.Tag.ver(t), {==}, LLogicBool.semver.ps.and_l(Sv.Rel.only.of(s, Sv.Tag.ver(t)), Sv.Rel.only(s, r), h)) : {True{} == Bool.and(_, Sv.Rel.newest(Sv.Rel.next(s, List.append(&2, String, pre, t <> r)), r)) : Bool}
      %ps.app_snoc(pre, t, r) : {True{} == Sv.Rel.newest(Sv.Rel.next(s, _), r) : Bool}
      ps.newest_only(r, s, List.append(&2, String, pre, [t]), LLogicBool.semver.ps.and_r(Sv.Rel.only.of(s, Sv.Tag.ver(t)), Sv.Rel.only(s, r), h))

# with only tags of the series, the workspace version X.Y.0 releases the
# next release
def ps.progress(c: String, +a: Nat, +b: Nat, +tags: List<&2, String>, parsed: {Sv.Ver.parse(c) == Some{Sv.Ver{a, b, 0n}} : Maybe<&2, Sv.Ver>}, only: {Sv.Rel.only(Sv.Ver{a, b, 0n}, tags) == True{} : Bool}) -> {Sv.Rel.release(c, tags) == Some{Sv.Rel.next(Sv.Ver{a, b, 0n}, tags)} : Maybe<&2, Sv.Ver>}:
  %Equal.sym(Maybe<&2, Sv.Ver>, Sv.Ver.parse(c), Some{Sv.Ver{a, b, 0n}}, parsed) : {Sv.Rel.release.of(_, tags) == Some{Sv.Rel.next(Sv.Ver{a, b, 0n}, tags)} : Maybe<&2, Sv.Ver>}
  %ps.newest_only(tags, Sv.Ver{a, b, 0n}, Nil{}, only) : {Sv.Rel.guard(_, Sv.Rel.next(Sv.Ver{a, b, 0n}, tags)) == Some{Sv.Rel.next(Sv.Ver{a, b, 0n}, tags)} : Maybe<&2, Sv.Ver>}
  {==}

def Semver.semver_release_progress(c, a, b, tags, parsed, only):
  ps.progress(c, a, b, tags, parsed, only)
