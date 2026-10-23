# eukhe: the proof of LAW replace_rank_in_range

import Base
import ../../bend/replace.bend as Rp
import ../../bend/semver.bend as Sv
import ../../laws/base.bend as LawsBase
import ../../laws/replace.bend as Replace
import ../../laws/semver.bend as Semver
import ../base/replace.bend as LReplace

def rk.ir(+a: Nat, +b: Nat, -t: Nat, +c: Nat, ok: Bool, eq: {Bool.and(LawsBase.rank_spec.short(a), Bool.and(LawsBase.rank_spec.short(b), LawsBase.rank_spec.short(c))) == ok : Bool}) -> {Semver.rank_spec.in_range(Replace.rank_spec.keep(ok, a, b, t, c)) == True{} : Bool}:
  match ok:
    case True{}:
      eq
    case False{}:
      {==}

def rk.in_range_of(m: Maybe<&2, Sv.Ver>, -t: Nat) -> {Semver.rank_spec.in_range(Replace.rank_spec.of(m, t)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      match v:
        case Sv.Ver{+a, +b, +c}:
          rk.ir(a, b, t, c, Bool.and(LawsBase.rank_spec.short(a), Bool.and(LawsBase.rank_spec.short(b), LawsBase.rank_spec.short(c))), {==})

def rk.in_range_cap(short: Bool, +s: String) -> {Semver.rank_spec.in_range(Replace.rank_spec.cap(short, s)) == True{} : Bool}:
  match short:
    case True{}:
      rk.in_range_of(Sv.Ver.parse(Replace.rank_spec.core(s)), Replace.rank_spec.tier(s))
    case False{}:
      {==}

def Semver.replace_rank_in_range(s):
  %Equal.sym(List<&2, Nat>, Rp.rank(s), Replace.rank_spec(s), LReplace.rk.rank(s)) : {Semver.rank_spec.in_range(_) == True{} : Bool}
  rk.in_range_cap(Nat.is_le(String.length(s), 64n), s)
