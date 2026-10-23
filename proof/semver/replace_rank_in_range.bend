# eukhe: the proof of LAW replace_rank_in_range

import Base
import ../../bend/semver.bend as Sv
import ../../bend/replace.bend as Rp
import ../../LAWS.bend as Laws
import ../base.bend as L

def rk.ir(+a: Nat, +b: Nat, -t: Nat, +c: Nat, ok: Bool, eq: {Bool.and(Laws.rank_spec.short(a), Bool.and(Laws.rank_spec.short(b), Laws.rank_spec.short(c))) == ok : Bool}) -> {Laws.rank_spec.in_range(Laws.rank_spec.keep(ok, a, b, t, c)) == True{} : Bool}:
  match ok:
    case True{}:
      eq
    case False{}:
      {==}

def rk.in_range_of(m: Maybe<&2, Sv.Ver>, -t: Nat) -> {Laws.rank_spec.in_range(Laws.rank_spec.of(m, t)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      match v:
        case Sv.Ver{+a, +b, +c}:
          rk.ir(a, b, t, c, Bool.and(Laws.rank_spec.short(a), Bool.and(Laws.rank_spec.short(b), Laws.rank_spec.short(c))), {==})

def rk.in_range_cap(short: Bool, +s: String) -> {Laws.rank_spec.in_range(Laws.rank_spec.cap(short, s)) == True{} : Bool}:
  match short:
    case True{}:
      rk.in_range_of(Sv.Ver.parse(Laws.rank_spec.core(s)), Laws.rank_spec.tier(s))
    case False{}:
      {==}

def Laws.replace_rank_in_range(s):
  %Equal.sym(List<&2, Nat>, Rp.rank(s), Laws.rank_spec(s), L.rk.rank(s)) : {Laws.rank_spec.in_range(_) == True{} : Bool}
  rk.in_range_cap(Nat.is_le(String.length(s), 64n), s)
