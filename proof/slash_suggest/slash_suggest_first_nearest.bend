# eukhe: the proof of LAW slash_suggest_first_nearest
#
# PROOF: the code's one pass (a right fold keeping the later candidate
# only when strictly nearer) answers the spec's two passes: by induction on
# the candidates, its nearest is the first candidate at the fewest edits
# (ssn.nearest, with LA.ssb.dist for each distance and the Nat comparison
# lemmas for the tie); its limit test of the typed name's UTF-8 bytes is
# sp_ok (LSk.sl.bytes0, LA.ssb.ok).

import Base
import ../../bend/slash_suggest.bend as Ss
import ../../bend/skill_load.bend as Sl
import ../../laws/slash_suggest.bend as SlashSuggest
import ../../laws/skill_load.bend as SkillLoad
import ../skill_load/base.bend as LSk
import ./base.bend as LA

# the nearest candidate the spec names: the first one at the fewest edits m
def ssn.near(+w: String, cs: List<&2, String>, m: Maybe<&2, Nat>) -> Maybe<&2, Ss.Near>:
  match m:
    case None{}:
      None{}
    case Some{+e}:
      Some{Ss.Near{SlashSuggest.sp_at(w, e, cs), e}}

def ssn.keep(+w: String, +x: String, +t: List<&2, String>, +e: Nat, b: Bool, +eb: {Nat.is_lt(e, SlashSuggest.sp_lev(w, x)) == b : Bool}) -> {Some{Ss.near.keep(b, SlashSuggest.sp_lev(w, x), Ss.Near{SlashSuggest.sp_at(w, e, t), e})} == ssn.near(w, x <> t, Some{SlashSuggest.sp_low.min(SlashSuggest.sp_lev(w, x), Some{e})}) : Maybe<&2, Ss.Near>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_le(SlashSuggest.sp_lev(w, x), e), False{}, LA.ssb.lt_nle(SlashSuggest.sp_lev(w, x), e, eb)) : {Some{Ss.Near{Nat.add(1n, SlashSuggest.sp_at(w, e, t)), e}} == Some{Ss.Near{SlashSuggest.sp_pick(Nat.is_eq(SlashSuggest.sp_lev(w, x), SlashSuggest.sp_pick(_, SlashSuggest.sp_lev(w, x), e)), 0n, Nat.add(1n, SlashSuggest.sp_at(w, SlashSuggest.sp_pick(_, SlashSuggest.sp_lev(w, x), e), t))), SlashSuggest.sp_pick(_, SlashSuggest.sp_lev(w, x), e)}} : Maybe<&2, Ss.Near>}
      %Equal.sym(Bool, Nat.is_eq(SlashSuggest.sp_lev(w, x), e), False{}, LA.ssb.lt_ne(SlashSuggest.sp_lev(w, x), e, eb)) : {Some{Ss.Near{Nat.add(1n, SlashSuggest.sp_at(w, e, t)), e}} == Some{Ss.Near{SlashSuggest.sp_pick(_, 0n, Nat.add(1n, SlashSuggest.sp_at(w, e, t))), e}} : Maybe<&2, Ss.Near>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_le(SlashSuggest.sp_lev(w, x), e), True{}, LA.ssb.nlt_le(SlashSuggest.sp_lev(w, x), e, eb)) : {Some{Ss.Near{0n, SlashSuggest.sp_lev(w, x)}} == Some{Ss.Near{SlashSuggest.sp_pick(Nat.is_eq(SlashSuggest.sp_lev(w, x), SlashSuggest.sp_pick(_, SlashSuggest.sp_lev(w, x), e)), 0n, Nat.add(1n, SlashSuggest.sp_at(w, SlashSuggest.sp_pick(_, SlashSuggest.sp_lev(w, x), e), t))), SlashSuggest.sp_pick(_, SlashSuggest.sp_lev(w, x), e)}} : Maybe<&2, Ss.Near>}
      %Equal.sym(Bool, Nat.is_eq(SlashSuggest.sp_lev(w, x), SlashSuggest.sp_lev(w, x)), True{}, LA.ssb.eq_refl(SlashSuggest.sp_lev(w, x))) : {Some{Ss.Near{0n, SlashSuggest.sp_lev(w, x)}} == Some{Ss.Near{SlashSuggest.sp_pick(_, 0n, Nat.add(1n, SlashSuggest.sp_at(w, SlashSuggest.sp_lev(w, x), t))), SlashSuggest.sp_lev(w, x)}} : Maybe<&2, Ss.Near>}
      {==}

# one step of the fold: the head x before the rest's answer m
def ssn.step(+w: String, +x: String, +t: List<&2, String>, m: Maybe<&2, Nat>) -> {Some{Ss.near.of(SlashSuggest.sp_lev(w, x), ssn.near(w, t, m))} == ssn.near(w, x <> t, Some{SlashSuggest.sp_low.min(SlashSuggest.sp_lev(w, x), m)}) : Maybe<&2, Ss.Near>}:
  match m:
    case None{}:
      +d = SlashSuggest.sp_lev(w, x)
      %Equal.sym(Bool, Nat.is_eq(d, d), True{}, LA.ssb.eq_refl(d)) : {Some{Ss.Near{0n, d}} == Some{Ss.Near{SlashSuggest.sp_pick(_, 0n, Nat.add(1n, SlashSuggest.sp_at(w, d, t))), d}} : Maybe<&2, Ss.Near>}
      {==}
    case Some{+e}:
      ssn.keep(w, x, t, e, Nat.is_lt(e, SlashSuggest.sp_lev(w, x)), {==})

# the code's nearest is the spec's first candidate at the fewest edits
def ssn.nearest(+w: String, cs: List<&2, String>) -> {Ss.nearest(w, cs) == ssn.near(w, cs, SlashSuggest.sp_low(w, cs)) : Maybe<&2, Ss.Near>}:
  match cs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(Maybe<&2, Ss.Near>, Ss.nearest(w, t), ssn.near(w, t, SlashSuggest.sp_low(w, t)), ssn.nearest(w, t)) : {Some{Ss.near.of(Ss.dist(w, x), _)} == ssn.near(w, x <> t, SlashSuggest.sp_low(w, x <> t)) : Maybe<&2, Ss.Near>}
      %Equal.sym(Nat, Ss.dist(w, x), SlashSuggest.sp_lev(w, x), LA.ssb.dist(w, x)) : {Some{Ss.near.of(_, ssn.near(w, t, SlashSuggest.sp_low(w, t)))} == ssn.near(w, x <> t, SlashSuggest.sp_low(w, x <> t)) : Maybe<&2, Ss.Near>}
      ssn.step(w, x, t, SlashSuggest.sp_low(w, t))

def ssn.within(b: Bool, j: Nat) -> {Ss.within(b, j) == SlashSuggest.sp_suggest.ok(b, j) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ssn.pick(+w: String, +cs: List<&2, String>, m: Maybe<&2, Nat>) -> {Ss.pick(w, ssn.near(w, cs, m)) == SlashSuggest.sp_suggest.low(w, cs, m) : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{+e}:
      %Equal.sym(Nat, Sl.bytes(w, 0n), SkillLoad.sl_bytes(w), LSk.sl.bytes0(w)) : {Ss.within(Nat.is_le(e, Ss.limit(_)), SlashSuggest.sp_at(w, e, cs)) == SlashSuggest.sp_suggest.ok(SlashSuggest.sp_ok(e, SkillLoad.sl_bytes(w)), SlashSuggest.sp_at(w, e, cs)) : Maybe<&2, Nat>}
      %LA.ssb.ok(e, SkillLoad.sl_bytes(w)) : {Ss.within(Nat.is_le(e, Ss.limit(SkillLoad.sl_bytes(w))), SlashSuggest.sp_at(w, e, cs)) == SlashSuggest.sp_suggest.ok(_, SlashSuggest.sp_at(w, e, cs)) : Maybe<&2, Nat>}
      ssn.within(Nat.is_le(e, Ss.limit(SkillLoad.sl_bytes(w))), SlashSuggest.sp_at(w, e, cs))

def SlashSuggest.slash_suggest_first_nearest(w, cs):
  %Equal.sym(Maybe<&2, Ss.Near>, Ss.nearest(w, cs), ssn.near(w, cs, SlashSuggest.sp_low(w, cs)), ssn.nearest(w, cs)) : {Ss.pick(w, _) == SlashSuggest.sp_suggest(w, cs) : Maybe<&2, Nat>}
  ssn.pick(w, cs, SlashSuggest.sp_low(w, cs))
