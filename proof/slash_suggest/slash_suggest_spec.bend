# eukhe: the proof of LAW slash_suggest_spec
#
# PROOF: the nearest candidate is the spec's (LA.ssb.nearest: each distance
# is the spec's, each tie kept the same way); the limit of the typed
# name's UTF-8 length is the spec's (LA.ssb.bytes, LA.ssb.limit).

import Base
import ../../bend/slash_suggest.bend as Ss
import ../../bend/ffi_slash_suggest.bend as FSs
import ../../bend/skill_load.bend as Sl
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/slash_suggest.bend as SlashSuggest
import ./base.bend as LA

def sss.within(b: Bool, j: Nat) -> {Ss.within(b, j) == SlashSuggest.sp_within(b, j) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sss.pick(+w: String, m: Maybe<&2, Ss.Near>) -> {Ss.pick(w, m) == SlashSuggest.sp_suggest.of(w, m) : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      match n:
        case Ss.Near{+j, +e}:
          %Equal.sym(Nat, Sl.bytes(w, 0n), Nat.add(SlashSuggest.sp_bytes(w), 0n), LA.ssb.bytes(w, 0n)) : {Ss.within(Nat.is_le(e, Ss.limit(_)), j) == SlashSuggest.sp_within(Nat.is_le(e, SlashSuggest.sp_limit(SlashSuggest.sp_bytes(w))), j) : Maybe<&2, Nat>}
          %Equal.sym(Nat, Nat.add(SlashSuggest.sp_bytes(w), 0n), SlashSuggest.sp_bytes(w), LA.ssb.add_zero(SlashSuggest.sp_bytes(w))) : {Ss.within(Nat.is_le(e, Ss.limit(_)), j) == SlashSuggest.sp_within(Nat.is_le(e, SlashSuggest.sp_limit(SlashSuggest.sp_bytes(w))), j) : Maybe<&2, Nat>}
          %Equal.sym(Nat, Ss.limit(SlashSuggest.sp_bytes(w)), SlashSuggest.sp_limit(SlashSuggest.sp_bytes(w)), LA.ssb.limit(SlashSuggest.sp_bytes(w))) : {Ss.within(Nat.is_le(e, _), j) == SlashSuggest.sp_within(Nat.is_le(e, SlashSuggest.sp_limit(SlashSuggest.sp_bytes(w))), j) : Maybe<&2, Nat>}
          sss.within(Nat.is_le(e, SlashSuggest.sp_limit(SlashSuggest.sp_bytes(w))), j)

def SlashSuggest.slash_suggest_spec(w, cs):
  %Equal.sym(Maybe<&2, Ss.Near>, Ss.nearest(w, cs), SlashSuggest.sp_first(w, cs), LA.ssb.nearest(w, cs)) : {Ss.pick(w, _) == SlashSuggest.sp_suggest(w, cs) : Maybe<&2, Nat>}
  sss.pick(w, SlashSuggest.sp_first(w, cs))
