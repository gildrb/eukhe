# eukhe: the laws of area effort

import Base
import ../bend/effort.bend as Ef
import ../bend/ffi_effort.bend as FEf
import ../bend/infer.bend as If
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (S10) Reasoning depth
# ---------------------
# docs/inference.md S10, the model in bend/effort.bend. Every input is
# free: any model, reasoning or not, with any thinking-level map (each
# entry missing, null or a wire string); any level; any stored level and
# default; any model switches, sets and cycle steps, in any order.

# LAW effort_offered_plain: a model without reasoning offers off only, whatever its map
law effort_offered_plain:
  for +map: Ef.LvMap
  {Ef.offered(Ef.Mdl{False{}, map}) == [Ef.Off{}] : List<&2, Ef.Lv>}

# LAW effort_offered_null: a reasoning model never offers a level with a null entry
law effort_offered_null:
  for +map: Ef.LvMap
  for +l: Ef.Lv
  for null: {Ef.entry(l, map) == Ef.Null{} : Ef.Ent}
  {Ef.has(Ef.offered(Ef.Mdl{True{}, map}), l) == False{} : Bool}

# LAW effort_offered_ext: a model offers xhigh or max only with a wire entry for it
law effort_offered_ext:
  for r: Bool
  for +map: Ef.LvMap
  for +l: Ef.Lv
  for x: {Ef.ext(l) == True{} : Bool}
  for in: {Ef.has(Ef.offered(Ef.Mdl{r, map}), l) == True{} : Bool}
  {Ef.entry(l, map) == Ef.Wire{} : Ef.Ent}

# LAW effort_offered_kept: a reasoning model offers every level that its map keeps (a wire
# entry, or a missing entry below xhigh)
law effort_offered_kept:
  for +map: Ef.LvMap
  for +l: Ef.Lv
  for k: {Ef.keep(map, l) == True{} : Bool}
  {Ef.has(Ef.offered(Ef.Mdl{True{}, map}), l) == True{} : Bool}

# LAW effort_offered_asc: the offered levels are strictly ascending in ladder order: no
# level comes twice
law effort_offered_asc:
  for m: Ef.Mdl
  {Ef.asc(Ef.offered(m)) == True{} : Bool}

# LAW effort_clamp_offered: when the model offers a level, the clamp of any level is an
# offered level (so is the level after a model switch)
law effort_clamp_offered:
  for +m: Ef.Mdl
  for +l: Ef.Lv
  for ne: {Ef.empty(Ef.offered(m)) == False{} : Bool}
  {Ef.has(Ef.offered(m), Ef.clamp(m, l)) == True{} : Bool}

# LAW effort_clamp_keeps: the clamp keeps an offered level
law effort_clamp_keeps:
  for +m: Ef.Mdl
  for +l: Ef.Lv
  for in: {Ef.has(Ef.offered(m), l) == True{} : Bool}
  {Ef.clamp(m, l) == l : Ef.Lv}

# LAW effort_clamp_idem: a second clamp changes nothing, also when the model offers no level
law effort_clamp_idem:
  for +m: Ef.Mdl
  for +l: Ef.Lv
  {Ef.clamp(m, Ef.clamp(m, l)) == Ef.clamp(m, l) : Ef.Lv}

# LAW effort_cycle_still: with fewer than two offered levels a cycle step changes nothing
law effort_cycle_still:
  for +m: Ef.Mdl
  for +l: Ef.Lv
  for +d: Ef.Dir
  for few: {Ef.two(Ef.offered(m)) == False{} : Bool}
  {Ef.cycle(m, l, d) == None{} : Maybe<&2, Ef.Lv>}

# LAW effort_cycle_next: forward from an offered level gives the next offered level
law effort_cycle_next:
  for +m: Ef.Mdl
  for +pre: List<&2, Ef.Lv>
  for +a: Ef.Lv
  for +b: Ef.Lv
  for +post: List<&2, Ef.Lv>
  for +split: {Ef.offered(m) == List.append(&2, Ef.Lv, pre, a <> b <> post) : List<&2, Ef.Lv>}
  {Ef.cycle(m, a, Ef.Forward{}) == Some{b} : Maybe<&2, Ef.Lv>}

# LAW effort_cycle_wrap: forward from the last offered level wraps to the first
law effort_cycle_wrap:
  for +m: Ef.Mdl
  for +h: Ef.Lv
  for +pre: List<&2, Ef.Lv>
  for +z: Ef.Lv
  for +split: {Ef.offered(m) == List.append(&2, Ef.Lv, h <> pre, [z]) : List<&2, Ef.Lv>}
  {Ef.cycle(m, z, Ef.Forward{}) == Some{h} : Maybe<&2, Ef.Lv>}

# LAW effort_cycle_prev: backward from an offered level gives the offered level before it
law effort_cycle_prev:
  for +m: Ef.Mdl
  for +pre: List<&2, Ef.Lv>
  for +a: Ef.Lv
  for +b: Ef.Lv
  for +post: List<&2, Ef.Lv>
  for +split: {Ef.offered(m) == List.append(&2, Ef.Lv, pre, a <> b <> post) : List<&2, Ef.Lv>}
  {Ef.cycle(m, b, Ef.Backward{}) == Some{a} : Maybe<&2, Ef.Lv>}

# LAW effort_cycle_wrap_back: backward from the first offered level wraps to the last
law effort_cycle_wrap_back:
  for +m: Ef.Mdl
  for +h: Ef.Lv
  for +pre: List<&2, Ef.Lv>
  for +z: Ef.Lv
  for split: {Ef.offered(m) == List.append(&2, Ef.Lv, h <> pre, [z]) : List<&2, Ef.Lv>}
  {Ef.cycle(m, h, Ef.Backward{}) == Some{z} : Maybe<&2, Ef.Lv>}

# LAW effort_cycle_inverse: a backward step undoes a forward step from an offered level
law effort_cycle_inverse:
  for +m: Ef.Mdl
  for +l: Ef.Lv
  for in: {Ef.has(Ef.offered(m), l) == True{} : Bool}
  {Ef.turn(m, Ef.turn(m, l, Ef.Forward{}), Ef.Backward{}) == l : Ef.Lv}

# LAW effort_cycle_inverse_back: a forward step undoes a backward step from an offered level
law effort_cycle_inverse_back:
  for +m: Ef.Mdl
  for +l: Ef.Lv
  for in: {Ef.has(Ef.offered(m), l) == True{} : Bool}
  {Ef.turn(m, Ef.turn(m, l, Ef.Backward{}), Ef.Forward{}) == l : Ef.Lv}

# LAW effort_unset_default: a session with no stored level shows `default`, never off
law effort_unset_default:
  for +mo: Maybe<&2, Ef.Mdl>
  {Ef.shown(Ef.Sess{mo, None{}}) == Ef.Default{} : Ef.Shown}

# LAW effort_settle_offered: open settles the stored level on an offered level when the model
# offers one
law effort_settle_offered:
  for +m: Ef.Mdl
  for +st: Maybe<&2, Ef.Lv>
  for +dflt: Ef.Lv
  for +k: Ef.Lv
  for ne: {Ef.empty(Ef.offered(m)) == False{} : Bool}
  for settled: {Ef.Sess.stored(Ef.open(Ef.Sess{Some{m}, st}, dflt)) == Some{k} : Maybe<&2, Ef.Lv>}
  {Ef.has(Ef.offered(m), k) == True{} : Bool}

# LAW effort_stored_is_sent: after open and any actions, the session stores the level it sends
law effort_stored_is_sent:
  for +s: Ef.Sess
  for +dflt: Ef.Lv
  for +acts: List<&2, Ef.Act>
  {Ef.Sess.stored(Ef.run(acts, Ef.open(s, dflt))) == Some{Ef.sent(Ef.run(acts, Ef.open(s, dflt)))} : Maybe<&2, Ef.Lv>}

# LAW effort_shown_is_sent: after open and any actions, the display shows the level the
# session sends
law effort_shown_is_sent:
  for +s: Ef.Sess
  for +dflt: Ef.Lv
  for +acts: List<&2, Ef.Act>
  {Ef.shown(Ef.run(acts, Ef.open(s, dflt))) == Ef.Level{Ef.sent(Ef.run(acts, Ef.open(s, dflt)))} : Ef.Shown}

# ---- ladder ----

# LAWS (S6.9): the thinking ladder of a model is rulebook data. Each law
# is an open claim about the model in bend/infer.bend section 6;
# PROOF.bend proves them (as Effort.<law>) with the lemmas of
# proof/effort/.

# (S6.9) The thinking ladder
# --------------------------
# docs/inference.md S6.9 and S10 (the ladder 0), the model in
# bend/infer.bend section 6. Every input is free: any explicit map, any
# rulebook ladder, any default ladders, any level.

# LAW quirk_ladder_offered_exact: a reasoning model offers a level exactly when its chosen ladder
# gives the level a wire string, or gives it no entry and the default
# ladder lists it; no other path offers a level
law quirk_ladder_offered_exact:
  for +explicit: Maybe<&2, Ef.LvMap>
  for +rule: Maybe<&2, Ef.LvMap>
  for +d: If.Defaults
  for +l: Ef.Lv
  {Ef.has(If.lad.offered(True{}, explicit, rule, d), l) == If.lad.keep(l, Ef.entry(l, If.lad.chosen(explicit, rule)), If.Defaults.reasoning(d)) : Bool}

# LAW quirk_ladder_plain_exact: a model without reasoning offers exactly the levels of the plain
# default ladder, whatever its maps
law quirk_ladder_plain_exact:
  for +explicit: Maybe<&2, Ef.LvMap>
  for +rule: Maybe<&2, Ef.LvMap>
  for +d: If.Defaults
  for +l: Ef.Lv
  {Ef.has(If.lad.offered(False{}, explicit, rule, d), l) == Ef.has(If.Defaults.plain(d), l) : Bool}

# LAW quirk_ladder_model_offers: the levels a model offers are the S10 ladder of one model, so the
# S10 laws of the clamp and the cycle hold for every ladder of the
# rulebook, with any default ladders
law quirk_ladder_model_offers:
  for r: Bool
  for +explicit: Maybe<&2, Ef.LvMap>
  for +rule: Maybe<&2, Ef.LvMap>
  for +d: If.Defaults
  {Ef.offered(If.lad.model(r, explicit, rule, d)) == If.lad.offered(r, explicit, rule, d) : List<&2, Ef.Lv>}

# (effort) The thinking ladder: bend/ffi_effort.bend
# --------------------------------------------------

# a list of levels whose length fits (every level's tag does)
def core_lvs_fit(ls: List<&2, Ef.Lv>) -> Bool:
  LawsBase.wire_fits(List.length(&2, Ef.Lv, ls))

def core_facts_fit(f: FEf.Facts) -> Bool:
  match f:
    case FEf.Facts{flag, by_map, explicit, rule, reasoning, plain}:
      Bool.and(core_lvs_fit(reasoning), core_lvs_fit(plain))

def core_effort_fits(q: FEf.Req) -> Bool:
  match q:
    case FEf.Offered{f}:
      core_facts_fit(f)
    case FEf.Clamp{f, l}:
      core_facts_fit(f)
    case FEf.Cycle{f, l, d}:
      core_facts_fit(f)

# the S10 model whose ladder the facts give (bend/infer.bend section 6)
def core_effort_model(f: FEf.Facts) -> Ef.Mdl:
  match f:
    case FEf.Facts{flag, by_map, +explicit, rule, reasoning, plain}:
      If.lad.model(If.lad.reasons(flag, by_map, explicit), explicit, rule, If.Defaults{reasoning, plain})

# LAW core_effort_round_trip (R1): a ladder request that fits reads back, and the rest is untouched
# EXCLUDES: a flag, a map entry, a default level, the level or the
#   direction lost, swapped or misread; a request that eats the rest
law core_effort_round_trip:
  for +q: FEf.Req
  for rest: String
  for h: {core_effort_fits(q) == True{} : Bool}
  {FEf.get_req(FEf.put_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FEf.Req>}

# LAW core_effort_offered (R2): the offer request answers the levels the model offers
# EXCLUDES: a codec that drops or swaps a fact, a default ladder
law core_effort_offered:
  for +f: FEf.Facts
  for h: {core_effort_fits(FEf.Offered{f}) == True{} : Bool}
  {FEf.ffi(FEf.put_req(FEf.Offered{f}, "")) == Wr.put_list(~Ef.Lv, ~FEf.put_lv, Ef.offered(core_effort_model(f)), "") : String}

# LAW core_effort_clamp (R2): the clamp request answers the model's clamp of the level
# EXCLUDES: a clamp of another level or of another model, the level as sent
law core_effort_clamp:
  for +f: FEf.Facts
  for +l: Ef.Lv
  for h: {core_effort_fits(FEf.Clamp{f, l}) == True{} : Bool}
  {FEf.ffi(FEf.put_req(FEf.Clamp{f, l}, "")) == FEf.put_lv(Ef.clamp(core_effort_model(f), l), "") : String}

# LAW core_effort_cycle (R2): the cycle request answers the model's cycle step
# EXCLUDES: a reversed direction, a step of another level or model
law core_effort_cycle:
  for +f: FEf.Facts
  for +l: Ef.Lv
  for +d: Ef.Dir
  for h: {core_effort_fits(FEf.Cycle{f, l, d}) == True{} : Bool}
  {FEf.ffi(FEf.put_req(FEf.Cycle{f, l, d}, "")) == FEf.put_mlv(Ef.cycle(core_effort_model(f), l, d), "") : String}

# LAW core_effort_malformed (R3): a malformed ladder request answers the error form
# EXCLUDES: a default ladder or level for a request it cannot read
law core_effort_malformed:
  for +s: String
  for h: {FEf.get_req(s) == Wr.Bad{} : Wr.Dec<FEf.Req>}
  {FEf.ffi(s) == Wr.err("ladder request: malformed") : String}

# LAW core_effort_left_over (R3): a ladder request with input left over answers the error form
# EXCLUDES: an entry that answers a request followed by garbage
law core_effort_left_over:
  for +q: FEf.Req
  for c: Char
  for rest: String
  for h: {core_effort_fits(q) == True{} : Bool}
  {FEf.ffi(FEf.put_req(q, SCon{c, rest})) == Wr.err("ladder request: input left over") : String}

# LAW core_effort_req_example (R1): anchor and witness: a cycle request is its tag, the facts (flag,
# by_map, explicit map, rule map, reasoning and plain defaults), the
# level and the direction, as `models/ladder.rs` writes them
# EXCLUDES: a vacuous core_effort_round_trip, fields or tags in another
#   order than Rust's
law core_effort_req_example:
  {core_effort_fits(FEf.Cycle{FEf.Facts{True{}, False{}, None{}, Some{Ef.LvMap{Ef.Missing{}, Ef.Null{}, Ef.Wire{}, Ef.Wire{}, Ef.Wire{}, Ef.Null{}, Ef.Missing{}}}, [Ef.Low{}, Ef.High{}], Nil{}}, Ef.Medium{}, Ef.Backward{}}) == True{} : Bool} & {FEf.put_req(FEf.Cycle{FEf.Facts{True{}, False{}, None{}, Some{Ef.LvMap{Ef.Missing{}, Ef.Null{}, Ef.Wire{}, Ef.Wire{}, Ef.Wire{}, Ef.Null{}, Ef.Missing{}}}, [Ef.Low{}, Ef.High{}], Nil{}}, Ef.Medium{}, Ef.Backward{}}, "") == "2,TF0,1,0,1,2,2,2,1,0,2,2,4,0,3,1," : String}

# LAW core_effort_reply_example (R2): anchor: a level is its tag off 0 .. max 6; a cycle's answer is 0
# (none) or 1 then the level
# EXCLUDES: level tags the Rust reader reads as other levels
law core_effort_reply_example:
  {FEf.put_lv(Ef.Off{}, FEf.put_lv(Ef.Minimal{}, FEf.put_lv(Ef.Low{}, FEf.put_lv(Ef.Medium{}, FEf.put_lv(Ef.High{}, FEf.put_lv(Ef.Xhigh{}, FEf.put_lv(Ef.Max{}, ""))))))) == "0,1,2,3,4,5,6," : String} & {FEf.put_mlv(None{}, FEf.put_mlv(Some{Ef.High{}}, "")) == "0,1,4," : String}

# LAW core_effort_malformed_example (R3): witness: a malformed ladder request exists (an unknown tag)
# EXCLUDES: a vacuous core_effort_malformed
law core_effort_malformed_example:
  {FEf.get_req("3,") == Wr.Bad{} : Wr.Dec<FEf.Req>} & {FEf.ffi("3,") == Wr.err("ladder request: malformed") : String}
