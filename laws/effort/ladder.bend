# eukhe: the laws of area effort, section ladder: the thinking ladder (S6.9) and the entry
# bend/ffi_effort.bend, by its wire and by the grammar's spelling

import Base
import ../../bend/effort.bend as Ef
import ../../bend/ffi_effort.bend as FEf
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase

# ---- ladder ----

# LAWS (S6.9): the thinking ladder of a model is rulebook data. Each law
# is an open claim about the model in bend/infer.bend section 6;
# PROOF.bend proves them (as Effort.<law>) with the lemmas of
# proof/effort/.

# (S6.9) The thinking ladder
# --------------------------
# the model in
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

# (effort) The entry's bytes, spelled by the grammar
# --------------------------------------------------
# The request and the reply as the wire grammar (bend/wire.bend) and
# `models/ladder.rs` spell them, written here from the wire primitives
# only (never the entry's put_* or get_*), so a tag, a field order or a
# reply form that drifts on both sides of the entry alike is caught.

# a level: its tag, off 0, minimal 1, low 2, medium 3, high 4, xhigh 5, max 6
def core_effort_spell_lv(l: Ef.Lv, rest: String) -> String:
  match l:
    case Ef.Off{}:
      Wr.put_nat(0n, rest)
    case Ef.Minimal{}:
      Wr.put_nat(1n, rest)
    case Ef.Low{}:
      Wr.put_nat(2n, rest)
    case Ef.Medium{}:
      Wr.put_nat(3n, rest)
    case Ef.High{}:
      Wr.put_nat(4n, rest)
    case Ef.Xhigh{}:
      Wr.put_nat(5n, rest)
    case Ef.Max{}:
      Wr.put_nat(6n, rest)

# an entry of a map: missing 0, null 1, a wire string 2
def core_effort_spell_ent(e: Ef.Ent, rest: String) -> String:
  match e:
    case Ef.Missing{}:
      Wr.put_nat(0n, rest)
    case Ef.Null{}:
      Wr.put_nat(1n, rest)
    case Ef.Wire{}:
      Wr.put_nat(2n, rest)

# a map: the entries of off, minimal, low, medium, high, xhigh, max
def core_effort_spell_map(m: Ef.LvMap, rest: String) -> String:
  match m:
    case Ef.LvMap{o, mi, lo, me, hi, xh, mx}:
      core_effort_spell_ent(o, core_effort_spell_ent(mi, core_effort_spell_ent(lo, core_effort_spell_ent(me, core_effort_spell_ent(hi, core_effort_spell_ent(xh, core_effort_spell_ent(mx, rest)))))))

# a map or none: 0 none, 1 then the map
def core_effort_spell_mmap(m: Maybe<&2, Ef.LvMap>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, core_effort_spell_map(x, rest))

# a cycle direction: forward 0, backward 1
def core_effort_spell_dir(d: Ef.Dir, rest: String) -> String:
  match d:
    case Ef.Forward{}:
      Wr.put_nat(0n, rest)
    case Ef.Backward{}:
      Wr.put_nat(1n, rest)

# the levels of ls, each spelled, then rest
def core_effort_spell_lvs.items(ls: List<&2, Ef.Lv>, rest: String) -> String:
  match ls:
    case Nil{}:
      rest
    case l <> t:
      core_effort_spell_lv(l, core_effort_spell_lvs.items(t, rest))

# a list of levels: its count, then each level
def core_effort_spell_lvs(+ls: List<&2, Ef.Lv>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Ef.Lv, ls), core_effort_spell_lvs.items(ls, rest))

# the facts: the flag and by_map (T or F each), the explicit map, the
# rulebook's map, the reasoning default ladder, the plain default ladder
def core_effort_spell_facts(f: FEf.Facts, rest: String) -> String:
  match f:
    case FEf.Facts{flag, by_map, explicit, rule, reasoning, plain}:
      Wr.put_bool(flag, Wr.put_bool(by_map, core_effort_spell_mmap(explicit, core_effort_spell_mmap(rule, core_effort_spell_lvs(reasoning, core_effort_spell_lvs(plain, rest))))))

# a request: its tag (offer 0, clamp 1, cycle 2), the facts, then the
# level (clamp, cycle), then the direction (cycle)
def core_effort_spell_req(q: FEf.Req, rest: String) -> String:
  match q:
    case FEf.Offered{f}:
      Wr.put_nat(0n, core_effort_spell_facts(f, rest))
    case FEf.Clamp{f, l}:
      Wr.put_nat(1n, core_effort_spell_facts(f, core_effort_spell_lv(l, rest)))
    case FEf.Cycle{f, l, d}:
      Wr.put_nat(2n, core_effort_spell_facts(f, core_effort_spell_lv(l, core_effort_spell_dir(d, rest))))

# a level or none: 0 none, 1 then the level
def core_effort_spell_mlv(m: Maybe<&2, Ef.Lv>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{l}:
      Wr.put_nat(1n, core_effort_spell_lv(l, rest))

# the spelled reply of the model's decision on q: the offered levels, the
# clamp of the level, or the cycle step (S10, bend/effort.bend; the model
# of the facts by core_effort_model)
def core_effort_spell_answer(q: FEf.Req) -> String:
  match q:
    case FEf.Offered{f}:
      core_effort_spell_lvs(Ef.offered(core_effort_model(f)), "")
    case FEf.Clamp{f, l}:
      core_effort_spell_lv(Ef.clamp(core_effort_model(f), l), "")
    case FEf.Cycle{f, l, d}:
      core_effort_spell_mlv(Ef.cycle(core_effort_model(f), l, d), "")

# LAW core_effort_answers_spelled: a ladder request spelled by the grammar, every count within
# the wire, is answered with the grammar's spelling of the model's
# decision: the offered levels (a count, then each level's tag), the clamp
# of the level (its tag), or the cycle step (0 none, or 1 then the tag)
# EXCLUDES: a level, entry, direction or request tag that drifts from the
#   grammar Rust writes and reads (swapped on both sides of the entry
#   alike), a reversed Bool, a fact, map entry or default ladder lost,
#   swapped or defaulted, another reply form
law core_effort_answers_spelled:
  for +q: FEf.Req
  for fits: {core_effort_fits(q) == True{} : Bool}
  {FEf.ffi(core_effort_spell_req(q, "")) == core_effort_spell_answer(q) : String}

# LAW core_effort_left_over_spelled: a spelled ladder request that fits, followed by any more
# input, answers the error form "ladder request: input left over"
# EXCLUDES: trailing input ignored, or read as part of the request
law core_effort_left_over_spelled:
  for +q: FEf.Req
  for fits: {core_effort_fits(q) == True{} : Bool}
  for +c: Char
  for +t: String
  {FEf.ffi(core_effort_spell_req(q, SCon{c, t})) == Wr.err("ladder request: input left over") : String}

# LAW core_effort_unknown_request: a request tag of 3 or more (of any length) answers the error
# form "ladder request: malformed", whatever follows
# EXCLUDES: an unknown request tag read as offer, clamp or cycle
law core_effort_unknown_request:
  for +n: Nat
  for +rest: String
  {FEf.ffi(Wr.put_nat(3n+n, rest)) == Wr.err("ladder request: malformed") : String}

# LAW core_effort_reads_only_requests: an answer that is not the error form answers a ladder
# request: the input is exactly the spelling of a request whose counts fit
# the wire, and the answer is the spelled reply of the model's decision on
# it
# EXCLUDES: a decoder that accepts an unknown tag (request, level, entry,
#   map or direction), a Bool other than T or F, a missing or extra field
#   or input left over, and answers it anyway (a default instead of the
#   error form)
law core_effort_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FEf.ffi(s)) == False{} : Bool}
  exs q: FEf.Req
  {(s, (core_effort_fits(q), FEf.ffi(s))) == (core_effort_spell_req(q, ""), (True{}, core_effort_spell_answer(q))) : String & (Bool & String)}

# LAW core_effort_malformed_unless_request: every answer but the error form "ladder request:
# malformed" comes from an input that begins with a spelled ladder request
# that fits
# EXCLUDES: the left-over error (or any answer) for input that does not
#   begin with a request, the malformed error spelled with another text
law core_effort_malformed_unless_request:
  for +s: String
  for other: {String.eq(FEf.ffi(s), Wr.err("ladder request: malformed")) == False{} : Bool}
  exs q: FEf.Req
  exs rest: String
  {(s, core_effort_fits(q)) == (core_effort_spell_req(q, rest), True{}) : String & Bool}

# LAW core_effort_tags_example: anchor: the bytes `models/ladder.rs` sends and reads: a
# reasoning model (T, F) with no explicit map and the rule map (missing,
# null, wire, wire, wire, null, missing), reasoning default [low, high],
# plain default [] offers low, medium, high (3,2,3,4,); the clamp of off is
# low (2,); forward from high wraps to low (1,2,); backward from medium is
# low (1,2,); a plain model (F, F) with no maps and no defaults offers
# nothing (0,) and does not cycle (0,); request tag 3, level tag 7,
# direction tag 2, entry tag 3, map tag 2 and Bool X are malformed; a
# request with input left over is refused
# EXCLUDES: a tag table both sides of the Bend entry agree on but Rust
#   does not, an unknown tag read as a known one
law core_effort_tags_example:
  {[FEf.ffi("0,TF0,1,0,1,2,2,2,1,0,2,2,4,0,"), FEf.ffi("1,TF0,1,0,1,2,2,2,1,0,2,2,4,0,0,"), FEf.ffi("2,TF0,1,0,1,2,2,2,1,0,2,2,4,0,4,0,"), FEf.ffi("2,TF0,1,0,1,2,2,2,1,0,2,2,4,0,3,1,"), FEf.ffi("0,FF0,0,0,0,"), FEf.ffi("2,FF0,0,0,0,4,0,")] == ["3,2,3,4,", "2,", "1,2,", "1,2,", "0,", "0,"] : List<&2, String>} & {[FEf.ffi("3,FF0,0,0,0,"), FEf.ffi("1,FF0,0,0,0,7,"), FEf.ffi("2,FF0,0,0,0,4,2,"), FEf.ffi("0,FF1,3,0,0,0,0,0,0,0,0,0,"), FEf.ffi("0,FF2,0,0,0,"), FEf.ffi("0,XF0,0,0,0,"), FEf.ffi("0,FF0,0,0,0,x")] == [Wr.err("ladder request: malformed"), Wr.err("ladder request: malformed"), Wr.err("ladder request: malformed"), Wr.err("ladder request: malformed"), Wr.err("ladder request: malformed"), Wr.err("ladder request: malformed"), Wr.err("ladder request: input left over")] : List<&2, String>}
