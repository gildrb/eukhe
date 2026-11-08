# eukhe: the laws of area facts

import Base
import ../bend/facts.bend as Fx
import ../bend/ffi_facts.bend as FFx
import ../bend/infer.bend as If
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (facts) The thinking budgets: bend/ffi_facts.bend
# -------------------------------------------------

def core_customs_fit(c: Fx.Customs) -> Bool:
  match c:
    case Fx.Customs{mi, lo, me, hi}:
      Bool.and(LawsBase.core_mfits(mi), Bool.and(LawsBase.core_mfits(lo), Bool.and(LawsBase.core_mfits(me), LawsBase.core_mfits(hi))))

def core_budgets_fit(b: Fx.Budgets) -> Bool:
  match b:
    case Fx.Budgets{mi, lo, me, hi}:
      Bool.and(LawsBase.wire_fits(mi), Bool.and(LawsBase.wire_fits(lo), Bool.and(LawsBase.wire_fits(me), LawsBase.wire_fits(hi))))

def core_mbudgets_fit(m: Maybe<&2, Fx.Budgets>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{b}:
      core_budgets_fit(b)

def core_facts_req_fits(q: FFx.Req) -> Bool:
  match q:
    case FFx.Level{l, c, d}:
      Bool.and(core_customs_fit(c), core_budgets_fit(d))
    case FFx.Room{b, m, a}:
      Bool.and(LawsBase.wire_fits(b), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(a)))
    case FFx.Adjust{base, mm, l, c, d, a}:
      Bool.and(LawsBase.core_mfits(base), Bool.and(LawsBase.wire_fits(mm), Bool.and(core_customs_fit(c), Bool.and(core_budgets_fit(d), LawsBase.wire_fits(a)))))
    case FFx.Google{rule, c, l}:
      Bool.and(core_mbudgets_fit(rule), core_customs_fit(c))
    case FFx.Aux{c, d, a, top}:
      Bool.and(core_customs_fit(c), Bool.and(core_budgets_fit(d), Bool.and(LawsBase.wire_fits(a), LawsBase.wire_fits(top))))

# LAW core_facts_round_trip (R1): a budget request that fits reads back, and the rest is untouched
# EXCLUDES: a level, a user's budget, a default budget, a cap or the
#   answer's room lost, swapped or misread; a user's budget read as none
law core_facts_round_trip:
  for +q: FFx.Req
  for rest: String
  for h: {core_facts_req_fits(q) == True{} : Bool}
  {FFx.get_req(FFx.put_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FFx.Req>}

# LAW core_facts_level (R2): the level request answers the level's budget
# EXCLUDES: the default budget over the user's, another level's budget
law core_facts_level:
  for +l: Fx.ELv
  for +c: Fx.Customs
  for +d: Fx.Budgets
  for h: {core_facts_req_fits(FFx.Level{l, c, d}) == True{} : Bool}
  {FFx.ffi(FFx.put_req(FFx.Level{l, c, d}, "")) == Wr.put_nat(Fx.budget(c, d, Fx.Lv.of(l)), "") : String}

# LAW core_facts_room (R2): the room request answers the budget under the answer's room
# EXCLUDES: the budget, the ceiling and the answer's tokens swapped
law core_facts_room:
  for +b: Nat
  for +m: Nat
  for +a: Nat
  for h: {core_facts_req_fits(FFx.Room{b, m, a}) == True{} : Bool}
  {FFx.ffi(FFx.put_req(FFx.Room{b, m, a}, "")) == Wr.put_nat(Fx.room(b, m, a), "") : String}

# LAW core_facts_adjust (R2): the adjust request answers the fitted ceiling and budget
# EXCLUDES: the caller's cap read as none, the model's cap and the answer's
#   tokens swapped, the ceiling and the budget swapped in the reply
law core_facts_adjust:
  for +base: Maybe<&2, Nat>
  for +mm: Nat
  for +l: Fx.ELv
  for +c: Fx.Customs
  for +d: Fx.Budgets
  for +a: Nat
  for h: {core_facts_req_fits(FFx.Adjust{base, mm, l, c, d, a}) == True{} : Bool}
  {FFx.ffi(FFx.put_req(FFx.Adjust{base, mm, l, c, d, a}, "")) == FFx.put_fit(Fx.adjust(base, mm, l, c, d, a), "") : String}

# LAW core_facts_google (R2): the Google request answers the Google budget, the refusal of an
# unordered rule included
# EXCLUDES: a rule read as none, a dynamic budget for an unordered rule
law core_facts_google:
  for +rule: Maybe<&2, Fx.Budgets>
  for +c: Fx.Customs
  for +l: Fx.Lv
  for h: {core_facts_req_fits(FFx.Google{rule, c, l}) == True{} : Bool}
  {FFx.ffi(FFx.put_req(FFx.Google{rule, c, l}, "")) == FFx.put_gb(Fx.gbudget(rule, c, l), "") : String}

# LAW core_facts_aux (R2): the aux request answers the auxiliary call's output cap
# EXCLUDES: the answer's tokens and the top swapped, a cap past the top
law core_facts_aux:
  for +c: Fx.Customs
  for +d: Fx.Budgets
  for +a: Nat
  for +top: Nat
  for h: {core_facts_req_fits(FFx.Aux{c, d, a, top}) == True{} : Bool}
  {FFx.ffi(FFx.put_req(FFx.Aux{c, d, a, top}, "")) == Wr.put_nat(Fx.aux(c, d, a, top), "") : String}

# LAW core_facts_malformed (R3): a malformed budget request answers the error form
# EXCLUDES: a default budget for a request it cannot read
law core_facts_malformed:
  for +s: String
  for h: {FFx.get_req(s) == Wr.Bad{} : Wr.Dec<FFx.Req>}
  {FFx.ffi(s) == Wr.err("budget request: malformed") : String}

# LAW core_facts_left_over (R3): a budget request with input left over answers the error form
# EXCLUDES: an entry that answers a request followed by garbage
law core_facts_left_over:
  for +q: FFx.Req
  for c: Char
  for rest: String
  for h: {core_facts_req_fits(q) == True{} : Bool}
  {FFx.ffi(FFx.put_req(q, SCon{c, rest})) == Wr.err("budget request: input left over") : String}

# LAW core_facts_req_example (R1): anchor and witness: an adjust request is its tag, the caller's
# cap, the model's cap, the level, the user's budgets, the defaults and
# the answer's tokens, as `api/simple_options.rs` writes them
# EXCLUDES: a vacuous core_facts_round_trip, fields or tags in another
#   order than Rust's
law core_facts_req_example:
  {core_facts_req_fits(FFx.Adjust{Some{100n}, 64n, Fx.EXhigh{}, Fx.Customs{None{}, Some{5n}, None{}, None{}}, Fx.Budgets{1n, 2n, 3n, 4n}, 8n}) == True{} : Bool} & {FFx.put_req(FFx.Adjust{Some{100n}, 64n, Fx.EXhigh{}, Fx.Customs{None{}, Some{5n}, None{}, None{}}, Fx.Budgets{1n, 2n, 3n, 4n}, 8n}, "") == "2,1,100,64,4,0,1,5,0,0,1,2,3,4,8," : String}

# LAW core_facts_reply_example (R2): anchor: a Google budget is 0 dynamic, 1 then the tokens, 2
# unordered; a fit is the ceiling, then the budget
# EXCLUDES: replies the Rust reader reads as other values
law core_facts_reply_example:
  {FFx.put_gb(Fx.Dynamic{}, FFx.put_gb(Fx.Tokens{5n}, FFx.put_gb(Fx.Unordered{}, ""))) == "0,1,5,2," : String} & {FFx.put_fit(Fx.Fit{9n, 4n}, "") == "9,4," : String}

# LAW core_facts_malformed_example (R3): witness: a malformed budget request exists (an unknown tag)
# EXCLUDES: a vacuous core_facts_malformed
law core_facts_malformed_example:
  {FFx.get_req("5,") == Wr.Bad{} : Wr.Dec<FFx.Req>} & {FFx.ffi("5,") == Wr.err("budget request: malformed") : String}

# The entry by the grammar's spelling
# -----------------------------------
# The bytes Rust's `Writer` sends and its `Reader` reads
# (`api/simple_options.rs` `budgets_call`, `api/google_shared/options.rs`),
# spelled here from the wire's primitives only, never the entry's put_*.

# a Maybe<Nat>: 0 none, 1 then the Nat
def facts_spell_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))

# a request's level: minimal 0, low 1, medium 2, high 3, xhigh 4, max 5
def facts_spell_elv(l: Fx.ELv, rest: String) -> String:
  match l:
    case Fx.EMinimal{}:
      Wr.put_nat(0n, rest)
    case Fx.ELow{}:
      Wr.put_nat(1n, rest)
    case Fx.EMedium{}:
      Wr.put_nat(2n, rest)
    case Fx.EHigh{}:
      Wr.put_nat(3n, rest)
    case Fx.EXhigh{}:
      Wr.put_nat(4n, rest)
    case Fx.EMax{}:
      Wr.put_nat(5n, rest)

# a budget level: minimal 0, low 1, medium 2, high 3
def facts_spell_lv(l: Fx.Lv, rest: String) -> String:
  match l:
    case Fx.Minimal{}:
      Wr.put_nat(0n, rest)
    case Fx.Low{}:
      Wr.put_nat(1n, rest)
    case Fx.Medium{}:
      Wr.put_nat(2n, rest)
    case Fx.High{}:
      Wr.put_nat(3n, rest)

# the user's budgets: minimal, low, medium, high, each a Maybe<Nat>
def facts_spell_customs(c: Fx.Customs, rest: String) -> String:
  match c:
    case Fx.Customs{mi, lo, me, hi}:
      facts_spell_mnat(mi, facts_spell_mnat(lo, facts_spell_mnat(me, facts_spell_mnat(hi, rest))))

# a budget table: minimal, low, medium, high
def facts_spell_budgets(b: Fx.Budgets, rest: String) -> String:
  match b:
    case Fx.Budgets{mi, lo, me, hi}:
      Wr.put_nat(mi, Wr.put_nat(lo, Wr.put_nat(me, Wr.put_nat(hi, rest))))

# a budget rule: 0 none, 1 then the table
def facts_spell_mbudgets(m: Maybe<&2, Fx.Budgets>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{b}:
      Wr.put_nat(1n, facts_spell_budgets(b, rest))

# a request: its tag (level 0, room 1, adjust 2, Google 3, aux 4), then
# its fields in Rust's order, then rest
def facts_spell_req(q: FFx.Req, rest: String) -> String:
  match q:
    case FFx.Level{l, c, d}:
      Wr.put_nat(0n, facts_spell_elv(l, facts_spell_customs(c, facts_spell_budgets(d, rest))))
    case FFx.Room{b, m, a}:
      Wr.put_nat(1n, Wr.put_nat(b, Wr.put_nat(m, Wr.put_nat(a, rest))))
    case FFx.Adjust{base, mm, l, c, d, a}:
      Wr.put_nat(2n, facts_spell_mnat(base, Wr.put_nat(mm, facts_spell_elv(l, facts_spell_customs(c, facts_spell_budgets(d, Wr.put_nat(a, rest)))))))
    case FFx.Google{rule, c, l}:
      Wr.put_nat(3n, facts_spell_mbudgets(rule, facts_spell_customs(c, facts_spell_lv(l, rest))))
    case FFx.Aux{c, d, a, top}:
      Wr.put_nat(4n, facts_spell_customs(c, facts_spell_budgets(d, Wr.put_nat(a, Wr.put_nat(top, rest)))))

# a fit: the response ceiling, then the thinking budget
def facts_spell_fit(f: Fx.Fit, rest: String) -> String:
  match f:
    case Fx.Fit{m, b}:
      Wr.put_nat(m, Wr.put_nat(b, rest))

# a Google budget: 0 dynamic, 1 then the tokens, 2 unordered
def facts_spell_gb(g: Fx.GB, rest: String) -> String:
  match g:
    case Fx.Dynamic{}:
      Wr.put_nat(0n, rest)
    case Fx.Tokens{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))
    case Fx.Unordered{}:
      Wr.put_nat(2n, rest)

# the spelled reply to a request: the model's decision (pinned by the laws
# of model_facts below), as Rust's reader reads it
def facts_spell_answer(q: FFx.Req) -> String:
  match q:
    case FFx.Level{l, c, d}:
      Wr.put_nat(Fx.budget(c, d, Fx.Lv.of(l)), "")
    case FFx.Room{b, m, a}:
      Wr.put_nat(Fx.room(b, m, a), "")
    case FFx.Adjust{base, mm, l, c, d, a}:
      facts_spell_fit(Fx.adjust(base, mm, l, c, d, a), "")
    case FFx.Google{rule, c, l}:
      facts_spell_gb(Fx.gbudget(rule, c, l), "")
    case FFx.Aux{c, d, a, top}:
      Wr.put_nat(Fx.aux(c, d, a, top), "")

# LAW core_facts_answers_spelled: a budget request spelled by the grammar, every number within
# the wire, answers the grammar's spelling of the model's decision: the
# level's budget, the budget under the answer's room, the ceiling then the
# fitted budget, the Google budget (0 dynamic, 1 then the tokens, 2
# unordered), the auxiliary call's cap
# EXCLUDES: a request, level, presence or reply tag that drifts on both
#   sides of the entry alike, a field lost, swapped or defaulted, a reply
#   spelled another way (the ceiling and the budget swapped)
law core_facts_answers_spelled:
  for +q: FFx.Req
  for fits: {core_facts_req_fits(q) == True{} : Bool}
  {FFx.ffi(facts_spell_req(q, "")) == facts_spell_answer(q) : String}

# LAW core_facts_left_over_spelled: a spelled budget request that fits, followed by any more
# input, answers the error form "budget request: input left over"
# EXCLUDES: trailing input ignored, read as part of the request, or named
#   as malformed
law core_facts_left_over_spelled:
  for +q: FFx.Req
  for fits: {core_facts_req_fits(q) == True{} : Bool}
  for +c: Char
  for +t: String
  {FFx.ffi(facts_spell_req(q, SCon{c, t})) == Wr.err("budget request: input left over") : String}

# LAW core_facts_unknown_request: a request tag of 5 or more (of any length) answers the error
# form "budget request: malformed", whatever follows
# EXCLUDES: an unknown request read as a known one, or as another error
law core_facts_unknown_request:
  for +n: Nat
  for +rest: String
  {FFx.ffi(Wr.put_nat(5n+n, rest)) == Wr.err("budget request: malformed") : String}

# LAW core_facts_unknown_level: a level request whose level tag is 6 or more (of any length)
# answers the error form "budget request: malformed", whatever follows
# EXCLUDES: an unknown level read as a known one (xhigh, max or high)
law core_facts_unknown_level:
  for +n: Nat
  for +rest: String
  {FFx.ffi(Wr.put_nat(0n, Wr.put_nat(6n+n, rest))) == Wr.err("budget request: malformed") : String}

# LAW core_facts_unknown_cap: an adjust request whose caller's cap tag is 2 or more answers the
# error form "budget request: malformed", whatever follows
# EXCLUDES: an unknown presence tag read as no cap or a cap
law core_facts_unknown_cap:
  for +n: Nat
  for +rest: String
  {FFx.ffi(Wr.put_nat(2n, Wr.put_nat(2n+n, rest))) == Wr.err("budget request: malformed") : String}

# LAW core_facts_unknown_rule: a Google request whose rule tag is 2 or more answers the error
# form "budget request: malformed", whatever follows
# EXCLUDES: an unknown rule tag read as no rule or a rule
law core_facts_unknown_rule:
  for +n: Nat
  for +rest: String
  {FFx.ffi(Wr.put_nat(3n, Wr.put_nat(2n+n, rest))) == Wr.err("budget request: malformed") : String}

# LAW core_facts_unknown_budget_level: a Google request with a spelled rule and user's budgets that
# fit, then a budget level tag of 4 or more (of any length), answers the
# error form "budget request: malformed", whatever follows
# EXCLUDES: an unknown budget level read as a known one (high)
law core_facts_unknown_budget_level:
  for +rule: Maybe<&2, Fx.Budgets>
  for +c: Fx.Customs
  for fits: {Bool.and(core_mbudgets_fit(rule), core_customs_fit(c)) == True{} : Bool}
  for +n: Nat
  for +rest: String
  {FFx.ffi(Wr.put_nat(3n, facts_spell_mbudgets(rule, facts_spell_customs(c, Wr.put_nat(4n+n, rest))))) == Wr.err("budget request: malformed") : String}

# LAW core_facts_unknown_custom: an aux request whose first user's budget tag is 2 or more
# answers the error form "budget request: malformed", whatever follows
# EXCLUDES: an unknown presence tag of a user's budget read as none or a
#   budget
law core_facts_unknown_custom:
  for +n: Nat
  for +rest: String
  {FFx.ffi(Wr.put_nat(4n, Wr.put_nat(2n+n, rest))) == Wr.err("budget request: malformed") : String}

# LAW core_facts_reads_only_requests: an answer that is not the error form answers a request:
# the input is exactly the spelling of a budget request whose numbers fit
# the wire, and the answer is the spelled reply of the model's decision
# EXCLUDES: a decoder that accepts an unknown tag (request, level, presence,
#   rule, budget level), a missing or extra field, or input left over, and
#   answers it anyway (a default instead of the error form)
law core_facts_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FFx.ffi(s)) == False{} : Bool}
  exs q: FFx.Req
  {(s, (core_facts_req_fits(q), FFx.ffi(s))) == (facts_spell_req(q, ""), (True{}, facts_spell_answer(q))) : String & (Bool & String)}

# LAW core_facts_malformed_unless_request: every answer but the error form "budget request:
# malformed" comes from an input that begins with a spelled budget request
# that fits
# EXCLUDES: the left-over error (or any answer) for input that does not
#   begin with a request, the malformed error spelled with another text
law core_facts_malformed_unless_request:
  for +s: String
  for other: {String.eq(FFx.ffi(s), Wr.err("budget request: malformed")) == False{} : Bool}
  exs q: FFx.Req
  exs rest: String
  {(s, core_facts_req_fits(q)) == (facts_spell_req(q, rest), True{}) : String & Bool}

# LAW core_facts_tags_example: anchor: the bytes Rust sends and reads: an xhigh level request
# with no user's budget and defaults 1, 2, 3, 4 answers the high default
# (4,), a medium one with the user's 7 answers 7; room 9 under ceiling 8
# with 3 for the answer answers 5; an adjust with the caller's cap 3,
# model cap 9, low, answer 2 answers ceiling 5, budget 2; with no cap,
# model cap 6, high, the user's 7 answers 6 then 4; a Google request with
# no rule and no user's budget is dynamic (0,), with rule 1, 2, 3, 4 and
# the user's low 9 is 1 then 4, an unordered rule answers 2; an aux
# request answers 2 more than the high budget (6,), held at the top 5;
# request tag 5, level tag 6, rule tag 2, budget level tag 4 and no input
# are malformed; a request with input left over is refused
# EXCLUDES: a tag table both sides of the Bend entry agree on but Rust
#   does not, a reply in another order, an unknown tag read as a known
#   one, the two error texts swapped
law core_facts_tags_example:
  {[FFx.ffi("0,4,0,0,0,0,1,2,3,4,"), FFx.ffi("0,2,0,0,1,7,0,1,2,3,4,"), FFx.ffi("1,9,8,3,"), FFx.ffi("2,1,3,9,1,0,0,0,0,1,2,3,4,2,"), FFx.ffi("2,0,6,3,0,0,0,1,7,1,2,3,4,2,"), FFx.ffi("3,0,0,0,0,0,2,"), FFx.ffi("3,1,1,2,3,4,0,1,9,0,0,1,"), FFx.ffi("3,1,4,3,2,1,0,0,0,0,0,"), FFx.ffi("4,0,0,0,0,1,2,3,4,2,9,"), FFx.ffi("4,0,0,0,0,1,2,3,4,2,5,"), FFx.ffi("5,"), FFx.ffi("0,6,"), FFx.ffi("3,2,"), FFx.ffi("3,0,0,0,0,0,4,"), FFx.ffi(""), FFx.ffi("1,9,8,3,x")] == ["4,", "7,", "5,", "5,2,", "6,4,", "0,", "1,4,", "2,", "6,", "5,", Wr.err("budget request: malformed"), Wr.err("budget request: malformed"), Wr.err("budget request: malformed"), Wr.err("budget request: malformed"), Wr.err("budget request: malformed"), Wr.err("budget request: input left over")] : List<&2, String>}

# ---- model_facts ----

# LAWS (S6.10): model and provider facts are data. A wire API decides a
# fact of a model only from the quirks rulebook's answer (and the model's
# explicit compat flag or the user's setting), the thinking budgets stay
# inside the model's limits, and where a fact moved from code into data the
# data gives the answers the code gave. Each law is an open claim about the
# model in bend/facts.bend; PROOF.bend proves them (as Facts.<law>)
# with the lemmas of proof/facts/. The decisions run as the compiled core
# (entry bend/ffi_model_facts.bend, laws at the end of this file).

# (S6.10.1) Decisions are rulebook lookups
# ----------------------------------------

# LAW facts_adaptive_compat_first: a model's explicit compat flag decides adaptive thinking, over the
# rulebook
law facts_adaptive_compat_first:
  for b: Bool
  for a: If.Ans
  {Fx.adaptive(Some{b}, a) == b : Bool}

# LAW facts_adaptive_rulebook_second: with no compat flag, adaptive thinking is the rulebook's answer,
# false where no rule applies; one rule for Anthropic Messages and Bedrock
law facts_adaptive_rulebook_second:
  for a: If.Ans
  {Fx.adaptive(None{}, a) == Fx.flag(a, False{}) : Bool}

# (S6.10.2) Budgets stay within the model's limits
# ------------------------------------------------

# LAW facts_google_budget_at_most_high: a Google budget of a model with a budget rule is at most the rule's
# high budget, whatever the user's budgets
law facts_google_budget_at_most_high:
  for +b: Fx.Budgets
  for c: Fx.Customs
  for +l: Fx.Lv
  for +ordered: {Fx.Budgets.ordered(b) == True{} : Bool}
  {Nat.is_le(Fx.gtokens(b, c, l), Fx.Budgets.high(b)) == True{} : Bool}

# LAW facts_google_budget_at_least_minimal: and at least the rule's minimal budget
law facts_google_budget_at_least_minimal:
  for +b: Fx.Budgets
  for c: Fx.Customs
  for +l: Fx.Lv
  for +ordered: {Fx.Budgets.ordered(b) == True{} : Bool}
  {Nat.is_le(Fx.Budgets.minimal(b), Fx.gtokens(b, c, l)) == True{} : Bool}

# LAW facts_google_rule_is_the_table: with no user budget, a Google budget is the rule's budget of the
# level, unchanged: the rule is the table
law facts_google_rule_is_the_table:
  for +b: Fx.Budgets
  for +l: Fx.Lv
  for +ordered: {Fx.Budgets.ordered(b) == True{} : Bool}
  {Fx.gtokens(b, Fx.Customs.none(), l) == Fx.Budgets.at(b, l) : Nat}

# LAW facts_fit_budget_under_ceiling: a fitted thinking budget is never above the response ceiling
law facts_fit_budget_under_ceiling:
  for +base: Maybe<&2, Nat>
  for +mm: Nat
  for +b: Nat
  for +a: Nat
  {Nat.is_le(Fx.Fit.budget(Fx.fit(base, mm, b, a)), Fx.Fit.max(Fx.fit(base, mm, b, a))) == True{} : Bool}

# LAW facts_fit_ceiling_under_model: and the response ceiling is never above the model's output cap
law facts_fit_ceiling_under_model:
  for +base: Maybe<&2, Nat>
  for +mm: Nat
  for +b: Nat
  for +a: Nat
  {Nat.is_le(Fx.Fit.max(Fx.fit(base, mm, b, a)), mm) == True{} : Bool}

# LAW facts_room_leaves_the_answer: a budget capped for answer room leaves the answer its tokens under
# the ceiling
law facts_room_leaves_the_answer:
  for +b: Nat
  for +m: Nat
  for +a: Nat
  for fits: {Nat.is_le(a, m) == True{} : Bool}
  {Nat.is_le(Nat.add(Fx.room(b, m, a), a), m) == True{} : Bool}

# LAW facts_aux_cap_answer_room: an auxiliary call's cap leaves its answer room over the thinking
# budget in use, whatever the user's budget
law facts_aux_cap_answer_room:
  for +b: Nat
  for +a: Nat
  {Nat.sub(Fx.aux_cap(b, a), b) == a : Nat}

# LAW facts_google_unordered_refused: an unordered budget rule (a minimal, low, medium, high that falls
# somewhere) gives no Google budget: the rule is refused, never clamped
# into a range it does not have (Rust `u64::clamp` panicked on minimal >
# high); EXCLUDES: a budget from a rule with no range, a panic
law facts_google_unordered_refused:
  for +b: Fx.Budgets
  for c: Fx.Customs
  for l: Fx.Lv
  for bad: {Fx.Budgets.ordered(b) == False{} : Bool}
  {Fx.gbudget(Some{b}, c, l) == Fx.Unordered{} : Fx.GB}

# LAW facts_google_ordered_tokens: an ordered budget rule gives the budget gtokens (so every law on
# gtokens holds for the Google budget)
law facts_google_ordered_tokens:
  for +b: Fx.Budgets
  for c: Fx.Customs
  for +l: Fx.Lv
  for ok: {Fx.Budgets.ordered(b) == True{} : Bool}
  {Fx.gbudget(Some{b}, c, l) == Fx.Tokens{Fx.gtokens(b, c, l)} : Fx.GB}

# x held inside lo..hi: never below lo, never above hi
def budgets.held(x: Nat, +lo: Nat, +hi: Nat) -> Nat:
  Nat.max(lo, Nat.min(x, hi))

# LAW facts_google_budget_held: a Google budget under a rule is the user's budget of the level,
# else the rule's, held inside the rule's minimal..high: a user's budget
# inside the range is sent as it is; EXCLUDES: a user's budget ignored, a
# budget moved inside the range
law facts_google_budget_held:
  for +b: Fx.Budgets
  for c: Fx.Customs
  for +l: Fx.Lv
  for +ordered: {Fx.Budgets.ordered(b) == True{} : Bool}
  {Fx.gtokens(b, c, l) == budgets.held(Maybe.default(&2, Nat, Fx.Customs.at(c, l), Fx.Budgets.at(b, l)), Fx.Budgets.minimal(b), Fx.Budgets.high(b)) : Nat}

# LAW facts_google_free_user: without a rule, a Google budget is the user's budget of the level
law facts_google_free_user:
  for c: Fx.Customs
  for l: Fx.Lv
  for n: Nat
  for u: {Fx.Customs.at(c, l) == Some{n} : Maybe<&2, Nat>}
  {Fx.gbudget(None{}, c, l) == Fx.Tokens{n} : Fx.GB}

# LAW facts_google_free_dynamic: without a rule and a user's budget, the Google budget is dynamic
law facts_google_free_dynamic:
  for c: Fx.Customs
  for l: Fx.Lv
  for u: {Fx.Customs.at(c, l) == None{} : Maybe<&2, Nat>}
  {Fx.gbudget(None{}, c, l) == Fx.Dynamic{} : Fx.GB}

# LAW facts_budget_levels: the budget level of a request's level: each level keeps its own,
# xhigh and max take high
law facts_budget_levels:
  {[Fx.Lv.of(Fx.EMinimal{}), Fx.Lv.of(Fx.ELow{}), Fx.Lv.of(Fx.EMedium{}), Fx.Lv.of(Fx.EHigh{}), Fx.Lv.of(Fx.EXhigh{}), Fx.Lv.of(Fx.EMax{})] == [Fx.Minimal{}, Fx.Low{}, Fx.Medium{}, Fx.High{}, Fx.High{}, Fx.High{}] : List<&2, Fx.Lv>}

# LAW facts_budget_user_first: the budget of a level is the user's budget of the level, over the
# defaults
law facts_budget_user_first:
  for c: Fx.Customs
  for d: Fx.Budgets
  for +l: Fx.Lv
  for n: Nat
  for u: {Fx.Customs.at(c, l) == Some{n} : Maybe<&2, Nat>}
  {Fx.budget(c, d, l) == n : Nat}

# LAW facts_budget_default: without the user's budget, the budget of a level is the default
law facts_budget_default:
  for c: Fx.Customs
  for d: Fx.Budgets
  for +l: Fx.Lv
  for u: {Fx.Customs.at(c, l) == None{} : Maybe<&2, Nat>}
  {Fx.budget(c, d, l) == Fx.Budgets.at(d, l) : Nat}

# the fit of the response ceiling m: the budget b, capped so that a
# tokens stay for the answer when it fills the ceiling
def budgets.fit.at(over: Bool, +m: Nat, +b: Nat, +a: Nat) -> Fx.Fit:
  match over:
    case True{}:
      Fx.Fit{m, Nat.min(b, Nat.sub(m, a))}
    case False{}:
      Fx.Fit{m, b}

def budgets.fit(+m: Nat, +b: Nat, +a: Nat) -> Fx.Fit:
  budgets.fit.at(Nat.is_le(m, b), m, b, a)

# LAW facts_fit_exact_caller: with the caller's cap x, the ceiling is x plus the budget, at most
# the model's cap, and the budget is capped for answer room when it fills
# the ceiling; EXCLUDES: any other ceiling or budget (the two laws above
# only bound them)
law facts_fit_exact_caller:
  for +x: Nat
  for +mm: Nat
  for +b: Nat
  for +a: Nat
  {Fx.fit(Some{x}, mm, b, a) == budgets.fit(Nat.min(Nat.add(x, b), mm), b, a) : Fx.Fit}

# LAW facts_fit_exact_model: without the caller's cap, the ceiling is the model's cap
law facts_fit_exact_model:
  for +mm: Nat
  for +b: Nat
  for +a: Nat
  {Fx.fit(None{}, mm, b, a) == budgets.fit(mm, b, a) : Fx.Fit}

# LAW facts_fit_saturated_caller (the Nat range): : a caller's cap at or above the model's cap fits as
# no cap, so the cap Rust saturates at the wire's largest Nat (10^14-1)
# fits as it did unsaturated whenever the model's cap is below it
law facts_fit_saturated_caller:
  for +x: Nat
  for +mm: Nat
  for +b: Nat
  for +a: Nat
  for +above: {Nat.is_le(mm, x) == True{} : Bool}
  {Fx.fit(Some{x}, mm, b, a) == Fx.fit(None{}, mm, b, a) : Fx.Fit}

# LAW facts_fit_saturated_budget (the Nat range): : two budgets at or above the model's cap fit alike,
# so a budget Rust saturates at the wire's largest Nat fits as it did
# unsaturated whenever the model's cap is below it
law facts_fit_saturated_budget:
  for +base: Maybe<&2, Nat>
  for +mm: Nat
  for +b1: Nat
  for +b2: Nat
  for +a: Nat
  for +h1: {Nat.is_le(mm, b1) == True{} : Bool}
  for +h2: {Nat.is_le(mm, b2) == True{} : Bool}
  {Fx.fit(base, mm, b1, a) == Fx.fit(base, mm, b2, a) : Fx.Fit}

# LAW facts_aux_cap_within (the Nat range): : the compactor's cap is the thinking budget plus the
# answer, at most top (Rust passes the wire's largest Nat): below top
# the answer keeps its room exactly (facts_aux_cap_answer_room), at top
# the cap saturates as Rust's `saturating_add` does
law facts_aux_cap_within:
  for +b: Nat
  for +a: Nat
  for +top: Nat
  {Fx.aux_cap.within(b, a, top) == Nat.min(Fx.aux_cap(b, a), top) : Nat}

# (S6.10.3) Oracles: the data gives the answers the code gave
# -----------------------------------------------------------

# LAW facts_bedrock_effort_oracle: the Bedrock effort from the thinking-level map is the effort of the
# old id list, for every model whose map keeps the catalog's promise (a
# native-xhigh model's map sends xhigh at xhigh)
law facts_bedrock_effort_oracle:
  for native: Bool
  for +m: Fx.EMap
  for +l: Fx.ELv
  for ok: {Fx.native_ok(native, m) == True{} : Bool}
  {Fx.effort.old(native, m, l) == Fx.effort(m, l) : Nat}

# LAW facts_bedrock_budget_oracle: the budget of budget-based Claude from the rulebook's default
# budgets is the budget of the old Bedrock table, for every user budget
law facts_bedrock_budget_oracle:
  for c: Fx.Customs
  for +l: Fx.Lv
  {Fx.budget(c, Fx.budgets.shipped(), l) == Fx.budget.old(c, l) : Nat}

# (S6.10.4) Prices are data
# -------------------------

# LAW facts_tier_price_model_row_first: a price row of the model wins over the row of every model: the
# gpt-5.5 priority price is a row, not an id test in code
law facts_tier_price_model_row_first:
  for +rows: List<&2, Fx.PRow>
  for +m: Nat
  for +t: Nat
  for +k: Nat
  for hit: {Fx.price.find(rows, m, t, True{}) == Some{k} : Maybe<&2, Nat>}
  {Fx.price(rows, m, t) == Some{k} : Maybe<&2, Nat>}

# LAW facts_tier_price_no_row_base: a tier that no row prices leaves the base price (a provider that does
# not sell the tier is not billed OpenAI's multiplier)
law facts_tier_price_no_row_base:
  for +rows: List<&2, Fx.PRow>
  for +m: Nat
  for +t: Nat
  for +base: Nat
  for none: {Fx.price(rows, m, t) == None{} : Maybe<&2, Nat>}
  {Fx.tier_cost(base, Fx.price(rows, m, t)) == Nat.mul(base, 100n) : Nat}

# LAW facts_tier_price_openai_oracle: the shipped OpenAI rows give the multiplier of the old OpenAI
# function for every model and tier
law facts_tier_price_openai_oracle:
  for m: Nat
  for t: Nat
  {Maybe.default(&2, Nat, Fx.price(Fx.prices.openai(), m, t), 100n) == Fx.price.old.openai(m, t) : Nat}

# LAW facts_tier_price_codex_oracle: the shipped Codex rows give the multiplier of the old Codex
# function for every model and tier
law facts_tier_price_codex_oracle:
  for m: Nat
  for t: Nat
  {Maybe.default(&2, Nat, Fx.price(Fx.prices.codex(), m, t), 100n) == Fx.price.old.codex(m, t) : Nat}

# LAW facts_cache_write_1h_own_rate: a 1h cache write of a model that no row prices costs the model's own
# cache write rate, never a price borrowed from another provider
law facts_cache_write_1h_own_rate:
  for +input: Nat
  for +write: Nat
  {Fx.rate_1h(None{}, input, write) == write : Nat}

# (S6.10) The model's terms the entry bend/ffi_model_facts.bend calls
# ------------------------------------------------------------------

# The model's own terms, independently: a known flag is true exactly at
# 1, an unknown one takes the wire API's default; the effort is the map's
# wire value at the level, else 2 (low) at minimal and low, 3 at medium, 4
# at high, xhigh and max; the price is the first row of the model that
# prices the tier, else the first row of every model that does, else none
def flag_spec(a: If.Ans, d: Bool) -> Bool:
  match a:
    case If.Known{v}:
      match v:
        case 0n:
          False{}
        case 1n+k:
          match k:
            case 0n:
              True{}
            case 1n+j:
              False{}
    case If.Unknown{}:
      d

def effort_spec.dflt(l: Fx.ELv) -> Nat:
  match l:
    case Fx.EMinimal{}:
      2n
    case Fx.ELow{}:
      2n
    case Fx.EMedium{}:
      3n
    case Fx.EHigh{}:
      4n
    case Fx.EXhigh{}:
      4n
    case Fx.EMax{}:
      4n

def effort_spec.at(m: Fx.EMap, l: Fx.ELv) -> Maybe<&2, Maybe<&2, Nat>>:
  match m:
    case Fx.EMap{mi, lo, me, hi, xh, mx}:
      match l:
        case Fx.EMinimal{}:
          mi
        case Fx.ELow{}:
          lo
        case Fx.EMedium{}:
          me
        case Fx.EHigh{}:
          hi
        case Fx.EXhigh{}:
          xh
        case Fx.EMax{}:
          mx

def effort_spec.of(e: Maybe<&2, Maybe<&2, Nat>>, d: Nat) -> Nat:
  match e:
    case None{}:
      d
    case Some{w}:
      Maybe.default(&2, Nat, w, d)

def effort_spec(+m: Fx.EMap, +l: Fx.ELv) -> Nat:
  effort_spec.of(effort_spec.at(m, l), effort_spec.dflt(l))

def price_spec.pick(hit: Bool, k: Nat, later: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{k}
    case False{}:
      later

def price_spec.exact(+m: Nat, rm: Maybe<&2, Nat>) -> Bool:
  match rm:
    case None{}:
      False{}
    case Some{x}:
      Nat.is_eq(x, m)

def price_spec.wide(rm: Maybe<&2, Nat>) -> Bool:
  match rm:
    case None{}:
      True{}
    case Some{x}:
      False{}

# the first row of the model m that prices the tier t
def price_spec.of_model(rows: List<&2, Fx.PRow>, +m: Nat, +t: Nat) -> Maybe<&2, Nat>:
  match rows:
    case Nil{}:
      None{}
    case r <> more:
      match r:
        case Fx.PRow{rm, rt, k}:
          price_spec.pick(Bool.and(price_spec.exact(m, rm), Nat.is_eq(rt, t)), k, price_spec.of_model(more, m, t))

# the first row of every model that prices the tier t
def price_spec.of_all(rows: List<&2, Fx.PRow>, +t: Nat) -> Maybe<&2, Nat>:
  match rows:
    case Nil{}:
      None{}
    case r <> more:
      match r:
        case Fx.PRow{rm, rt, k}:
          price_spec.pick(Bool.and(price_spec.wide(rm), Nat.is_eq(rt, t)), k, price_spec.of_all(more, t))

def price_spec.or(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match a:
    case None{}:
      b
    case Some{k}:
      Some{k}

def price_spec(+rows: List<&2, Fx.PRow>, +m: Nat, +t: Nat) -> Maybe<&2, Nat>:
  price_spec.or(price_spec.of_model(rows, m, t), price_spec.of_all(rows, t))

# LAW facts_flag_exact: a flag decision is exactly: a known answer is true only when it is 1, an unknown one takes the wire API's default
law facts_flag_exact:
  for a: If.Ans
  for d: Bool
  {Fx.flag(a, d) == flag_spec(a, d) : Bool}

# LAW facts_effort_exact: the Bedrock effort is exactly the map's wire value at the level, else low at minimal and low, medium at medium, high at high, xhigh and max (a null entry takes the default too)
law facts_effort_exact:
  for +m: Fx.EMap
  for +l: Fx.ELv
  {Fx.effort(m, l) == effort_spec(m, l) : Nat}

# LAW facts_price_exact: a tier's multiplier is exactly the first row of the model that prices the tier, else the first row of every model that does, else none
law facts_price_exact:
  for +rows: List<&2, Fx.PRow>
  for +m: Nat
  for +t: Nat
  {Fx.price(rows, m, t) == price_spec(rows, m, t) : Maybe<&2, Nat>}

def customs_spec(c: Fx.Customs, l: Fx.Lv) -> Maybe<&2, Nat>:
  match c:
    case Fx.Customs{mi, lo, me, hi}:
      match l:
        case Fx.Minimal{}:
          mi
        case Fx.Low{}:
          lo
        case Fx.Medium{}:
          me
        case Fx.High{}:
          hi

# LAW facts_customs_at_exact: the user's budget of a level is exactly the user's budget written for that level (minimal, low, medium, high), never another level's
law facts_customs_at_exact:
  for c: Fx.Customs
  for l: Fx.Lv
  {Fx.Customs.at(c, l) == customs_spec(c, l) : Maybe<&2, Nat>}

# LAW facts_aux_exact: an auxiliary call's output cap is exactly the high budget (the user's, else the default) plus the answer's tokens, held at the top
law facts_aux_exact:
  for c: Fx.Customs
  for d: Fx.Budgets
  for +a: Nat
  for +top: Nat
  {Fx.aux(c, d, a, top) == Fx.aux_cap.within(Maybe.default(&2, Nat, customs_spec(c, Fx.High{}), Fx.Budgets.at(d, Fx.High{})), a, top) : Nat}
