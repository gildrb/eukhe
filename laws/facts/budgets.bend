# eukhe: the laws of area facts, section budgets: the thinking budgets of the entry bend/ffi_facts.bend, by its
# wire and by the grammar's spelling

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_facts.bend as FFx
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase

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

def core_win_fit(w: Fx.Win) -> Bool:
  match w:
    case Fx.Win{n, p, s, f, st}:
      Bool.and(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(p), Bool.and(LawsBase.wire_fits(s), LawsBase.wire_fits(f))))

def core_facts_req_fits(q: FFx.Req) -> Bool:
  match q:
    case FFx.Level{l, c, d}:
      Bool.and(core_customs_fit(c), core_budgets_fit(d))
    case FFx.Room{b, m, a}:
      Bool.and(LawsBase.wire_fits(b), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(a)))
    case FFx.Adjust{base, mm, l, c, d, a, w}:
      Bool.and(LawsBase.core_mfits(base), Bool.and(LawsBase.wire_fits(mm), Bool.and(core_customs_fit(c), Bool.and(core_budgets_fit(d), Bool.and(LawsBase.wire_fits(a), core_win_fit(w))))))
    case FFx.Google{rule, c, l}:
      Bool.and(core_mbudgets_fit(rule), core_customs_fit(c))
    case FFx.Aux{c, d, a, top}:
      Bool.and(core_customs_fit(c), Bool.and(core_budgets_fit(d), Bool.and(LawsBase.wire_fits(a), LawsBase.wire_fits(top))))
    case FFx.Cap{x, mm, n, w}:
      Bool.and(LawsBase.core_mfits(x), Bool.and(LawsBase.wire_fits(mm), core_win_fit(w)))

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
#   tokens swapped, the ceiling and the budget swapped in the reply, the
#   window facts lost or misread
law core_facts_adjust:
  for +base: Maybe<&2, Nat>
  for +mm: Nat
  for +l: Fx.ELv
  for +c: Fx.Customs
  for +d: Fx.Budgets
  for +a: Nat
  for +w: Fx.Win
  for h: {core_facts_req_fits(FFx.Adjust{base, mm, l, c, d, a, w}) == True{} : Bool}
  {FFx.ffi(FFx.put_req(FFx.Adjust{base, mm, l, c, d, a, w}, "")) == FFx.put_fit(Fx.adjust(base, mm, l, c, d, a, w), "") : String}

# LAW core_facts_cap (R2): the cap request answers the output cap of the request: none (0) or the cap
# EXCLUDES: the caller's cap read as none, the catalog's max and the window
#   swapped, needs or stops lost or flipped, an omitted cap read back as a cap
law core_facts_cap:
  for +x: Maybe<&2, Nat>
  for +mm: Nat
  for +n: Bool
  for +w: Fx.Win
  for h: {core_facts_req_fits(FFx.Cap{x, mm, n, w}) == True{} : Bool}
  {FFx.ffi(FFx.put_req(FFx.Cap{x, mm, n, w}, "")) == FFx.put_mnat(Fx.cap(x, mm, n, w), "") : String}

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
# cap, the model's cap, the level, the user's budgets, the defaults, the
# answer's tokens and the window facts (window, prompt, safety, floor,
# stops), as `api/simple_options.rs` writes them
# EXCLUDES: a vacuous core_facts_round_trip, fields or tags in another
#   order than Rust's
law core_facts_req_example:
  {core_facts_req_fits(FFx.Adjust{Some{100n}, 64n, Fx.EXhigh{}, Fx.Customs{None{}, Some{5n}, None{}, None{}}, Fx.Budgets{1n, 2n, 3n, 4n}, 8n, Fx.Win{9n, 5n, 4n, 1n, False{}}}) == True{} : Bool} & {FFx.put_req(FFx.Adjust{Some{100n}, 64n, Fx.EXhigh{}, Fx.Customs{None{}, Some{5n}, None{}, None{}}, Fx.Budgets{1n, 2n, 3n, 4n}, 8n, Fx.Win{9n, 5n, 4n, 1n, False{}}}, "") == "2,1,100,64,4,0,1,5,0,0,1,2,3,4,8,9,5,4,1,F" : String}

# LAW core_facts_cap_example (R1): anchor: a cap request is its tag, the caller's cap, the
# catalog's max, needs, then the window facts, as `api/simple_options.rs`
# writes them; without a caller's cap, a host that leaves the default cap
# out (needs F) answers none (0), one that takes it (needs T) with a
# catalog max far below the window answers that max
# EXCLUDES: a vacuous core_facts_cap, fields in another order than Rust's,
#   none and a cap swapped in the reply
law core_facts_cap_example:
  {FFx.put_req(FFx.Cap{None{}, 64n, False{}, Fx.Win{64n, 30n, 4n, 1n, False{}}}, "") == "5,0,64,F64,30,4,1,F" : String} & {FFx.ffi("5,0,64,F64,30,4,1,F") == "0," : String} & {FFx.ffi("5,0,20,T100,10,4,1,F") == "1,20," : String}

# LAW core_facts_reply_example (R2): anchor: a Google budget is 0 dynamic, 1 then the tokens, 2
# unordered; a fit is the ceiling, then the budget
# EXCLUDES: replies the Rust reader reads as other values
law core_facts_reply_example:
  {FFx.put_gb(Fx.Dynamic{}, FFx.put_gb(Fx.Tokens{5n}, FFx.put_gb(Fx.Unordered{}, ""))) == "0,1,5,2," : String} & {FFx.put_fit(Fx.Fit{9n, 4n}, "") == "9,4," : String}

# LAW core_facts_malformed_example (R3): witness: a malformed budget request exists (an unknown tag)
# EXCLUDES: a vacuous core_facts_malformed
law core_facts_malformed_example:
  {FFx.get_req("6,") == Wr.Bad{} : Wr.Dec<FFx.Req>} & {FFx.ffi("6,") == Wr.err("budget request: malformed") : String}

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

# the window facts: the window, the prompt, the safety, the floor, then
# stops (a Bool)
def facts_spell_win(w: Fx.Win, rest: String) -> String:
  match w:
    case Fx.Win{n, p, s, f, st}:
      Wr.put_nat(n, Wr.put_nat(p, Wr.put_nat(s, Wr.put_nat(f, Wr.put_bool(st, rest)))))

# a request: its tag (level 0, room 1, adjust 2, Google 3, aux 4, cap 5),
# then its fields in Rust's order, then rest
def facts_spell_req(q: FFx.Req, rest: String) -> String:
  match q:
    case FFx.Level{l, c, d}:
      Wr.put_nat(0n, facts_spell_elv(l, facts_spell_customs(c, facts_spell_budgets(d, rest))))
    case FFx.Room{b, m, a}:
      Wr.put_nat(1n, Wr.put_nat(b, Wr.put_nat(m, Wr.put_nat(a, rest))))
    case FFx.Adjust{base, mm, l, c, d, a, w}:
      Wr.put_nat(2n, facts_spell_mnat(base, Wr.put_nat(mm, facts_spell_elv(l, facts_spell_customs(c, facts_spell_budgets(d, Wr.put_nat(a, facts_spell_win(w, rest))))))))
    case FFx.Google{rule, c, l}:
      Wr.put_nat(3n, facts_spell_mbudgets(rule, facts_spell_customs(c, facts_spell_lv(l, rest))))
    case FFx.Aux{c, d, a, top}:
      Wr.put_nat(4n, facts_spell_customs(c, facts_spell_budgets(d, Wr.put_nat(a, Wr.put_nat(top, rest)))))
    case FFx.Cap{x, mm, n, w}:
      Wr.put_nat(5n, facts_spell_mnat(x, Wr.put_nat(mm, Wr.put_bool(n, facts_spell_win(w, rest)))))

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
    case FFx.Adjust{base, mm, l, c, d, a, w}:
      facts_spell_fit(Fx.adjust(base, mm, l, c, d, a, w), "")
    case FFx.Google{rule, c, l}:
      facts_spell_gb(Fx.gbudget(rule, c, l), "")
    case FFx.Aux{c, d, a, top}:
      Wr.put_nat(Fx.aux(c, d, a, top), "")
    case FFx.Cap{x, mm, n, w}:
      facts_spell_mnat(Fx.cap(x, mm, n, w), "")

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

# LAW core_facts_unknown_request: a request tag of 6 or more (of any length) answers the error
# form "budget request: malformed", whatever follows
# EXCLUDES: an unknown request read as a known one, or as another error
law core_facts_unknown_request:
  for +n: Nat
  for +rest: String
  {FFx.ffi(Wr.put_nat(6n+n, rest)) == Wr.err("budget request: malformed") : String}

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
# model cap 9, low, answer 2 and an unknown window (0, 0, 0, 0, F)
# answers ceiling 5, budget 2; with no cap,
# model cap 6, high, the user's 7 answers 6 then 4; a Google request with
# no rule and no user's budget is dynamic (0,), with rule 1, 2, 3, 4 and
# the user's low 9 is 1 then 4, an unordered rule answers 2; an aux
# request answers 2 more than the high budget (6,), held at the top 5;
# request tag 6, level tag 6, rule tag 2, budget level tag 4 and no input
# are malformed; a request with input left over is refused
# EXCLUDES: a tag table both sides of the Bend entry agree on but Rust
#   does not, a reply in another order, an unknown tag read as a known
#   one, the two error texts swapped
law core_facts_tags_example:
  {[FFx.ffi("0,4,0,0,0,0,1,2,3,4,"), FFx.ffi("0,2,0,0,1,7,0,1,2,3,4,"), FFx.ffi("1,9,8,3,"), FFx.ffi("2,1,3,9,1,0,0,0,0,1,2,3,4,2,0,0,0,0,F"), FFx.ffi("2,0,6,3,0,0,0,1,7,1,2,3,4,2,0,0,0,0,F"), FFx.ffi("3,0,0,0,0,0,2,"), FFx.ffi("3,1,1,2,3,4,0,1,9,0,0,1,"), FFx.ffi("3,1,4,3,2,1,0,0,0,0,0,"), FFx.ffi("4,0,0,0,0,1,2,3,4,2,9,"), FFx.ffi("4,0,0,0,0,1,2,3,4,2,5,"), FFx.ffi("6,"), FFx.ffi("0,6,"), FFx.ffi("3,2,"), FFx.ffi("3,0,0,0,0,0,4,"), FFx.ffi(""), FFx.ffi("1,9,8,3,x")] == ["4,", "7,", "5,", "5,2,", "6,4,", "0,", "1,4,", "2,", "6,", "5,", Wr.err("budget request: malformed"), Wr.err("budget request: malformed"), Wr.err("budget request: malformed"), Wr.err("budget request: malformed"), Wr.err("budget request: malformed"), Wr.err("budget request: input left over")] : List<&2, String>}
