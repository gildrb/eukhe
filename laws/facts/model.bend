# eukhe: the laws of area facts, section model: the model and provider facts (S6.10) of bend/facts.bend, the
# output cap, and the model's terms the entry bend/ffi_model_facts.bend calls

import Base
import ../../bend/facts.bend as Fx

# ---- model_facts ----

# LAWS (S6.10): model and provider facts are data. A wire API decides a
# fact of a model only from the quirks rulebook's answer (and the model's
# explicit compat flag or the user's setting), the thinking budgets stay
# inside the model's limits, and where a fact moved from code into data the
# data gives the answers the code gave. Each law is an open claim about the
# model in bend/facts.bend; PROOF.bend proves them (as Facts.<law>)
# with the lemmas of proof/facts/. The decisions run as the compiled core
# (entries bend/ffi_facts.bend, laws/facts/budgets.bend and entry.bend;
# bend/ffi_model_facts.bend, laws/facts/adaptive.bend and
# laws/model_facts.bend).
#
# Requirements (stated in the header of bend/facts.bend and the Rust doc
# comments its functions name; omp at c28b3e3 no longer has these code
# paths in this shape, so the ported Rust is the source), each with the
# laws that state it:
#   S6.10.1 a wire API decides a fact only from the rulebook's answer, the
#     model's compat flag or the user's setting: adaptive thinking is the
#     compat flag, else the rulebook's flag with the default false
#     (laws/facts/adaptive.bend facts_adaptive_compat_wins,
#     facts_adaptive_else_flag); a flag is true only at a known 1, an
#     unknown one the wire API's default (at the entry: laws/model_facts.bend
#     model_facts_ffi_flag_known, model_facts_ffi_flag_unknown_default; the
#     rulebook lookup: laws/infer.bend facts_rulebook_decides,
#     facts_rulebook_default)
#   S6.10.2 the thinking budgets stay inside the model's limits: the Google
#     budget (facts_google_*), the room under a ceiling (facts_room_*), the
#     fitted ceiling and budget (facts_fit_*), the auxiliary call's cap
#     (facts_aux_*); the level request's budget (the user's over the
#     default, xhigh and max at high) at the entry: laws/facts/entry.bend
#     facts_ffi_exact
#   S6.10.3 where a fact moved from code into data, the data gives the old
#     code's answers: facts_bedrock_effort_oracle (the old Rust
#     `old_effort`), facts_bedrock_budget_oracle
#   S6.10.4 prices are data: the first row of the model that prices the
#     tier, else the first row of every model, else none
#     (facts_tier_price_model_row_first, facts_price_wide_row_next,
#     facts_price_no_row_none); the shipped rows give the old multipliers
#     (facts_tier_price_openai_oracle, facts_tier_price_codex_oracle)
#   S6.10.5 the Bedrock reasoning fields of the rulebook's shape
#     (facts_reasoning_exact); that the rulebook gives each catalog model
#     the shape of the old name checks is the Rust test
#     `the_reasoning_shape_is_the_rulebook_answer_of_the_old_name_checks`
#     (crates/eukhe-ai/src/api/bedrock_converse_stream/convert/facts_tests.rs),
#     not a law here: no Bend def reads rulebook.json
#   A1 the output cap: the wish, shrunk only on a real window conflict,
#     never below the floor, omitted only when the max is unknown
#     (facts_cap_*)

# (S6.10) The model's terms the entry bend/ffi_model_facts.bend calls
# ------------------------------------------------------------------

# the map's entry of a level (the projection of facts_bedrock_effort_oracle
# and of effort_old below)
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

# the user's budget of a level: the field of that level (laws/facts/entry.bend
# and the facts_google_* laws)
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

# a budget rule falls somewhere: a level's budget below the one before it
# (low below minimal, medium below low, or high below medium)
def rule_falls(+mi: Nat, +lo: Nat, +me: Nat, +hi: Nat) -> Bool:
  Bool.or(Nat.is_lt(lo, mi), Bool.or(Nat.is_lt(me, lo), Nat.is_lt(hi, me)))

# the rule's budget of a level, read off the rule's four fields
def rule_at(+mi: Nat, +lo: Nat, +me: Nat, +hi: Nat, l: Fx.Lv) -> Nat:
  match l:
    case Fx.Minimal{}:
      mi
    case Fx.Low{}:
      lo
    case Fx.Medium{}:
      me
    case Fx.High{}:
      hi

# LAW facts_google_unordered_refused: a budget rule that falls somewhere (a level's budget below
# the one before it) gives no Google budget, whatever the user's budgets
# and the level: the rule is refused, never clamped into a range it does
# not have (Rust `u64::clamp` panicked on minimal > high)
# EXCLUDES: a budget from a rule with no range, a panic, a rule refused
#   only when minimal is above high (a low below minimal let through)
law facts_google_unordered_refused:
  for +mi: Nat
  for +lo: Nat
  for +me: Nat
  for +hi: Nat
  for +c: Fx.Customs
  for +l: Fx.Lv
  for +falls: {rule_falls(mi, lo, me, hi) == True{} : Bool}
  {Fx.gbudget(Some{Fx.Budgets{mi, lo, me, hi}}, c, l) == Fx.Unordered{} : Fx.GB}

# LAW facts_google_user_kept: under a budget rule that never falls, the user's budget n of the
# level (the field of that level of the user's budgets), inside the rule's
# minimal..high, is the Google budget as it is
# EXCLUDES: a user's budget ignored for the rule's, a budget inside the
#   range moved, the user's budget of another level, an ordered rule
#   refused
law facts_google_user_kept:
  for +mi: Nat
  for +lo: Nat
  for +me: Nat
  for +hi: Nat
  for +c: Fx.Customs
  for +l: Fx.Lv
  for +n: Nat
  for +ok: {rule_falls(mi, lo, me, hi) == False{} : Bool}
  for +u: {customs_spec(c, l) == Some{n} : Maybe<&2, Nat>}
  for +above: {Nat.is_le(mi, n) == True{} : Bool}
  for +below: {Nat.is_le(n, hi) == True{} : Bool}
  {Fx.gbudget(Some{Fx.Budgets{mi, lo, me, hi}}, c, l) == Fx.Tokens{n} : Fx.GB}

# LAW facts_google_user_raised: under a budget rule that never falls, a user's budget of the level
# below the rule's minimal is raised to the minimal
# EXCLUDES: a budget below the model's minimal sent (the provider refuses
#   it), a raise to another level's budget
law facts_google_user_raised:
  for +mi: Nat
  for +lo: Nat
  for +me: Nat
  for +hi: Nat
  for +c: Fx.Customs
  for +l: Fx.Lv
  for +n: Nat
  for +ok: {rule_falls(mi, lo, me, hi) == False{} : Bool}
  for +u: {customs_spec(c, l) == Some{n} : Maybe<&2, Nat>}
  for +low: {Nat.is_lt(n, mi) == True{} : Bool}
  {Fx.gbudget(Some{Fx.Budgets{mi, lo, me, hi}}, c, l) == Fx.Tokens{mi} : Fx.GB}

# LAW facts_google_user_lowered: under a budget rule that never falls, a user's budget of the level
# above the rule's high is lowered to the high
# EXCLUDES: a budget past the model's high sent, a cut to another level's
#   budget
law facts_google_user_lowered:
  for +mi: Nat
  for +lo: Nat
  for +me: Nat
  for +hi: Nat
  for +c: Fx.Customs
  for +l: Fx.Lv
  for +n: Nat
  for +ok: {rule_falls(mi, lo, me, hi) == False{} : Bool}
  for +u: {customs_spec(c, l) == Some{n} : Maybe<&2, Nat>}
  for +high: {Nat.is_lt(hi, n) == True{} : Bool}
  {Fx.gbudget(Some{Fx.Budgets{mi, lo, me, hi}}, c, l) == Fx.Tokens{hi} : Fx.GB}

# LAW facts_google_rule_default: under a budget rule that never falls, with no user's budget of the
# level, the Google budget is the rule's budget of the level
# EXCLUDES: a dynamic budget for a model with a rule, another level's
#   budget, the rule's budget moved
law facts_google_rule_default:
  for +mi: Nat
  for +lo: Nat
  for +me: Nat
  for +hi: Nat
  for +c: Fx.Customs
  for +l: Fx.Lv
  for +ok: {rule_falls(mi, lo, me, hi) == False{} : Bool}
  for +u: {customs_spec(c, l) == None{} : Maybe<&2, Nat>}
  {Fx.gbudget(Some{Fx.Budgets{mi, lo, me, hi}}, c, l) == Fx.Tokens{rule_at(mi, lo, me, hi, l)} : Fx.GB}

# LAW facts_fit_budget_under_ceiling: a fitted thinking budget is never above the response ceiling
law facts_fit_budget_under_ceiling:
  for +base: Maybe<&2, Nat>
  for +mm: Nat
  for +b: Nat
  for +a: Nat
  for +win: Fx.Win
  {Nat.is_le(Fx.Fit.budget(Fx.fit(base, mm, b, a, win)), Fx.Fit.max(Fx.fit(base, mm, b, a, win))) == True{} : Bool}

# LAW facts_fit_ceiling_under_model: and the response ceiling is never above the model's output cap
# (with a floor at most that cap)
# EXCLUDES: a thinking request past the catalog's max
law facts_fit_ceiling_under_model:
  for +base: Maybe<&2, Nat>
  for +mm: Nat
  for +b: Nat
  for +a: Nat
  for +w: Nat
  for +p: Nat
  for +s: Nat
  for +f: Nat
  for +st: Bool
  for hf: {Nat.is_le(f, mm) == True{} : Bool}
  {Nat.is_le(Fx.Fit.max(Fx.fit(base, mm, b, a, Fx.Win{w, p, s, f, st})), mm) == True{} : Bool}

# LAW facts_room_leaves_the_answer: a budget capped for answer room leaves the answer its tokens under
# the ceiling
law facts_room_leaves_the_answer:
  for +b: Nat
  for +m: Nat
  for +a: Nat
  for fits: {Nat.is_le(a, m) == True{} : Bool}
  {Nat.is_le(Nat.add(Fx.room(b, m, a), a), m) == True{} : Bool}

# LAW facts_room_at_most_budget: a budget capped for answer room is at most the budget
# EXCLUDES: a room past the budget asked for (thinking the user did not
#   allow)
law facts_room_at_most_budget:
  for +b: Nat
  for +m: Nat
  for +a: Nat
  {Nat.is_le(Fx.room(b, m, a), b) == True{} : Bool}

# LAW facts_room_cut_only_for_answer: when the ceiling m holds the answer's tokens a, a budget capped
# for answer room is the budget, or exactly fills the ceiling with the
# answer (a plus it is m): it is cut only as far as the answer needs
# (with facts_room_at_most_budget and facts_room_leaves_the_answer: the
# smaller of the budget and m - a)
# EXCLUDES: a budget cut further than the answer needs (half the room, 0)
law facts_room_cut_only_for_answer:
  for +b: Nat
  for +m: Nat
  for +a: Nat
  for +fits: {Nat.is_le(a, m) == True{} : Bool}
  {Bool.or(Nat.is_eq(Fx.room(b, m, a), b), Nat.is_eq(Nat.add(a, Fx.room(b, m, a)), m)) == True{} : Bool}

# LAW facts_room_no_room: a ceiling below the answer's tokens leaves no room for a budget
# EXCLUDES: a budget that takes the little room the answer has
law facts_room_no_room:
  for +b: Nat
  for +m: Nat
  for +a: Nat
  for +h: {Nat.is_lt(m, a) == True{} : Bool}
  {Fx.room(b, m, a) == 0n : Nat}

# LAW facts_aux_keeps_answer_room: an auxiliary call's output cap is the level request's high budget
# (the user's, else the default: Fx.budget at high) plus the answer's
# tokens, whenever that sum is at most the top
# EXCLUDES: thinking taken out of the answer's room, the low or default
#   budget for a user's high budget, a cap cut below the top with room
#   to spare
law facts_aux_keeps_answer_room:
  for +c: Fx.Customs
  for +d: Fx.Budgets
  for +a: Nat
  for +top: Nat
  for +fits: {Nat.is_le(Nat.add(Fx.budget(c, d, Fx.High{}), a), top) == True{} : Bool}
  {Fx.aux(c, d, a, top) == Nat.add(Fx.budget(c, d, Fx.High{}), a) : Nat}

# LAW facts_aux_saturates_at_top: and is the top when that sum passes it (Rust `saturating_add`
# at the wire's largest Nat)
# EXCLUDES: a cap past the top, a wrapped or reduced cap
law facts_aux_saturates_at_top:
  for +c: Fx.Customs
  for +d: Fx.Budgets
  for +a: Nat
  for +top: Nat
  for +past: {Nat.is_lt(top, Nat.add(Fx.budget(c, d, Fx.High{}), a)) == True{} : Bool}
  {Fx.aux(c, d, a, top) == top : Nat}

# x held inside lo..hi: never below lo, never above hi (laws/facts/entry.bend)
def budgets.held(x: Nat, +lo: Nat, +hi: Nat) -> Nat:
  Nat.max(lo, Nat.min(x, hi))

# LAW facts_budget_levels: the budget level of a request's level: each level keeps its own,
# xhigh and max take high
law facts_budget_levels:
  {[Fx.Lv.of(Fx.EMinimal{}), Fx.Lv.of(Fx.ELow{}), Fx.Lv.of(Fx.EMedium{}), Fx.Lv.of(Fx.EHigh{}), Fx.Lv.of(Fx.EXhigh{}), Fx.Lv.of(Fx.EMax{})] == [Fx.Minimal{}, Fx.Low{}, Fx.Medium{}, Fx.High{}, Fx.High{}, Fx.High{}] : List<&2, Fx.Lv>}

# the fit of the response ceiling m: the budget b, capped so that a
# tokens stay for the answer (laws/facts/entry.bend)
def budgets.fit(+m: Nat, +b: Nat, +a: Nat) -> Fx.Fit:
  Fx.Fit{m, Nat.min(b, Nat.sub(m, a))}

# the caller's cap of the output cap that bounds the thinking ceiling: the
# caller's answer cap x plus the budget b, at most the model's cap mm; none
# without a caller's cap
def fit_caller(base: Maybe<&2, Nat>, +mm: Nat, +b: Nat) -> Maybe<&2, Nat>:
  match base:
    case None{}:
      None{}
    case Some{x}:
      Some{Nat.min(Nat.add(x, b), mm)}

# LAW facts_fit_ceiling_is_the_cap: the thinking ceiling is the output cap (Fx.cap, facts_cap_*) of
# a request that needs the field, whose caller's cap is the caller's
# answer cap plus the budget, at most the model's cap (thinking on top of
# the answer), or none without a caller's cap: one window rule for both
# EXCLUDES: thinking taken out of the answer's cap, a ceiling past the
#   model's cap, a second window clamp (the double clamp of the Anthropic
#   path), a ceiling that bypasses the cap rule, a ceiling below the
#   catalog's max with room to spare
law facts_fit_ceiling_is_the_cap:
  for +base: Maybe<&2, Nat>
  for +mm: Nat
  for +b: Nat
  for +a: Nat
  for +win: Fx.Win
  {Some{Fx.Fit.max(Fx.fit(base, mm, b, a, win))} == Fx.cap(fit_caller(base, mm, b), mm, True{}, win) : Maybe<&2, Nat>}

# LAW facts_fit_budget_at_most_level: a fitted thinking budget is at most the budget asked for
# EXCLUDES: a fitted budget grown past the level's budget
law facts_fit_budget_at_most_level:
  for +base: Maybe<&2, Nat>
  for +mm: Nat
  for +b: Nat
  for +a: Nat
  for +win: Fx.Win
  {Nat.is_le(Fx.Fit.budget(Fx.fit(base, mm, b, a, win)), b) == True{} : Bool}

# LAW facts_fit_budget_cut_only_for_answer: when the ceiling holds the answer's tokens a, the fitted
# budget is the budget asked for, or exactly fills the ceiling with the
# answer: it is cut only as far as the answer needs (with
# facts_fit_answer_room and facts_fit_budget_at_most_level: the smaller of
# the budget and the ceiling minus a)
# EXCLUDES: a budget cut further than the answer needs, a budget kept
#   whole that leaves the answer less than its tokens (with
#   facts_fit_answer_room)
law facts_fit_budget_cut_only_for_answer:
  for +base: Maybe<&2, Nat>
  for +mm: Nat
  for +b: Nat
  for +a: Nat
  for +win: Fx.Win
  for +h: {Nat.is_le(a, Fx.Fit.max(Fx.fit(base, mm, b, a, win))) == True{} : Bool}
  {Bool.or(Nat.is_eq(Fx.Fit.budget(Fx.fit(base, mm, b, a, win)), b), Nat.is_eq(Nat.add(a, Fx.Fit.budget(Fx.fit(base, mm, b, a, win))), Fx.Fit.max(Fx.fit(base, mm, b, a, win)))) == True{} : Bool}

# LAW facts_fit_saturated_caller (the Nat range): : a caller's cap at or above the model's cap fits as
# no cap, so the cap Rust saturates at the wire's largest Nat (10^14-1)
# fits as it did unsaturated whenever the model's cap is below it
law facts_fit_saturated_caller:
  for +x: Nat
  for +mm: Nat
  for +b: Nat
  for +a: Nat
  for +win: Fx.Win
  for +above: {Nat.is_le(mm, x) == True{} : Bool}
  {Fx.fit(Some{x}, mm, b, a, win) == Fx.fit(None{}, mm, b, a, win) : Fx.Fit}

# LAW facts_fit_saturated_budget (the Nat range): : two budgets at or above the model's cap fit alike
# (with a floor at most that cap), so a budget Rust saturates at the
# wire's largest Nat fits as it did unsaturated whenever the model's cap is
# below it
law facts_fit_saturated_budget:
  for +base: Maybe<&2, Nat>
  for +mm: Nat
  for +b1: Nat
  for +b2: Nat
  for +a: Nat
  for +w: Nat
  for +p: Nat
  for +s: Nat
  for +f: Nat
  for +st: Bool
  for +h1: {Nat.is_le(mm, b1) == True{} : Bool}
  for +h2: {Nat.is_le(mm, b2) == True{} : Bool}
  for +hf: {Nat.is_le(f, mm) == True{} : Bool}
  {Fx.fit(base, mm, b1, a, Fx.Win{w, p, s, f, st}) == Fx.fit(base, mm, b2, a, Fx.Win{w, p, s, f, st}) : Fx.Fit}

# LAW facts_fit_answer_room: the thinking budget never starves the answer: when the ceiling holds
# the answer's tokens a, the budget plus a is at most the ceiling
# EXCLUDES: a reply that spends its whole output cap on thinking (stop
#   reason length, no text: the budget under the ceiling but over the
#   ceiling minus the answer's room)
law facts_fit_answer_room:
  for +base: Maybe<&2, Nat>
  for +mm: Nat
  for +b: Nat
  for +a: Nat
  for +win: Fx.Win
  for h: {Nat.is_le(a, Fx.Fit.max(Fx.fit(base, mm, b, a, win))) == True{} : Bool}
  {Nat.is_le(Nat.add(Fx.Fit.budget(Fx.fit(base, mm, b, a, win)), a), Fx.Fit.max(Fx.fit(base, mm, b, a, win))) == True{} : Bool}

# LAW facts_fit_no_room_no_thinking: a ceiling below the answer's tokens leaves no thinking budget
# EXCLUDES: a budget that takes the little room the answer has
law facts_fit_no_room_no_thinking:
  for +base: Maybe<&2, Nat>
  for +mm: Nat
  for +b: Nat
  for +a: Nat
  for +win: Fx.Win
  for h: {Nat.is_lt(Fx.Fit.max(Fx.fit(base, mm, b, a, win)), a) == True{} : Bool}
  {Fx.Fit.budget(Fx.fit(base, mm, b, a, win)) == 0n : Nat}

# (facts) The output cap
# ----------------------

# the request's wish: the caller's cap, else the catalog's max
def cap_want(caller: Maybe<&2, Nat>, mm: Nat) -> Nat:
  Maybe.default(&2, Nat, caller, mm)

# a real conflict with the window: a known window, a model that does not
# stop at it, and the prompt, the safety and the wish x past it
def cap_conflict(x: Nat, win: Fx.Win) -> Bool:
  match win:
    case Fx.Win{+w, p, s, f, st}:
      Bool.and(Bool.not(st), Bool.and(Nat.is_lt(0n, w), Nat.is_lt(w, Nat.add(Nat.add(p, s), x))))

# the room the window leaves after the prompt and the safety, at least the
# floor
def cap_room(win: Fx.Win) -> Nat:
  match win:
    case Fx.Win{w, p, s, f, st}:
      Nat.max(f, Nat.sub(w, Nat.add(p, s)))

# the max is unknown: no caller's cap, a wire API that does not need the
# field, a known window the catalog's max does not go past
def cap_unknown(caller: Maybe<&2, Nat>, mm: Nat, needs: Bool, win: Fx.Win) -> Bool:
  match caller:
    case Some{x}:
      False{}
    case None{}:
      match win:
        case Fx.Win{+w, p, s, f, st}:
          Bool.and(Bool.not(needs), Bool.and(Nat.is_lt(0n, w), Nat.is_le(w, mm)))

def cap_present(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

# LAW facts_cap_keeps_the_want: without a window conflict, the request carries its wish: the
# caller's cap, else the catalog's max
# EXCLUDES: a made-up default cap (16384) or any cap below the catalog's
#   max while the window has room (a reasoning model cut short: stop
#   reason length, thinking only); a shrink with no conflict
law facts_cap_keeps_the_want:
  for +caller: Maybe<&2, Nat>
  for +mm: Nat
  for +needs: Bool
  for +win: Fx.Win
  for h1: {cap_unknown(caller, mm, needs, win) == False{} : Bool}
  for h2: {cap_conflict(cap_want(caller, mm), win) == False{} : Bool}
  {Fx.cap(caller, mm, needs, win) == Some{cap_want(caller, mm)} : Maybe<&2, Nat>}

# LAW facts_cap_shrinks_on_conflict: on a real window conflict, the cap is the room the window leaves
# after the prompt and the safety, at least the floor
# EXCLUDES: a request past the window (the provider refuses it), a shrink
#   to less than the room, a shrink below the floor
law facts_cap_shrinks_on_conflict:
  for +caller: Maybe<&2, Nat>
  for +mm: Nat
  for +needs: Bool
  for +win: Fx.Win
  for h1: {cap_unknown(caller, mm, needs, win) == False{} : Bool}
  for h2: {cap_conflict(cap_want(caller, mm), win) == True{} : Bool}
  {Fx.cap(caller, mm, needs, win) == Some{cap_room(win)} : Maybe<&2, Nat>}

# LAW facts_cap_never_below_floor: a cap the window shrinks is at least the floor
# EXCLUDES: a cap of 0 (or below the floor) for a prompt that fills the
#   window
law facts_cap_never_below_floor:
  for +caller: Maybe<&2, Nat>
  for +mm: Nat
  for +needs: Bool
  for +w: Nat
  for +p: Nat
  for +s: Nat
  for +f: Nat
  for +st: Bool
  for h1: {cap_unknown(caller, mm, needs, Fx.Win{w, p, s, f, st}) == False{} : Bool}
  for h2: {cap_conflict(cap_want(caller, mm), Fx.Win{w, p, s, f, st}) == True{} : Bool}
  {Nat.is_le(f, Maybe.default(&2, Nat, Fx.cap(caller, mm, needs, Fx.Win{w, p, s, f, st}), 0n)) == True{} : Bool}

# LAW facts_cap_stops_never_shrinks: a model that ends its output at the window itself is never
# shrunk: the request carries its wish whatever the prompt
# EXCLUDES: a shrink of a model the provider stops at the window (Claude
#   4.5+ on the Claude API)
law facts_cap_stops_never_shrinks:
  for +caller: Maybe<&2, Nat>
  for +mm: Nat
  for +needs: Bool
  for +w: Nat
  for +p: Nat
  for +s: Nat
  for +f: Nat
  for h1: {cap_unknown(caller, mm, needs, Fx.Win{w, p, s, f, True{}}) == False{} : Bool}
  {Fx.cap(caller, mm, needs, Fx.Win{w, p, s, f, True{}}) == Some{cap_want(caller, mm)} : Maybe<&2, Nat>}

# LAW facts_cap_omits_unknown: with an unknown max (no caller's cap, a wire API that does not need
# the field, a catalog max at or past the window) the field is omitted:
# the provider's own max applies
# EXCLUDES: a made-up cap sent for a model whose max the catalog does not
#   know (a models.json model without maxTokens)
law facts_cap_omits_unknown:
  for +caller: Maybe<&2, Nat>
  for +mm: Nat
  for +needs: Bool
  for +win: Fx.Win
  for h: {cap_unknown(caller, mm, needs, win) == True{} : Bool}
  {Fx.cap(caller, mm, needs, win) == None{} : Maybe<&2, Nat>}

# LAW facts_cap_needs_never_omits: a wire API that needs the field (Anthropic Messages, Bedrock
# Claude) always carries a cap
# EXCLUDES: a request the provider refuses for a missing max_tokens
law facts_cap_needs_never_omits:
  for +caller: Maybe<&2, Nat>
  for +mm: Nat
  for +win: Fx.Win
  {cap_present(Fx.cap(caller, mm, True{}, win)) == True{} : Bool}

# LAW facts_cap_example: anchor: the user's case and its neighbours at small scale: a catalog max
# at the window without a caller's cap is omitted; a max far below the
# window is sent whole; a long prompt shrinks it to the room; a model that
# stops at the window is not shrunk; a wire API that needs the field
# shrinks a max at the window
# EXCLUDES: a spec that is wrong on the cases the Rust tests pin
law facts_cap_example:
  {Fx.cap(None{}, 64n, False{}, Fx.Win{64n, 30n, 4n, 1n, False{}}) == None{} : Maybe<&2, Nat>} &
  {Fx.cap(None{}, 20n, False{}, Fx.Win{100n, 10n, 4n, 1n, False{}}) == Some{20n} : Maybe<&2, Nat>} &
  {Fx.cap(None{}, 20n, False{}, Fx.Win{100n, 90n, 4n, 1n, False{}}) == Some{6n} : Maybe<&2, Nat>} &
  {Fx.cap(None{}, 20n, True{}, Fx.Win{100n, 90n, 4n, 1n, True{}}) == Some{20n} : Maybe<&2, Nat>} &
  {Fx.cap(None{}, 64n, True{}, Fx.Win{64n, 30n, 4n, 1n, False{}}) == Some{30n} : Maybe<&2, Nat>} &
  {Fx.cap(Some{8n}, 64n, False{}, Fx.Win{64n, 99n, 4n, 1n, False{}}) == Some{1n} : Maybe<&2, Nat>}

# LAW facts_aux_cap_within (the Nat range): : the compactor's cap is the thinking budget plus the
# answer, at most top (Rust passes the wire's largest Nat): below top
# the answer keeps its room exactly (facts_aux_keeps_answer_room), at top
# the cap saturates as Rust's `saturating_add` does
law facts_aux_cap_within:
  for +b: Nat
  for +a: Nat
  for +top: Nat
  {Fx.aux_cap.within(b, a, top) == Nat.min(Fx.aux_cap(b, a), top) : Nat}

# (S6.10.3) Oracles: the data gives the answers the code gave
# -----------------------------------------------------------

# The old Bedrock effort rule, as the Rust oracle `old_effort` of
# crates/eukhe-ai/src/api/bedrock_converse_stream/convert/facts_tests.rs
# writes it (the id list before the thinking-level map): a model on the
# native-xhigh id list sends xhigh (5) at xhigh; else the map's wire value
# of the level; else low (2) at minimal and low, medium (3) at medium, high
# (4) at high, xhigh and max. e is the map's entry of the level: missing
# (None), null (Some{None}) or a wire value.
def effort_old.mapped(e: Maybe<&2, Maybe<&2, Nat>>, d: Nat) -> Nat:
  match e:
    case Some{w}:
      match w:
        case Some{v}:
          v
        case None{}:
          d
    case None{}:
      d

def effort_old.xhigh(native: Bool, e: Maybe<&2, Maybe<&2, Nat>>) -> Nat:
  match native:
    case True{}:
      5n
    case False{}:
      effort_old.mapped(e, 4n)

def effort_old(native: Bool, e: Maybe<&2, Maybe<&2, Nat>>, l: Fx.ELv) -> Nat:
  match l:
    case Fx.EMinimal{}:
      effort_old.mapped(e, 2n)
    case Fx.ELow{}:
      effort_old.mapped(e, 2n)
    case Fx.EMedium{}:
      effort_old.mapped(e, 3n)
    case Fx.EHigh{}:
      effort_old.mapped(e, 4n)
    case Fx.EXhigh{}:
      effort_old.xhigh(native, e)
    case Fx.EMax{}:
      effort_old.mapped(e, 4n)

# the map's entry is the wire value xhigh (5)
def effort_old.five(e: Maybe<&2, Maybe<&2, Nat>>) -> Bool:
  match e:
    case Some{w}:
      match w:
        case Some{v}:
          Nat.is_eq(v, 5n)
        case None{}:
          False{}
    case None{}:
      False{}

# the catalog's promise for a model on the native-xhigh id list: its map
# sends xhigh at xhigh (the Rust test
# `a_row_without_native_xhigh_in_its_map_is_sent_high` pins the one row
# that breaks it)
def effort_old.kept(native: Bool, m: Fx.EMap) -> Bool:
  match native:
    case True{}:
      effort_old.five(effort_spec.at(m, Fx.EXhigh{}))
    case False{}:
      True{}

# LAW facts_bedrock_effort_oracle: the Bedrock effort from the thinking-level map is the effort of the
# old Rust rule (the native-xhigh id list, then the map, then the fixed
# table: `old_effort`), at every level, for every map whose model keeps
# the catalog's promise (on the id list: its map sends xhigh at xhigh);
# off the id list this pins the effort of every map and level
# EXCLUDES: a default effort other than the old table (xhigh or max sent
#   as xhigh, minimal sent as minimal), a map's wire value ignored, a null
#   entry sent as a value, a native-xhigh model sent high at xhigh
law facts_bedrock_effort_oracle:
  for +native: Bool
  for +m: Fx.EMap
  for +l: Fx.ELv
  for +ok: {effort_old.kept(native, m) == True{} : Bool}
  {Fx.effort(m, l) == effort_old(native, effort_spec.at(m, l), l) : Nat}

# LAW facts_bedrock_budget_oracle: the budget of budget-based Claude from the rulebook's default
# budgets is the budget of the old Bedrock table, for every user budget
law facts_bedrock_budget_oracle:
  for c: Fx.Customs
  for +l: Fx.Lv
  {Fx.budget(c, Fx.budgets.shipped(), l) == Fx.budget.old(c, l) : Nat}

# (S6.10.4) Prices are data
# -------------------------

# a row of the model m that prices the tier t
def row_of_model(r: Fx.PRow, +m: Nat, +t: Nat) -> Bool:
  match r:
    case Fx.PRow{rm, rt, k}:
      match rm:
        case None{}:
          False{}
        case Some{x}:
          Bool.and(Nat.is_eq(x, m), Nat.is_eq(rt, t))

# a row of every model that prices the tier t
def row_of_all(r: Fx.PRow, +t: Nat) -> Bool:
  match r:
    case Fx.PRow{rm, rt, k}:
      match rm:
        case None{}:
          Nat.is_eq(rt, t)
        case Some{x}:
          False{}

# some row of rows is a row of the model m that prices the tier t
def rows_of_model(rows: List<&2, Fx.PRow>, +m: Nat, +t: Nat) -> Bool:
  match rows:
    case Nil{}:
      False{}
    case r <> more:
      Bool.or(row_of_model(r, m, t), rows_of_model(more, m, t))

# some row of rows is a row of every model that prices the tier t
def rows_of_all(rows: List<&2, Fx.PRow>, +t: Nat) -> Bool:
  match rows:
    case Nil{}:
      False{}
    case r <> more:
      Bool.or(row_of_all(r, t), rows_of_all(more, t))

# LAW facts_tier_price_model_row_first: the first row of the model that prices the tier gives the
# multiplier, whatever rows of every model come before it or any row comes
# after it: the gpt-5.5 priority price is a row of the model 0, not an id
# test in code (facts_tier_price_openai_oracle: the shipped rows)
# EXCLUDES: a row of every model over the model's own row, a later row
#   over an earlier one, the row's multiplier read from another row
law facts_tier_price_model_row_first:
  for +pre: List<&2, Fx.PRow>
  for +post: List<&2, Fx.PRow>
  for +m: Nat
  for +t: Nat
  for +k: Nat
  for +first: {rows_of_model(pre, m, t) == False{} : Bool}
  {Fx.price(List.append(&2, Fx.PRow, pre, Fx.PRow{Some{m}, t, k} <> post), m, t) == Some{k} : Maybe<&2, Nat>}

# LAW facts_price_wide_row_next: with no row of the model that prices the tier, the first row of
# every model that prices it gives the multiplier
# EXCLUDES: a row of another model or another tier taken, a later row of
#   every model over an earlier one, no price where a row of every model
#   prices the tier
law facts_price_wide_row_next:
  for +pre: List<&2, Fx.PRow>
  for +post: List<&2, Fx.PRow>
  for +m: Nat
  for +t: Nat
  for +k: Nat
  for +none: {rows_of_model(List.append(&2, Fx.PRow, pre, Fx.PRow{None{}, t, k} <> post), m, t) == False{} : Bool}
  for +first: {rows_of_all(pre, t) == False{} : Bool}
  {Fx.price(List.append(&2, Fx.PRow, pre, Fx.PRow{None{}, t, k} <> post), m, t) == Some{k} : Maybe<&2, Nat>}

# LAW facts_price_no_row_none: with no row of the model and no row of every model that prices the
# tier, there is no multiplier (Rust bills the base price: a provider that
# does not sell the tier is not billed another's multiplier)
# EXCLUDES: a multiplier made up for a tier no row prices, a row of
#   another model or another tier taken
law facts_price_no_row_none:
  for +rows: List<&2, Fx.PRow>
  for +m: Nat
  for +t: Nat
  for +none: {rows_of_model(rows, m, t) == False{} : Bool}
  for +wide: {rows_of_all(rows, t) == False{} : Bool}
  {Fx.price(rows, m, t) == None{} : Maybe<&2, Nat>}

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

# (S6.10.5) The Bedrock reasoning fields are the rulebook's shape
# ----------------------------------------------------------------
# Rust reads the rulebook's `bedrock_reasoning` (the shape a family of
# rulebook.json names: `claude`, `gpt`, `gpt-oss`) and the map's entry of
# the level; the model decides the fields. The model's terms,
# independently: a level's rank (minimal 0 .. max 5); GPT sends the
# map's wire value, else the larger of low (2) and the rank plus one; gpt-oss
# sends the smaller of high (4) and that default, never reading the map.

def reasoning_spec.rank(l: Fx.ELv) -> Nat:
  match l:
    case Fx.EMinimal{}:
      0n
    case Fx.ELow{}:
      1n
    case Fx.EMedium{}:
      2n
    case Fx.EHigh{}:
      3n
    case Fx.EXhigh{}:
      4n
    case Fx.EMax{}:
      5n

def reasoning_spec.gpt(l: Fx.ELv) -> Nat:
  Nat.max(2n, Nat.add(reasoning_spec.rank(l), 1n))

def reasoning_spec.wire(e: Maybe<&2, Maybe<&2, Nat>>, d: Nat) -> Nat:
  match e:
    case None{}:
      d
    case Some{w}:
      Maybe.default(&2, Nat, w, d)

def reasoning_spec(s: Maybe<&2, Fx.Shape>, e: Maybe<&2, Maybe<&2, Nat>>, +l: Fx.ELv) -> Fx.RFields:
  match s:
    case None{}:
      Fx.RNone{}
    case Some{x}:
      match x:
        case Fx.SClaude{}:
          Fx.RClaude{}
        case Fx.SGpt{}:
          Fx.RNested{reasoning_spec.wire(e, reasoning_spec.gpt(l))}
        case Fx.SGptOss{}:
          Fx.RFlat{Nat.min(4n, reasoning_spec.gpt(l))}

# LAW facts_reasoning_exact: the Bedrock reasoning fields are exactly: none with no shape, Claude's for Claude, GPT's nested effort (the map's wire value, else low at minimal and low, then medium, high, xhigh, max), gpt-oss's flat effort (low at minimal and low, medium, high at high, xhigh and max; the map unread)
# EXCLUDES: a shape read as another; the map read for gpt-oss or ignored for
#   GPT; xhigh or max sent flat; a GPT level collapsed to high; a null entry
#   sent as a wire string
law facts_reasoning_exact:
  for s: Maybe<&2, Fx.Shape>
  for e: Maybe<&2, Maybe<&2, Nat>>
  for +l: Fx.ELv
  {Fx.reasoning(s, e, l) == reasoning_spec(s, e, l) : Fx.RFields}

# LAW facts_reasoning_example: anchor, one per former branch of the Bedrock code: Claude (`anthropic.claude-opus-4-7`); gpt-oss (`openai.gpt-oss-120b`) sends low at minimal and high at xhigh, whatever its map; GPT (`openai.gpt-5.4`) sends xhigh and max as named, its map's string first, the default at a null entry; no shape (`amazon.nova-pro-v1:0`) sends nothing
# EXCLUDES: a spec that is wrong on the cases the old Rust tests pinned
law facts_reasoning_example:
  {Fx.reasoning(Some{Fx.SClaude{}}, None{}, Fx.EHigh{}) == Fx.RClaude{} : Fx.RFields} &
  {Fx.reasoning(Some{Fx.SGptOss{}}, None{}, Fx.EMinimal{}) == Fx.RFlat{2n} : Fx.RFields} &
  {Fx.reasoning(Some{Fx.SGptOss{}}, Some{Some{0n}}, Fx.EXhigh{}) == Fx.RFlat{4n} : Fx.RFields} &
  {Fx.reasoning(Some{Fx.SGpt{}}, None{}, Fx.EXhigh{}) == Fx.RNested{5n} : Fx.RFields} &
  {Fx.reasoning(Some{Fx.SGpt{}}, None{}, Fx.EMax{}) == Fx.RNested{6n} : Fx.RFields} &
  {Fx.reasoning(Some{Fx.SGpt{}}, Some{Some{0n}}, Fx.EHigh{}) == Fx.RNested{0n} : Fx.RFields} &
  {Fx.reasoning(Some{Fx.SGpt{}}, Some{None{}}, Fx.EMinimal{}) == Fx.RNested{2n} : Fx.RFields} &
  {Fx.reasoning(None{}, Some{Some{0n}}, Fx.EHigh{}) == Fx.RNone{} : Fx.RFields} &
  {Fx.shape.old(True{}, True{}, True{}) == Some{Fx.SClaude{}} : Maybe<&2, Fx.Shape>} &
  {Fx.shape.old(False{}, True{}, True{}) == Some{Fx.SGptOss{}} : Maybe<&2, Fx.Shape>}

# LAW facts_bedrock_reasoning_oracle: for every model the old name checks place (a name with "claude",
# "gpt-oss", "gpt-"), the fields of the shape the rulebook gives it are the fields the old code sent
# EXCLUDES: the shape data ordered differently from the old checks (gpt-oss
#   read as GPT, Claude as GPT), the effort tables changed by the move
law facts_bedrock_reasoning_oracle:
  for cl: Bool
  for oss: Bool
  for gpt: Bool
  for e: Maybe<&2, Maybe<&2, Nat>>
  for +l: Fx.ELv
  {Fx.reasoning.old(cl, oss, gpt, e, l) == Fx.reasoning(Fx.shape.old(cl, oss, gpt), e, l) : Fx.RFields}
