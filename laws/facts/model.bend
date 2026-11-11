# eukhe: the laws of area facts, section model: the model and provider facts (S6.10) of bend/facts.bend, the
# output cap, and the model's terms the entry bend/ffi_model_facts.bend calls

import Base
import ../../bend/facts.bend as Fx
import ../../bend/infer.bend as If

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
# tokens stay for the answer
def budgets.fit(+m: Nat, +b: Nat, +a: Nat) -> Fx.Fit:
  Fx.Fit{m, Nat.min(b, Nat.sub(m, a))}

# LAW facts_fit_exact_caller: with the caller's cap x, the thinking ceiling is x plus the budget
# (thinking on top of the answer cap), at most the model's cap, through
# the window; the budget is capped so that the answer keeps a tokens
# EXCLUDES: any other ceiling or budget (the laws above only bound them);
#   thinking taken out of the answer's cap; a budget kept whole that leaves
#   the answer less than its tokens
law facts_fit_exact_caller:
  for +x: Nat
  for +mm: Nat
  for +b: Nat
  for +a: Nat
  for +win: Fx.Win
  {Fx.fit(Some{x}, mm, b, a, win) == budgets.fit(Fx.cap.shrink(Nat.min(Nat.add(x, b), mm), win), b, a) : Fx.Fit}

# LAW facts_fit_exact_model: without the caller's cap, the thinking ceiling is the model's cap,
# through the window
# EXCLUDES: a ceiling below the catalog's max with room to spare
law facts_fit_exact_model:
  for +mm: Nat
  for +b: Nat
  for +a: Nat
  for +win: Fx.Win
  {Fx.fit(None{}, mm, b, a, win) == budgets.fit(Fx.cap.shrink(mm, win), b, a) : Fx.Fit}

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

# LAW facts_fit_ceiling_on_the_cap: the thinking ceiling is the output cap of a request that needs
# its cap, with the thinking ceiling as the caller's cap: one decision
# EXCLUDES: a second window clamp of the thinking ceiling (the double clamp
#   of the Anthropic path), a thinking ceiling that bypasses the cap rule
law facts_fit_ceiling_on_the_cap:
  for base: Maybe<&2, Nat>
  for +mm: Nat
  for +b: Nat
  for +a: Nat
  for +win: Fx.Win
  {Some{Fx.Fit.max(Fx.fit(base, mm, b, a, win))} == Fx.cap(Some{Fx.fit.cap(base, mm, b)}, mm, True{}, win) : Maybe<&2, Nat>}

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

# the cost of base under the tier's multiplier p (in hundredths), in
# hundredths of base: base times the multiplier; with no row, the base
# price (times 100)
def tier_cost_spec(+base: Nat, p: Maybe<&2, Nat>) -> Nat:
  match p:
    case Some{k}:
      Nat.mul(base, k)
    case None{}:
      Nat.mul(base, 100n)

# LAW facts_tier_cost_exact (S6.10.4): the cost under a tier is the base price times the row's multiplier (in hundredths), and the base price (times 100) with no row, for every base and multiplier
# EXCLUDES: a cost that ignores the row's multiplier (tier_cost(base, p) =
#   base * 100, which facts_tier_price_no_row_base lets through), a
#   multiplier read as another, a cost rounded or capped
law facts_tier_cost_exact:
  for +base: Nat
  for p: Maybe<&2, Nat>
  {Fx.tier_cost(base, p) == tier_cost_spec(base, p) : Nat}

# the rate of a 1h cache write, in hundredths: a row's multiplier k (in
# hundredths) of the input rate, floor(input * k / 100); with no row, the
# model's own cache write rate
def rate_1h_spec(row: Maybe<&2, Nat>, +input: Nat, +write: Nat) -> Nat:
  match row:
    case Some{k}:
      Nat.div(Nat.mul(input, k), 100n)
    case None{}:
      write

# LAW facts_cache_write_1h_exact (S6.10.4): a 1h cache write costs a row's multiplier of the input rate, and with no row the model's own cache write rate, for every row, input rate and write rate
# EXCLUDES: a row's multiplier ignored (the write rate, or the input rate,
#   whatever the row), a multiplier applied to the write rate instead of
#   the input rate, a rate not scaled back from hundredths
law facts_cache_write_1h_exact:
  for row: Maybe<&2, Nat>
  for +input: Nat
  for +write: Nat
  {Fx.rate_1h(row, input, write) == rate_1h_spec(row, input, write) : Nat}

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

# (S6.10.5) The Bedrock reasoning fields are the rulebook's shape
# ----------------------------------------------------------------
# Rust reads the rulebook's `bedrock_reasoning` (the shape a family of
# rulebook.json names: `claude`, `gpt`) and the map's entry of the level;
# the model decides the fields (effort mode sends `reasoning.effort`,
# every other reasoning model Anthropic's thinking block). The model's
# terms, independently: a level's rank (minimal 0 .. max 5); GPT sends the
# map's wire value, else the larger of low (2) and the rank plus one; a
# model of no shape or of Claude's sends the thinking block.

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

def reasoning_spec.shaped(x: Fx.Shape, e: Maybe<&2, Maybe<&2, Nat>>, +l: Fx.ELv) -> Fx.RFields:
  match x:
    case Fx.SGpt{}:
      Fx.RNested{reasoning_spec.wire(e, reasoning_spec.gpt(l))}
    case Fx.SClaude{}:
      Fx.RThinking{}

def reasoning_spec(s: Maybe<&2, Fx.Shape>, e: Maybe<&2, Maybe<&2, Nat>>, +l: Fx.ELv) -> Fx.RFields:
  match s:
    case Some{x}:
      reasoning_spec.shaped(x, e, l)
    case None{}:
      Fx.RThinking{}

# LAW facts_reasoning_exact: the Bedrock reasoning fields are exactly: GPT's nested effort (the map's wire value, else low at minimal and low, then medium, high, xhigh, max); Anthropic's thinking block for Claude and for a model of no shape
# EXCLUDES: a shape read as another; the map ignored for GPT; a GPT level
#   collapsed to high; a null entry sent as a wire string; a reasoning
#   model of no shape sent no reasoning field
law facts_reasoning_exact:
  for s: Maybe<&2, Fx.Shape>
  for e: Maybe<&2, Maybe<&2, Nat>>
  for +l: Fx.ELv
  {Fx.reasoning(s, e, l) == reasoning_spec(s, e, l) : Fx.RFields}

# LAW facts_reasoning_example: anchor: Claude (`anthropic.claude-opus-4-7`) sends the thinking block; GPT (`openai.gpt-5.4`) sends xhigh and max as named, its map's string first, the default at a null entry; no shape (`amazon.nova-2-lite-v1:0`, `openai.gpt-oss-120b-1:0`) sends the thinking block
# EXCLUDES: a spec that is wrong on the cases the Rust tests pin
law facts_reasoning_example:
  {Fx.reasoning(Some{Fx.SClaude{}}, None{}, Fx.EHigh{}) == Fx.RThinking{} : Fx.RFields} &
  {Fx.reasoning(Some{Fx.SGpt{}}, None{}, Fx.EXhigh{}) == Fx.RNested{5n} : Fx.RFields} &
  {Fx.reasoning(Some{Fx.SGpt{}}, None{}, Fx.EMax{}) == Fx.RNested{6n} : Fx.RFields} &
  {Fx.reasoning(Some{Fx.SGpt{}}, Some{Some{0n}}, Fx.EHigh{}) == Fx.RNested{0n} : Fx.RFields} &
  {Fx.reasoning(Some{Fx.SGpt{}}, Some{None{}}, Fx.EMinimal{}) == Fx.RNested{2n} : Fx.RFields} &
  {Fx.reasoning(None{}, Some{Some{0n}}, Fx.EMinimal{}) == Fx.RThinking{} : Fx.RFields}
