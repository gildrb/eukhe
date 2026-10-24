# facts: the model of the model and provider facts that live in data, not
# in code (docs/inference.md S6.10). laws/facts.bend states its laws;
# proof/facts/ proves them. Sections 1 to 4 run as the compiled core:
# bend/ffi_facts.bend (the budgets) and bend/ffi_model_facts.bend (the
# flags, adaptive thinking, the Bedrock effort, the tier price row).
#
# 1. Decisions from the rulebook: a wire API reads a fact of a model (adaptive
#    thinking, block binding, prompt caching, explicit cache breakpoints, the
#    Google thinking format) as the quirks rulebook's answer for one
#    directive; no other input than that answer, the model's explicit compat
#    flag and the user's setting reaches the decision.
# 2. Thinking budgets: the budget of a level, the Google budget held inside
#    the model's range (an unordered budget rule is refused, never
#    clamped), the fit of a budget under the response ceiling, and the
#    answer room of an auxiliary call. The Rust caller saturates every
#    budget, cap and size at the wire's largest Nat (10^14-1, below the
#    runtime's 2^48-1) before the call; no def here forms a value above
#    its inputs or above `top`, so a run never meets the runtime's Nat
#    bound and every answer fits the wire.
# 3. Oracles: the code that held the facts before, as functions, for the
#    laws that say the data gives the same answers.

import Base
import ./infer.bend as If

# 1. Decisions from the rulebook
# ------------------------------

# a flag directive's decision: a known value 1 is true, any other known
# value false; Unknown (no rule applies) takes the wire API's default
def flag(a: If.Ans, dflt: Bool) -> Bool:
  match a:
    case If.Known{v}:
      Nat.is_eq(v, 1n)
    case If.Unknown{}:
      dflt

# the decision of the rulebook rs for query q and directive d
def decide(+rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, dflt: Bool) -> Bool:
  flag(If.lookup(rs, q, d), dflt)

# adaptive thinking, one rule for Anthropic Messages and Bedrock: the
# model's explicit compat flag, else the rulebook's answer, else false
def adaptive(compat: Maybe<&2, Bool>, a: If.Ans) -> Bool:
  match compat:
    case Some{b}:
      b
    case None{}:
      flag(a, False{})

# 2. Thinking budgets
# -------------------

# the four budget levels (xhigh and max take high)
type Lv is Data:
  Minimal{}
  Low{}
  Medium{}
  High{}

# a budget per level (the rulebook's `thinking_defaults.budgets`, or a
# model's `thinking_budgets` rule)
type Budgets is Data:
  Budgets{minimal: Nat, low: Nat, medium: Nat, high: Nat}

def Budgets.at(b: Budgets, l: Lv) -> Nat:
  match b:
    case Budgets{mi, lo, me, hi}:
      match l:
        case Minimal{}:
          mi
        case Low{}:
          lo
        case Medium{}:
          me
        case High{}:
          hi

def Budgets.minimal(b: Budgets) -> Nat:
  match b:
    case Budgets{mi, lo, me, hi}:
      mi

def Budgets.high(b: Budgets) -> Nat:
  match b:
    case Budgets{mi, lo, me, hi}:
      hi

# each level at least the one before it: the shape a rule must have
def Budgets.ordered(b: Budgets) -> Bool:
  match b:
    case Budgets{+mi, +lo, +me, +hi}:
      Bool.and(Nat.is_le(mi, lo), Bool.and(Nat.is_le(lo, me), Nat.is_le(me, hi)))

# the user's `thinkingBudgets`: a budget or none per level
type Customs is Data:
  Customs{minimal: Maybe<&2, Nat>, low: Maybe<&2, Nat>, medium: Maybe<&2, Nat>, high: Maybe<&2, Nat>}

def Customs.at(c: Customs, l: Lv) -> Maybe<&2, Nat>:
  match c:
    case Customs{mi, lo, me, hi}:
      match l:
        case Minimal{}:
          mi
        case Low{}:
          lo
        case Medium{}:
          me
        case High{}:
          hi

def Customs.none() -> Customs:
  Customs{None{}, None{}, None{}, None{}}

# a request's level (`ThinkingLevel`): the ladder without off; the
# Bedrock effort of section 3 reads it too
type ELv is Data:
  EMinimal{}
  ELow{}
  EMedium{}
  EHigh{}
  EXhigh{}
  EMax{}

# the budget level of a request's level (`clamp_reasoning`): xhigh and max
# take high
def Lv.of(l: ELv) -> Lv:
  match l:
    case EMinimal{}:
      Minimal{}
    case ELow{}:
      Low{}
    case EMedium{}:
      Medium{}
    case EHigh{}:
      High{}
    case EXhigh{}:
      High{}
    case EMax{}:
      High{}

# the budget of level l (`thinking_budget_for_level`): the user's budget,
# else the default budget
def budget(c: Customs, d: Budgets, +l: Lv) -> Nat:
  Maybe.default(&2, Nat, Customs.at(c, l), Budgets.at(d, l))

# x held inside lo..hi (Rust `u64::clamp`); lt is x < lo, gt is hi < x
def clamp.hi(gt: Bool, x: Nat, hi: Nat) -> Nat:
  match gt:
    case True{}:
      hi
    case False{}:
      x

def clamp.lo(lt: Bool, +x: Nat, lo: Nat, +hi: Nat) -> Nat:
  match lt:
    case True{}:
      lo
    case False{}:
      clamp.hi(Nat.is_lt(hi, x), x, hi)

def clamp(+x: Nat, +lo: Nat, +hi: Nat) -> Nat:
  clamp.lo(Nat.is_lt(x, lo), x, lo, hi)

# a Google `thinkingBudget`: dynamic (-1, the server decides) or tokens;
# a budget rule that is not ordered has no range to hold a budget in
type GB is Data:
  Dynamic{}
  Tokens{n: Nat}
  Unordered{}

# the Google budget of a model with the rule b: the user's budget, else
# the rule's, held inside the rule's minimal..high
def gtokens(+b: Budgets, c: Customs, +l: Lv) -> Nat:
  clamp(Maybe.default(&2, Nat, Customs.at(c, l), Budgets.at(b, l)), Budgets.minimal(b), Budgets.high(b))

def gbudget.free(m: Maybe<&2, Nat>) -> GB:
  match m:
    case Some{n}:
      Tokens{n}
    case None{}:
      Dynamic{}

# ok is Budgets.ordered(b)
def gbudget.rule(ok: Bool, +b: Budgets, c: Customs, +l: Lv) -> GB:
  match ok:
    case True{}:
      Tokens{gtokens(b, c, l)}
    case False{}:
      Unordered{}

# the Google budget of level l (`google_thinking_budget`): with an ordered
# rule, gtokens; with an unordered one, Unordered; without one, the user's
# budget, else dynamic
def gbudget(rule: Maybe<&2, Budgets>, c: Customs, l: Lv) -> GB:
  match rule:
    case Some{+b}:
      gbudget.rule(Budgets.ordered(b), b, c, l)
    case None{}:
      gbudget.free(Customs.at(c, l))

# a response ceiling and the thinking budget under it
type Fit is Data:
  Fit{max: Nat, budget: Nat}

def Fit.max(f: Fit) -> Nat:
  match f:
    case Fit{m, b}:
      m

def Fit.budget(f: Fit) -> Nat:
  match f:
    case Fit{m, b}:
      b

# the budget b capped so that a tokens stay for the answer under the
# ceiling m (`clamp_thinking_budget_to_answer_room`)
def room(+b: Nat, +m: Nat, +a: Nat) -> Nat:
  Nat.min(b, Nat.sub(m, a))

# the caller's cap x plus the budget b, else mm; lt is b < mm - x, so the
# sum is formed only below mm
def fit.cap.add(lt: Bool, +x: Nat, +mm: Nat, +b: Nat) -> Nat:
  match lt:
    case True{}:
      Nat.add(x, b)
    case False{}:
      mm

# the ceiling: the caller's cap plus the budget, else the model's cap,
# never above the model's cap mm
def fit.cap(base: Maybe<&2, Nat>, +mm: Nat, +b: Nat) -> Nat:
  match base:
    case None{}:
      mm
    case Some{+x}:
      fit.cap.add(Nat.is_lt(b, Nat.sub(mm, x)), x, mm, b)

# over is m <= b: the budget fills the ceiling, so it gives room
def fit.at(over: Bool, +m: Nat, +b: Nat, +a: Nat) -> Fit:
  match over:
    case True{}:
      Fit{m, room(b, m, a)}
    case False{}:
      Fit{m, b}

# the budget b fitted under the ceiling (`adjust_max_tokens_for_thinking`),
# a tokens kept for the answer when the budget fills the ceiling
def fit(base: Maybe<&2, Nat>, +mm: Nat, +b: Nat, +a: Nat) -> Fit:
  +m = fit.cap(base, mm, b)
  fit.at(Nat.is_le(m, b), m, b, a)

# the budget of a request's level l fitted under the ceiling
# (`adjust_max_tokens_for_thinking`): the user's budgets c, the default
# budgets d, the answer's tokens a
def adjust(base: Maybe<&2, Nat>, +mm: Nat, l: ELv, c: Customs, d: Budgets, +a: Nat) -> Fit:
  fit(base, mm, budget(c, d, Lv.of(l)), a)

# an auxiliary call's output cap: the thinking budget plus the answer
# (`thinking_output_cap`)
def aux_cap(+b: Nat, +a: Nat) -> Nat:
  Nat.add(b, a)

# the cap b + a, at most top; lt is b < top - a, so the sum is formed only
# below top
def aux_cap.add(lt: Bool, +b: Nat, +a: Nat, +top: Nat) -> Nat:
  match lt:
    case True{}:
      Nat.add(b, a)
    case False{}:
      top

def aux_cap.within(+b: Nat, +a: Nat, +top: Nat) -> Nat:
  aux_cap.add(Nat.is_lt(b, Nat.sub(top, a)), b, a, top)

# the compactor's output cap (`thinking_output_cap` of the high budget):
# the high budget of the user's budgets c, else of the defaults d, plus
# the answer's tokens a, at most top
def aux(c: Customs, d: Budgets, +a: Nat, +top: Nat) -> Nat:
  aux_cap.within(budget(c, d, High{}), a, top)

# 3. Oracles
# ----------

# Bedrock effort. A wire value is a number: 2 low, 3 medium, 4 high, 5
# xhigh. A thinking-level map entry is missing (None), null (Some{None}) or
# a wire value (Some{Some{w}}); the level is an ELv (section 2).
type EMap is Data:
  EMap{minimal: Maybe<&2, Maybe<&2, Nat>>, low: Maybe<&2, Maybe<&2, Nat>>, medium: Maybe<&2, Maybe<&2, Nat>>, high: Maybe<&2, Maybe<&2, Nat>>, xhigh: Maybe<&2, Maybe<&2, Nat>>, max: Maybe<&2, Maybe<&2, Nat>>}

def EMap.at(m: EMap, l: ELv) -> Maybe<&2, Maybe<&2, Nat>>:
  match m:
    case EMap{mi, lo, me, hi, xh, mx}:
      match l:
        case EMinimal{}:
          mi
        case ELow{}:
          lo
        case EMedium{}:
          me
        case EHigh{}:
          hi
        case EXhigh{}:
          xh
        case EMax{}:
          mx

# the Bedrock default effort of a level
def effort.default(l: ELv) -> Nat:
  match l:
    case EMinimal{}:
      2n
    case ELow{}:
      2n
    case EMedium{}:
      3n
    case EHigh{}:
      4n
    case EXhigh{}:
      4n
    case EMax{}:
      4n

def effort.of(e: Maybe<&2, Maybe<&2, Nat>>, +l: ELv) -> Nat:
  match e:
    case Some{w}:
      match w:
        case Some{v}:
          v
        case None{}:
          effort.default(l)
    case None{}:
      effort.default(l)

# the effort now (`map_thinking_level_to_effort`): the map's wire value,
# else the default effort
def effort(+m: EMap, +l: ELv) -> Nat:
  effort.of(EMap.at(m, l), l)

def is_xhigh(l: ELv) -> Bool:
  match l:
    case EXhigh{}:
      True{}
    case EMinimal{}:
      False{}
    case ELow{}:
      False{}
    case EMedium{}:
      False{}
    case EHigh{}:
      False{}
    case EMax{}:
      False{}

def effort.old.at(hit: Bool, +m: EMap, +l: ELv) -> Nat:
  match hit:
    case True{}:
      5n
    case False{}:
      effort(m, l)

# the effort before: a model on the native-xhigh id list (native) sends
# xhigh at xhigh before its map is read
def effort.old(native: Bool, +m: EMap, +l: ELv) -> Nat:
  effort.old.at(Bool.and(native, is_xhigh(l)), m, l)

def native_ok.e(e: Maybe<&2, Maybe<&2, Nat>>) -> Bool:
  match e:
    case Some{w}:
      match w:
        case Some{v}:
          Nat.is_eq(v, 5n)
        case None{}:
          False{}
    case None{}:
      False{}

# the catalog's promise for a native-xhigh model: its map sends xhigh at
# xhigh
def native_ok(native: Bool, m: EMap) -> Bool:
  match native:
    case True{}:
      native_ok.e(EMap.at(m, EXhigh{}))
    case False{}:
      True{}

# the budget-based Claude table of the Bedrock code, before the rulebook
# held it (the level is clamped to high already)
def budget.old(c: Customs, l: Lv) -> Nat:
  match l:
    case Minimal{}:
      Maybe.default(&2, Nat, Customs.at(c, Minimal{}), 1024n)
    case Low{}:
      Maybe.default(&2, Nat, Customs.at(c, Low{}), 2048n)
    case Medium{}:
      Maybe.default(&2, Nat, Customs.at(c, Medium{}), 8192n)
    case High{}:
      Maybe.default(&2, Nat, Customs.at(c, High{}), 16384n)

# the shipped default budgets (rulebook.json `thinking_defaults.budgets`)
def budgets.shipped() -> Budgets:
  Budgets{1024n, 2048n, 8192n, 16384n}

# 4. Prices
# ---------

# A service tier price row of one provider and wire API: a model (none:
# every model of the provider), a tier, the multiplier in hundredths. A
# model is a number; the shipped tables name gpt-5.5 as 0. A tier is a
# number: 1 flex, 2 priority, 3 fast, more for every other tier.
type PRow is Data:
  PRow{model: Maybe<&2, Nat>, tier: Nat, mult: Nat}

def PRow.mult(r: PRow) -> Nat:
  match r:
    case PRow{m, t, k}:
      k

def same.model(want: Maybe<&2, Nat>, +m: Nat, exact: Bool) -> Bool:
  match want:
    case Some{x}:
      Bool.and(exact, Nat.is_eq(x, m))
    case None{}:
      Bool.not(exact)

# row r prices tier t for model m: exact, a row of model m; else a row of
# every model
def PRow.hit(r: PRow, +m: Nat, +t: Nat, exact: Bool) -> Bool:
  match r:
    case PRow{want, rt, k}:
      Bool.and(Nat.is_eq(rt, t), same.model(want, m, exact))

def price.pick(hit: Bool, +r: PRow, later: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{PRow.mult(r)}
    case False{}:
      later

# the first row of rows that prices tier t for model m (exact or not)
def price.find(+rows: List<&2, PRow>, +m: Nat, +t: Nat, +exact: Bool) -> Maybe<&2, Nat>:
  match rows:
    case Nil{}:
      None{}
    case r <> rest:
      price.pick(PRow.hit(r, m, t, exact), r, price.find(rest, m, t, exact))

def price.or(first: Maybe<&2, Nat>, later: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match first:
    case Some{k}:
      Some{k}
    case None{}:
      later

# the multiplier of tier t for model m (`service_tier_multiplier`): the row
# of the model, else the row of every model, else none
def price(+rows: List<&2, PRow>, +m: Nat, +t: Nat) -> Maybe<&2, Nat>:
  price.or(price.find(rows, m, t, True{}), price.find(rows, m, t, False{}))

# the cost of base under the multiplier p, in hundredths
# (`apply_service_tier_pricing`): no row leaves the base price
def tier_cost(+base: Nat, p: Maybe<&2, Nat>) -> Nat:
  Nat.mul(base, Maybe.default(&2, Nat, p, 100n))

# the shipped OpenAI rows (openai over openai-responses, and over
# openai-completions)
def prices.openai() -> List<&2, PRow>:
  [PRow{None{}, 1n, 50n}, PRow{None{}, 2n, 200n}, PRow{None{}, 3n, 200n}, PRow{Some{0n}, 2n, 250n}, PRow{Some{0n}, 3n, 250n}]

# the shipped Codex rows (openai-codex over openai-codex-responses)
def prices.codex() -> List<&2, PRow>:
  [PRow{None{}, 1n, 50n}, PRow{None{}, 2n, 200n}, PRow{Some{0n}, 2n, 250n}]

# the priority price before the table: 2.5 for gpt-5.5, else 2.0
def price.old.g(m: Nat) -> Nat:
  match m:
    case 0n:
      250n
    case 1n+p:
      200n

# the OpenAI multiplier before the table: flex 0.5, priority and fast
# 2.0 (2.5 for gpt-5.5), else 1
def price.old.openai(m: Nat, t: Nat) -> Nat:
  match t:
    case 0n:
      100n
    case 1n+a:
      match a:
        case 0n:
          50n
        case 1n+b:
          match b:
            case 0n:
              price.old.g(m)
            case 1n+c:
              match c:
                case 0n:
                  price.old.g(m)
                case 1n+d:
                  100n

# the Codex multiplier before the table: no fast
def price.old.codex(m: Nat, t: Nat) -> Nat:
  match t:
    case 0n:
      100n
    case 1n+a:
      match a:
        case 0n:
          50n
        case 1n+b:
          match b:
            case 0n:
              price.old.g(m)
            case 1n+c:
              100n

# the rate of a 1h cache write, in hundredths: a row's multiplier (in
# hundredths) of the input rate, else the model's own cache write rate
# (`calculate_cost`); never a price borrowed from another provider
def rate_1h(row: Maybe<&2, Nat>, +input: Nat, +write: Nat) -> Nat:
  match row:
    case Some{k}:
      Nat.div(Nat.mul(input, k), 100n)
    case None{}:
      write
