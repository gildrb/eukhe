# proof_facts: proofs of laws/model_facts.bend (the model in
# bend/facts.bend). PROOF.bend proves each law as ModelFacts.<law> with the
# pf.<law> of this file. The rulebook laws reuse the lookup lemmas of
# bend/proof_quirks.bend.

import Base
import ./infer.bend as If
import ./facts.bend as Fx
import ./proof_quirks.bend as Q

# Nat order
# ---------

def pf.le_refl(+n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pf.le_refl(p)

def pf.le_succ(+n: Nat) -> {Nat.is_le(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pf.le_succ(p)

# a not below b: b is at most a
def pf.not_lt_le(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Q.pq.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pf.not_lt_le(p, q, h)

# a not at most b: b is at most a
def pf.not_le_le(+a: Nat, +b: Nat, h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Q.pq.absurd({Nat.is_le(0n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      Q.pq.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pf.not_le_le(p, q, h)

# a below b and b at most a cannot both hold
def pf.lt_le_absurd(-A: Type, +a: Nat, +b: Nat, h1: {Nat.is_lt(a, b) == True{} : Bool}, h2: {Nat.is_le(b, a) == True{} : Bool}) -> A:
  match a b:
    case 0n 0n:
      Q.pq.absurdF(A, h1)
    case 0n 1n+q:
      Q.pq.absurdF(A, h2)
    case 1n+p 0n:
      Q.pq.absurdF(A, h1)
    case 1n+p 1n+q:
      pf.lt_le_absurd(A, p, q, h1, h2)

def pf.le_trans(+a: Nat, +b: Nat, +c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n b c:
      Q.pq.le0(c)
    case 1n+p 0n c:
      Q.pq.absurdF({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      Q.pq.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      pf.le_trans(p, q, r, ab, bc)

def pf.min_le_r(+x: Nat, +y: Nat) -> {Nat.is_le(Nat.min(x, y), y) == True{} : Bool}:
  match x y:
    case 0n y:
      Q.pq.le0(y)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pf.min_le_r(p, q)

def pf.sub_le(+m: Nat, +a: Nat) -> {Nat.is_le(Nat.sub(m, a), m) == True{} : Bool}:
  match m a:
    case 0n a:
      {==}
    case 1n+p 0n:
      pf.le_refl(1n+p)
    case 1n+p 1n+q:
      pf.le_trans(Nat.sub(p, q), p, 1n+p, pf.sub_le(p, q), pf.le_succ(p))

def pf.add_zero(+n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %pf.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def pf.add_succ(+x: Nat, +q: Nat) -> {Nat.add(x, 1n+q) == 1n+Nat.add(x, q) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %pf.add_succ(p, q) : {1n+Nat.add(p, 1n+q) == 1n+_ : Nat}
      {==}

# (m - a) + a is m when a is at most m
def pf.sub_add(+m: Nat, +a: Nat, h: {Nat.is_le(a, m) == True{} : Bool}) -> {Nat.add(Nat.sub(m, a), a) == m : Nat}:
  match m a:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Q.pq.absurdF({Nat.add(Nat.sub(0n, 1n+q), 1n+q) == 0n : Nat}, h)
    case 1n+p 0n:
      pf.add_zero(1n+p)
    case 1n+p 1n+q:
      %Equal.sym(Nat, Nat.add(Nat.sub(p, q), 1n+q), 1n+Nat.add(Nat.sub(p, q), q), pf.add_succ(Nat.sub(p, q), q)) : {_ == 1n+p : Nat}
      %pf.sub_add(p, q, h) : {1n+Nat.add(Nat.sub(p, q), q) == 1n+_ : Nat}
      {==}

def pf.le_add(+y: Nat, +a: Nat) -> {Nat.is_le(a, Nat.add(y, a)) == True{} : Bool}:
  match y:
    case 0n:
      pf.le_refl(a)
    case 1n+q:
      pf.le_trans(a, Nat.add(q, a), 1n+Nat.add(q, a), pf.le_add(q, a), pf.le_succ(Nat.add(q, a)))

def pf.le_add_mono(+x: Nat, +y: Nat, +a: Nat, h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.add(x, a), Nat.add(y, a)) == True{} : Bool}:
  match x y:
    case 0n y:
      pf.le_add(y, a)
    case 1n+p 0n:
      Q.pq.absurdF({Nat.is_le(Nat.add(1n+p, a), Nat.add(0n, a)) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pf.le_add_mono(p, q, a, h)

def pf.sub_zero(+a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pf.add_sub(+b: Nat, +a: Nat) -> {Nat.sub(Nat.add(b, a), b) == a : Nat}:
  match b:
    case 0n:
      pf.sub_zero(a)
    case 1n+p:
      pf.add_sub(p, a)

# Decisions from the rulebook
# ---------------------------

def pf.facts_rulebook_decides(+known: List<&2, Nat>, +pre: List<&2, If.Rule>, +r: If.Rule, +post: List<&2, If.Rule>, +q: If.Query, dflt: Bool, ok: {If.compiles(known, List.append(&2, If.Rule, pre, r <> post)) == True{} : Bool}, hit: {If.applies(q, r) == True{} : Bool}, top: {If.any_at(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r), 1n+If.Rule.rank(r)) == False{} : Bool}) -> {Fx.decide(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r), dflt) == Nat.is_eq(If.Rule.val(r), 1n) : Bool}:
  +L = List.append(&2, If.Rule, pre, r <> post)
  +D = If.Rule.dir(r)
  +V = If.Rule.val(r)
  %Equal.sym(If.Ans, If.lookup(L, q, D), If.Known{V}, Q.pq.quirk_highest_wins(known, pre, r, post, q, ok, hit, top)) : {Fx.flag(_, dflt) == Nat.is_eq(V, 1n) : Bool}
  {==}

def pf.facts_rulebook_default(+rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, dflt: Bool, none: {If.any_at(rs, q, d, 0n) == False{} : Bool}) -> {Fx.decide(rs, q, d, dflt) == dflt : Bool}:
  %Equal.sym(If.Ans, If.lookup(rs, q, d), If.Unknown{}, Q.pq.quirk_unknown_when_none(rs, q, d, none)) : {Fx.flag(_, dflt) == dflt : Bool}
  {==}

def pf.facts_only_the_rulebook_decides(+rs: List<&2, If.Rule>, +q1: If.Query, +q2: If.Query, +d: Nat, dflt: Bool, same: {If.lookup(rs, q1, d) == If.lookup(rs, q2, d) : If.Ans}) -> {Fx.decide(rs, q1, d, dflt) == Fx.decide(rs, q2, d, dflt) : Bool}:
  %same : {Fx.flag(If.lookup(rs, q1, d), dflt) == Fx.flag(_, dflt) : Bool}
  {==}

def pf.facts_adaptive_compat_first(b: Bool, a: If.Ans) -> {Fx.adaptive(Some{b}, a) == b : Bool}:
  {==}

def pf.facts_adaptive_rulebook_second(a: If.Ans) -> {Fx.adaptive(None{}, a) == Fx.flag(a, False{}) : Bool}:
  {==}

# Budgets
# -------

def pf.hi_le(+x: Nat, +hi: Nat, g: Bool, eg: {Nat.is_lt(hi, x) == g : Bool}) -> {Nat.is_le(Fx.clamp.hi(g, x, hi), hi) == True{} : Bool}:
  match g:
    case True{}:
      pf.le_refl(hi)
    case False{}:
      pf.not_lt_le(hi, x, eg)

def pf.lo_le(+x: Nat, +lo: Nat, +hi: Nat, c: Bool, lohi: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Nat.is_le(Fx.clamp.lo(c, x, lo, hi), hi) == True{} : Bool}:
  match c:
    case True{}:
      lohi
    case False{}:
      pf.hi_le(x, hi, Nat.is_lt(hi, x), {==})

def pf.clamp_le(+x: Nat, +lo: Nat, +hi: Nat, lohi: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Nat.is_le(Fx.clamp(x, lo, hi), hi) == True{} : Bool}:
  pf.lo_le(x, lo, hi, Nat.is_lt(x, lo), lohi)

def pf.hi_ge(+x: Nat, +lo: Nat, +hi: Nat, g: Bool, lohi: {Nat.is_le(lo, hi) == True{} : Bool}, lox: {Nat.is_le(lo, x) == True{} : Bool}) -> {Nat.is_le(lo, Fx.clamp.hi(g, x, hi)) == True{} : Bool}:
  match g:
    case True{}:
      lohi
    case False{}:
      lox

def pf.lo_ge(+x: Nat, +lo: Nat, +hi: Nat, c: Bool, ec: {Nat.is_lt(x, lo) == c : Bool}, lohi: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Nat.is_le(lo, Fx.clamp.lo(c, x, lo, hi)) == True{} : Bool}:
  match c:
    case True{}:
      pf.le_refl(lo)
    case False{}:
      pf.hi_ge(x, lo, hi, Nat.is_lt(hi, x), lohi, pf.not_lt_le(x, lo, ec))

def pf.clamp_ge(+x: Nat, +lo: Nat, +hi: Nat, lohi: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Nat.is_le(lo, Fx.clamp(x, lo, hi)) == True{} : Bool}:
  pf.lo_ge(x, lo, hi, Nat.is_lt(x, lo), {==}, lohi)

def pf.hi_id(+x: Nat, +hi: Nat, g: Bool, eg: {Nat.is_lt(hi, x) == g : Bool}, xhi: {Nat.is_le(x, hi) == True{} : Bool}) -> {Fx.clamp.hi(g, x, hi) == x : Nat}:
  match g:
    case True{}:
      pf.lt_le_absurd({hi == x : Nat}, hi, x, eg, xhi)
    case False{}:
      {==}

def pf.lo_id(+x: Nat, +lo: Nat, +hi: Nat, c: Bool, ec: {Nat.is_lt(x, lo) == c : Bool}, lox: {Nat.is_le(lo, x) == True{} : Bool}, xhi: {Nat.is_le(x, hi) == True{} : Bool}) -> {Fx.clamp.lo(c, x, lo, hi) == x : Nat}:
  match c:
    case True{}:
      pf.lt_le_absurd({lo == x : Nat}, x, lo, ec, lox)
    case False{}:
      pf.hi_id(x, hi, Nat.is_lt(hi, x), {==}, xhi)

# a value inside lo..hi stays as it is
def pf.clamp_id(+x: Nat, +lo: Nat, +hi: Nat, lox: {Nat.is_le(lo, x) == True{} : Bool}, xhi: {Nat.is_le(x, hi) == True{} : Bool}) -> {Fx.clamp(x, lo, hi) == x : Nat}:
  pf.lo_id(x, lo, hi, Nat.is_lt(x, lo), {==}, lox, xhi)

# the minimal budget of an ordered rule is at most its high budget
def pf.ord_mh(+b: Fx.Budgets, +ordered: {Fx.Budgets.ordered(b) == True{} : Bool}) -> {Nat.is_le(Fx.Budgets.minimal(b), Fx.Budgets.high(b)) == True{} : Bool}:
  match b:
    case Fx.Budgets{+mi, +lo, +me, +hi}:
      +ml = Q.pq.and_l(Nat.is_le(mi, lo), Bool.and(Nat.is_le(lo, me), Nat.is_le(me, hi)), ordered)
      +rest = Q.pq.and_r(Nat.is_le(mi, lo), Bool.and(Nat.is_le(lo, me), Nat.is_le(me, hi)), ordered)
      +lm = Q.pq.and_l(Nat.is_le(lo, me), Nat.is_le(me, hi), rest)
      +mh = Q.pq.and_r(Nat.is_le(lo, me), Nat.is_le(me, hi), rest)
      pf.le_trans(mi, lo, hi, ml, pf.le_trans(lo, me, hi, lm, mh))

def pf.facts_google_budget_at_most_high(+b: Fx.Budgets, c: Fx.Customs, +l: Fx.Lv, +ordered: {Fx.Budgets.ordered(b) == True{} : Bool}) -> {Nat.is_le(Fx.gtokens(b, c, l), Fx.Budgets.high(b)) == True{} : Bool}:
  pf.clamp_le(Maybe.default(&2, Nat, Fx.Customs.at(c, l), Fx.Budgets.at(b, l)), Fx.Budgets.minimal(b), Fx.Budgets.high(b), pf.ord_mh(b, ordered))

def pf.facts_google_budget_at_least_minimal(+b: Fx.Budgets, c: Fx.Customs, +l: Fx.Lv, +ordered: {Fx.Budgets.ordered(b) == True{} : Bool}) -> {Nat.is_le(Fx.Budgets.minimal(b), Fx.gtokens(b, c, l)) == True{} : Bool}:
  pf.clamp_ge(Maybe.default(&2, Nat, Fx.Customs.at(c, l), Fx.Budgets.at(b, l)), Fx.Budgets.minimal(b), Fx.Budgets.high(b), pf.ord_mh(b, ordered))

def pf.table_at(+mi: Nat, +lo: Nat, +me: Nat, +hi: Nat, l: Fx.Lv, ml: {Nat.is_le(mi, lo) == True{} : Bool}, lm: {Nat.is_le(lo, me) == True{} : Bool}, mh: {Nat.is_le(me, hi) == True{} : Bool}) -> {Fx.gtokens(Fx.Budgets{mi, lo, me, hi}, Fx.Customs.none(), l) == Fx.Budgets.at(Fx.Budgets{mi, lo, me, hi}, l) : Nat}:
  match l:
    case Fx.Minimal{}:
      pf.clamp_id(mi, mi, hi, pf.le_refl(mi), pf.le_trans(mi, lo, hi, ml, pf.le_trans(lo, me, hi, lm, mh)))
    case Fx.Low{}:
      pf.clamp_id(lo, mi, hi, ml, pf.le_trans(lo, me, hi, lm, mh))
    case Fx.Medium{}:
      pf.clamp_id(me, mi, hi, pf.le_trans(mi, lo, me, ml, lm), mh)
    case Fx.High{}:
      pf.clamp_id(hi, mi, hi, pf.le_trans(mi, lo, hi, ml, pf.le_trans(lo, me, hi, lm, mh)), pf.le_refl(hi))

def pf.facts_google_rule_is_the_table(+b: Fx.Budgets, +l: Fx.Lv, +ordered: {Fx.Budgets.ordered(b) == True{} : Bool}) -> {Fx.gtokens(b, Fx.Customs.none(), l) == Fx.Budgets.at(b, l) : Nat}:
  match b:
    case Fx.Budgets{+mi, +lo, +me, +hi}:
      +rest = Q.pq.and_r(Nat.is_le(mi, lo), Bool.and(Nat.is_le(lo, me), Nat.is_le(me, hi)), ordered)
      pf.table_at(mi, lo, me, hi, l, Q.pq.and_l(Nat.is_le(mi, lo), Bool.and(Nat.is_le(lo, me), Nat.is_le(me, hi)), ordered), Q.pq.and_l(Nat.is_le(lo, me), Nat.is_le(me, hi), rest), Q.pq.and_r(Nat.is_le(lo, me), Nat.is_le(me, hi), rest))

def pf.fit_at_le(+m: Nat, +b: Nat, +a: Nat, c: Bool, ec: {Nat.is_le(m, b) == c : Bool}) -> {Nat.is_le(Fx.Fit.budget(Fx.fit.at(c, m, b, a)), Fx.Fit.max(Fx.fit.at(c, m, b, a))) == True{} : Bool}:
  match c:
    case True{}:
      pf.le_trans(Nat.min(b, Nat.sub(m, a)), Nat.sub(m, a), m, pf.min_le_r(b, Nat.sub(m, a)), pf.sub_le(m, a))
    case False{}:
      pf.not_le_le(m, b, ec)

def pf.facts_fit_budget_under_ceiling(+base: Maybe<&2, Nat>, +mm: Nat, +b: Nat, +a: Nat) -> {Nat.is_le(Fx.Fit.budget(Fx.fit(base, mm, b, a)), Fx.Fit.max(Fx.fit(base, mm, b, a))) == True{} : Bool}:
  +m = Fx.fit.cap(base, mm, b)
  pf.fit_at_le(m, b, a, Nat.is_le(m, b), {==})

def pf.fit_at_max(+m: Nat, +b: Nat, +a: Nat, c: Bool) -> {Fx.Fit.max(Fx.fit.at(c, m, b, a)) == m : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def pf.cap_le(+base: Maybe<&2, Nat>, +mm: Nat, +b: Nat) -> {Nat.is_le(Fx.fit.cap(base, mm, b), mm) == True{} : Bool}:
  match base:
    case None{}:
      pf.le_refl(mm)
    case Some{x}:
      pf.min_le_r(Nat.add(x, b), mm)

def pf.facts_fit_ceiling_under_model(+base: Maybe<&2, Nat>, +mm: Nat, +b: Nat, +a: Nat) -> {Nat.is_le(Fx.Fit.max(Fx.fit(base, mm, b, a)), mm) == True{} : Bool}:
  +m = Fx.fit.cap(base, mm, b)
  +c = Nat.is_le(m, b)
  %Equal.sym(Nat, Fx.Fit.max(Fx.fit.at(c, m, b, a)), m, pf.fit_at_max(m, b, a, c)) : {Nat.is_le(_, mm) == True{} : Bool}
  pf.cap_le(base, mm, b)

def pf.facts_room_leaves_the_answer(+b: Nat, +m: Nat, +a: Nat, fits: {Nat.is_le(a, m) == True{} : Bool}) -> {Nat.is_le(Nat.add(Fx.room(b, m, a), a), m) == True{} : Bool}:
  +R = Nat.min(b, Nat.sub(m, a))
  %pf.sub_add(m, a, fits) : {Nat.is_le(Nat.add(R, a), _) == True{} : Bool}
  pf.le_add_mono(R, Nat.sub(m, a), a, pf.min_le_r(b, Nat.sub(m, a)))

def pf.facts_aux_cap_answer_room(+b: Nat, +a: Nat) -> {Nat.sub(Fx.aux_cap(b, a), b) == a : Nat}:
  pf.add_sub(b, a)

# Oracles
# -------

# a native-xhigh model whose map keeps the promise sends xhigh at xhigh
def pf.xhigh(+m: Fx.EMap, ok: {Fx.native_ok.e(Fx.EMap.at(m, Fx.EXhigh{})) == True{} : Bool}) -> {5n == Fx.effort(m, Fx.EXhigh{}) : Nat}:
  match m:
    case Fx.EMap{mi, lo, me, hi, xh, mx}:
      match xh:
        case None{}:
          Q.pq.absurdF({5n == Fx.effort.default(Fx.EXhigh{}) : Nat}, ok)
        case Some{w}:
          match w:
            case None{}:
              Q.pq.absurdF({5n == Fx.effort.default(Fx.EXhigh{}) : Nat}, ok)
            case Some{v}:
              Equal.sym(Nat, v, 5n, Q.pq.eq_true(v, 5n, ok))

def pf.facts_bedrock_effort_oracle(native: Bool, +m: Fx.EMap, +l: Fx.ELv, ok: {Fx.native_ok(native, m) == True{} : Bool}) -> {Fx.effort.old(native, m, l) == Fx.effort(m, l) : Nat}:
  match native:
    case False{}:
      {==}
    case True{}:
      match l:
        case Fx.EMinimal{}:
          {==}
        case Fx.ELow{}:
          {==}
        case Fx.EMedium{}:
          {==}
        case Fx.EHigh{}:
          {==}
        case Fx.EMax{}:
          {==}
        case Fx.EXhigh{}:
          pf.xhigh(m, ok)

def pf.facts_bedrock_budget_oracle(c: Fx.Customs, +l: Fx.Lv) -> {Fx.budget(c, Fx.budgets.shipped(), l) == Fx.budget.old(c, l) : Nat}:
  match l:
    case Fx.Minimal{}:
      {==}
    case Fx.Low{}:
      {==}
    case Fx.Medium{}:
      {==}
    case Fx.High{}:
      {==}

# Prices
# ------

def pf.facts_tier_price_model_row_first(+rows: List<&2, Fx.PRow>, +m: Nat, +t: Nat, +k: Nat, hit: {Fx.price.find(rows, m, t, True{}) == Some{k} : Maybe<&2, Nat>}) -> {Fx.price(rows, m, t) == Some{k} : Maybe<&2, Nat>}:
  %Equal.sym(Maybe<&2, Nat>, Fx.price.find(rows, m, t, True{}), Some{k}, hit) : {Fx.price.or(_, Fx.price.find(rows, m, t, False{})) == Some{k} : Maybe<&2, Nat>}
  {==}

def pf.facts_tier_price_no_row_base(+rows: List<&2, Fx.PRow>, +m: Nat, +t: Nat, +base: Nat, none: {Fx.price(rows, m, t) == None{} : Maybe<&2, Nat>}) -> {Fx.tier_cost(base, Fx.price(rows, m, t)) == Nat.mul(base, 100n) : Nat}:
  %Equal.sym(Maybe<&2, Nat>, Fx.price(rows, m, t), None{}, none) : {Fx.tier_cost(base, _) == Nat.mul(base, 100n) : Nat}
  {==}

def pf.facts_tier_price_openai_oracle(m: Nat, t: Nat) -> {Maybe.default(&2, Nat, Fx.price(Fx.prices.openai(), m, t), 100n) == Fx.price.old.openai(m, t) : Nat}:
  match m t:
    case 0n 0n:
      {==}
    case 0n 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+c:
              match c:
                case 0n:
                  {==}
                case 1n+d:
                  {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+c:
              match c:
                case 0n:
                  {==}
                case 1n+d:
                  {==}

def pf.facts_tier_price_codex_oracle(m: Nat, t: Nat) -> {Maybe.default(&2, Nat, Fx.price(Fx.prices.codex(), m, t), 100n) == Fx.price.old.codex(m, t) : Nat}:
  match m t:
    case 0n 0n:
      {==}
    case 0n 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+c:
              {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+c:
              {==}

def pf.facts_cache_write_1h_own_rate(+input: Nat, +write: Nat) -> {Fx.rate_1h(None{}, input, write) == write : Nat}:
  {==}
