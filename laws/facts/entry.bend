# eukhe: the laws of area facts, section entry: the entry of the compiled
# core for the thinking budgets and the output cap (bend/ffi_facts.bend),
# stated independently of that file and of the model's functions

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_facts.bend as FFx
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase
import ./model.bend as Facts

# LAWS (facts, compiled core): Rust (crates/eukhe-ai `api/simple_options.rs`,
# `api/google_shared/options.rs`; crates/eukhe-core `memory/summarizer.rs`)
# sends one budget request and reads one reply. The law below pins the
# reply to every input from:
#   - a reader of the request grammar (the header of bend/ffi_facts.bend)
#     built only from the wire primitives of bend/wire.bend;
#   - the decisions as the laws of laws/facts/model.bend state them (the user's
#     budget over the default, xhigh and max at high; the room under the
#     ceiling; the fitted ceiling and budget; the Google budget; the aux
#     cap; the output cap), written here with spec terms only;
#   - a speller of the reply built from the wire primitives.

# Reader
# ------

# a Maybe<Nat>: 0 none | 1, then the Nat
def fr.mnat.some(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{Some{n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def fr.mnat.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      fr.mnat.some(Wr.get_nat(s))
    case 2n+p:
      Wr.Bad{}

def fr.mnat(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{t, s}:
      fr.mnat.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# a request's level: 0 minimal .. 5 max
def fr.elv.tag(t: Nat, s: String) -> Wr.Dec<Fx.ELv>:
  match t:
    case 0n:
      Wr.Got{Fx.EMinimal{}, s}
    case 1n:
      Wr.Got{Fx.ELow{}, s}
    case 2n:
      Wr.Got{Fx.EMedium{}, s}
    case 3n:
      Wr.Got{Fx.EHigh{}, s}
    case 4n:
      Wr.Got{Fx.EXhigh{}, s}
    case 5n:
      Wr.Got{Fx.EMax{}, s}
    case 6n+p:
      Wr.Bad{}

def fr.elv(r: Wr.Dec<Nat>) -> Wr.Dec<Fx.ELv>:
  match r:
    case Wr.Got{t, s}:
      fr.elv.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# a budget level: 0 minimal .. 3 high
def fr.lv.tag(t: Nat, s: String) -> Wr.Dec<Fx.Lv>:
  match t:
    case 0n:
      Wr.Got{Fx.Minimal{}, s}
    case 1n:
      Wr.Got{Fx.Low{}, s}
    case 2n:
      Wr.Got{Fx.Medium{}, s}
    case 3n:
      Wr.Got{Fx.High{}, s}
    case 4n+p:
      Wr.Bad{}

def fr.lv(r: Wr.Dec<Nat>) -> Wr.Dec<Fx.Lv>:
  match r:
    case Wr.Got{t, s}:
      fr.lv.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# the user's budgets: four Maybe<Nat>, minimal to high
def fr.customs.hi(mi: Maybe<&2, Nat>, lo: Maybe<&2, Nat>, me: Maybe<&2, Nat>, r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<Fx.Customs>:
  match r:
    case Wr.Got{hi, s}:
      Wr.Got{Fx.Customs{mi, lo, me, hi}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def fr.customs.me(mi: Maybe<&2, Nat>, lo: Maybe<&2, Nat>, r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<Fx.Customs>:
  match r:
    case Wr.Got{me, s}:
      fr.customs.hi(mi, lo, me, fr.mnat(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.customs.lo(mi: Maybe<&2, Nat>, r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<Fx.Customs>:
  match r:
    case Wr.Got{lo, s}:
      fr.customs.me(mi, lo, fr.mnat(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.customs.mi(r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<Fx.Customs>:
  match r:
    case Wr.Got{mi, s}:
      fr.customs.lo(mi, fr.mnat(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.customs(s: String) -> Wr.Dec<Fx.Customs>:
  fr.customs.mi(fr.mnat(Wr.get_nat(s)))

# a budget table: four Nat, minimal to high
def fr.budgets.hi(mi: Nat, lo: Nat, me: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Fx.Budgets>:
  match r:
    case Wr.Got{hi, s}:
      Wr.Got{Fx.Budgets{mi, lo, me, hi}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def fr.budgets.me(mi: Nat, lo: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Fx.Budgets>:
  match r:
    case Wr.Got{me, s}:
      fr.budgets.hi(mi, lo, me, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.budgets.lo(mi: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Fx.Budgets>:
  match r:
    case Wr.Got{lo, s}:
      fr.budgets.me(mi, lo, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.budgets.mi(r: Wr.Dec<Nat>) -> Wr.Dec<Fx.Budgets>:
  match r:
    case Wr.Got{mi, s}:
      fr.budgets.lo(mi, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.budgets(s: String) -> Wr.Dec<Fx.Budgets>:
  fr.budgets.mi(Wr.get_nat(s))

# a Maybe<Budgets>: 0 none | 1, then the table
def fr.mbudgets.some(r: Wr.Dec<Fx.Budgets>) -> Wr.Dec<Maybe<&2, Fx.Budgets>>:
  match r:
    case Wr.Got{b, s}:
      Wr.Got{Some{b}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def fr.mbudgets.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, Fx.Budgets>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      fr.mbudgets.some(fr.budgets(s))
    case 2n+p:
      Wr.Bad{}

def fr.mbudgets(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Fx.Budgets>>:
  match r:
    case Wr.Got{t, s}:
      fr.mbudgets.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# the window facts: the window, the prompt, the safety, the floor (Nat),
# then whether the model stops at the window (a Bool)
def fr.win.st(w: Nat, p: Nat, sf: Nat, f: Nat, r: Wr.Dec<Bool>) -> Wr.Dec<Fx.Win>:
  match r:
    case Wr.Got{st, s}:
      Wr.Got{Fx.Win{w, p, sf, f, st}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def fr.win.f(w: Nat, p: Nat, sf: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Fx.Win>:
  match r:
    case Wr.Got{f, s}:
      fr.win.st(w, p, sf, f, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.win.sf(w: Nat, p: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Fx.Win>:
  match r:
    case Wr.Got{sf, s}:
      fr.win.f(w, p, sf, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.win.p(w: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Fx.Win>:
  match r:
    case Wr.Got{p, s}:
      fr.win.sf(w, p, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.win.w(r: Wr.Dec<Nat>) -> Wr.Dec<Fx.Win>:
  match r:
    case Wr.Got{w, s}:
      fr.win.p(w, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.win(s: String) -> Wr.Dec<Fx.Win>:
  fr.win.w(Wr.get_nat(s))

# 0 a level: the level, the user's budgets, the defaults
def fr.level.d(l: Fx.ELv, c: Fx.Customs, r: Wr.Dec<Fx.Budgets>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{d, s}:
      Wr.Got{FFx.Level{l, c, d}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def fr.level.c(l: Fx.ELv, r: Wr.Dec<Fx.Customs>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{c, s}:
      fr.level.d(l, c, fr.budgets(s))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.level(r: Wr.Dec<Fx.ELv>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{l, s}:
      fr.level.c(l, fr.customs(s))
    case Wr.Bad{}:
      Wr.Bad{}

# 1 a room: the budget, the ceiling, the answer's tokens
def fr.room.a(b: Nat, m: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{a, s}:
      Wr.Got{FFx.Room{b, m, a}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def fr.room.m(b: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{m, s}:
      fr.room.a(b, m, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.room(r: Wr.Dec<Nat>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{b, s}:
      fr.room.m(b, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# 2 an adjust: the caller's cap, the model's cap, the level, the user's
# budgets, the defaults, the answer's tokens, the window facts
def fr.adjust.w(base: Maybe<&2, Nat>, mm: Nat, l: Fx.ELv, c: Fx.Customs, d: Fx.Budgets, a: Nat, r: Wr.Dec<Fx.Win>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{w, s}:
      Wr.Got{FFx.Adjust{base, mm, l, c, d, a, w}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def fr.adjust.a(base: Maybe<&2, Nat>, mm: Nat, l: Fx.ELv, c: Fx.Customs, d: Fx.Budgets, r: Wr.Dec<Nat>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{a, s}:
      fr.adjust.w(base, mm, l, c, d, a, fr.win(s))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.adjust.d(base: Maybe<&2, Nat>, mm: Nat, l: Fx.ELv, c: Fx.Customs, r: Wr.Dec<Fx.Budgets>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{d, s}:
      fr.adjust.a(base, mm, l, c, d, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.adjust.c(base: Maybe<&2, Nat>, mm: Nat, l: Fx.ELv, r: Wr.Dec<Fx.Customs>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{c, s}:
      fr.adjust.d(base, mm, l, c, fr.budgets(s))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.adjust.l(base: Maybe<&2, Nat>, mm: Nat, r: Wr.Dec<Fx.ELv>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{l, s}:
      fr.adjust.c(base, mm, l, fr.customs(s))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.adjust.mm(base: Maybe<&2, Nat>, r: Wr.Dec<Nat>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{mm, s}:
      fr.adjust.l(base, mm, fr.elv(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.adjust(r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{base, s}:
      fr.adjust.mm(base, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# 3 a Google budget: the rule, the user's budgets, the budget level
def fr.google.l(rule: Maybe<&2, Fx.Budgets>, c: Fx.Customs, r: Wr.Dec<Fx.Lv>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{l, s}:
      Wr.Got{FFx.Google{rule, c, l}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def fr.google.c(rule: Maybe<&2, Fx.Budgets>, r: Wr.Dec<Fx.Customs>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{c, s}:
      fr.google.l(rule, c, fr.lv(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.google(r: Wr.Dec<Maybe<&2, Fx.Budgets>>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{rule, s}:
      fr.google.c(rule, fr.customs(s))
    case Wr.Bad{}:
      Wr.Bad{}

# 4 an aux cap: the user's budgets, the defaults, the answer's tokens, the
# top
def fr.aux.top(c: Fx.Customs, d: Fx.Budgets, a: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{top, s}:
      Wr.Got{FFx.Aux{c, d, a, top}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def fr.aux.a(c: Fx.Customs, d: Fx.Budgets, r: Wr.Dec<Nat>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{a, s}:
      fr.aux.top(c, d, a, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.aux.d(c: Fx.Customs, r: Wr.Dec<Fx.Budgets>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{d, s}:
      fr.aux.a(c, d, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.aux(r: Wr.Dec<Fx.Customs>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{c, s}:
      fr.aux.d(c, fr.budgets(s))
    case Wr.Bad{}:
      Wr.Bad{}

# 5 an output cap: the caller's cap, the catalog's max, needs, the window
# facts
def fr.cap.w(x: Maybe<&2, Nat>, mm: Nat, n: Bool, r: Wr.Dec<Fx.Win>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{w, s}:
      Wr.Got{FFx.Cap{x, mm, n, w}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def fr.cap.n(x: Maybe<&2, Nat>, mm: Nat, r: Wr.Dec<Bool>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{n, s}:
      fr.cap.w(x, mm, n, fr.win(s))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.cap.mm(x: Maybe<&2, Nat>, r: Wr.Dec<Nat>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{mm, s}:
      fr.cap.n(x, mm, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.cap(r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{x, s}:
      fr.cap.mm(x, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def fr.req.tag(t: Nat, s: String) -> Wr.Dec<FFx.Req>:
  match t:
    case 0n:
      fr.level(fr.elv(Wr.get_nat(s)))
    case 1n:
      fr.room(Wr.get_nat(s))
    case 2n:
      fr.adjust(fr.mnat(Wr.get_nat(s)))
    case 3n:
      fr.google(fr.mbudgets(Wr.get_nat(s)))
    case 4n:
      fr.aux(fr.customs(s))
    case 5n:
      fr.cap(fr.mnat(Wr.get_nat(s)))
    case 6n+p:
      Wr.Bad{}

def fr.req(r: Wr.Dec<Nat>) -> Wr.Dec<FFx.Req>:
  match r:
    case Wr.Got{t, s}:
      fr.req.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# the request s starts with, and what follows it
def fr.read(s: String) -> Wr.Dec<FFx.Req>:
  fr.req(Wr.get_nat(s))

# Decisions
# ---------

# the budget level of a request's level: each keeps its own, xhigh and max
# take high (facts_budget_levels)
def fs.lv(l: Fx.ELv) -> Fx.Lv:
  match l:
    case Fx.EMinimal{}:
      Fx.Minimal{}
    case Fx.ELow{}:
      Fx.Low{}
    case Fx.EMedium{}:
      Fx.Medium{}
    case Fx.EHigh{}:
      Fx.High{}
    case Fx.EXhigh{}:
      Fx.High{}
    case Fx.EMax{}:
      Fx.High{}

# the budget a table d gives the level l
def fs.at(d: Fx.Budgets, l: Fx.Lv) -> Nat:
  match d:
    case Fx.Budgets{mi, lo, me, hi}:
      match l:
        case Fx.Minimal{}:
          mi
        case Fx.Low{}:
          lo
        case Fx.Medium{}:
          me
        case Fx.High{}:
          hi

def fs.minimal(d: Fx.Budgets) -> Nat:
  match d:
    case Fx.Budgets{mi, lo, me, hi}:
      mi

def fs.high(d: Fx.Budgets) -> Nat:
  match d:
    case Fx.Budgets{mi, lo, me, hi}:
      hi

# the budget of the level l: the user's, else the default
# (stated by facts_ffi_exact itself; no model law restates it)
def fs.budget(c: Fx.Customs, d: Fx.Budgets, +l: Fx.Lv) -> Nat:
  Maybe.default(&2, Nat, Facts.customs_spec(c, l), fs.at(d, l))

# the budget b capped so that a tokens stay under the ceiling m
def fs.room(+b: Nat, +m: Nat, +a: Nat) -> Nat:
  Nat.min(b, Nat.sub(m, a))

# the cap x through the window: the room after the prompt and the safety
# (at least the floor) on a real conflict, else x (facts_cap_keeps_the_want,
# facts_cap_shrinks_on_conflict)
def fs.shrink.at(over: Bool, +x: Nat, win: Fx.Win) -> Nat:
  match over:
    case True{}:
      Facts.cap_room(win)
    case False{}:
      x

def fs.shrink(+x: Nat, +win: Fx.Win) -> Nat:
  fs.shrink.at(Facts.cap_conflict(x, win), x, win)

# the thinking ceiling before the window: the caller's cap plus the
# budget, at most the model's cap; else the model's cap
# (facts_fit_ceiling_is_the_cap)
def fs.ceiling(base: Maybe<&2, Nat>, +mm: Nat, +b: Nat) -> Nat:
  match base:
    case None{}:
      mm
    case Some{x}:
      Nat.min(Nat.add(x, b), mm)

def fs.fit(base: Maybe<&2, Nat>, +mm: Nat, +b: Nat, +a: Nat, +win: Fx.Win) -> Fx.Fit:
  Facts.budgets.fit(fs.shrink(fs.ceiling(base, mm, b), win), b, a)

# each level of a rule at least the one before it
def fs.ordered(d: Fx.Budgets) -> Bool:
  match d:
    case Fx.Budgets{+mi, +lo, +me, +hi}:
      Bool.and(Nat.is_le(mi, lo), Bool.and(Nat.is_le(lo, me), Nat.is_le(me, hi)))

# a Google budget without a rule: the user's budget, else dynamic
# (stated by facts_ffi_exact itself; no model law restates it)
def fs.gb.free(m: Maybe<&2, Nat>) -> Fx.GB:
  match m:
    case Some{n}:
      Fx.Tokens{n}
    case None{}:
      Fx.Dynamic{}

# a Google budget with the rule b: refused when the rule is not ordered,
# else the user's budget of the level, else the rule's, held inside the
# rule's minimal..high (facts_google_unordered_refused,
# facts_google_user_kept, facts_google_user_raised, facts_google_user_lowered,
# facts_google_rule_default)
def fs.gb.rule(ok: Bool, +b: Fx.Budgets, c: Fx.Customs, +l: Fx.Lv) -> Fx.GB:
  match ok:
    case True{}:
      Fx.Tokens{Facts.budgets.held(Maybe.default(&2, Nat, Facts.customs_spec(c, l), fs.at(b, l)), fs.minimal(b), fs.high(b))}
    case False{}:
      Fx.Unordered{}

def fs.gb(rule: Maybe<&2, Fx.Budgets>, c: Fx.Customs, +l: Fx.Lv) -> Fx.GB:
  match rule:
    case None{}:
      fs.gb.free(Facts.customs_spec(c, l))
    case Some{+b}:
      fs.gb.rule(fs.ordered(b), b, c, l)

# an auxiliary call's output cap: the high budget plus the answer's tokens,
# at most the top (facts_aux_keeps_answer_room, facts_aux_saturates_at_top)
def fs.aux(c: Fx.Customs, d: Fx.Budgets, +a: Nat, +top: Nat) -> Nat:
  Nat.min(Nat.add(fs.budget(c, d, Fx.High{}), a), top)

# the output cap: none when the max is unknown (facts_cap_omits_unknown),
# else the wish through the window
def fs.cap.at(unknown: Bool, caller: Maybe<&2, Nat>, +mm: Nat, +win: Fx.Win) -> Maybe<&2, Nat>:
  match unknown:
    case True{}:
      None{}
    case False{}:
      Some{fs.shrink(Facts.cap_want(caller, mm), win)}

def fs.cap(+caller: Maybe<&2, Nat>, +mm: Nat, +needs: Bool, +win: Fx.Win) -> Maybe<&2, Nat>:
  fs.cap.at(Facts.cap_unknown(caller, mm, needs, win), caller, mm, win)

# Speller
# -------

def fs.put_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))

def fs.put_gb(g: Fx.GB, rest: String) -> String:
  match g:
    case Fx.Dynamic{}:
      Wr.put_nat(0n, rest)
    case Fx.Tokens{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))
    case Fx.Unordered{}:
      Wr.put_nat(2n, rest)

def fs.put_fit(f: Fx.Fit, rest: String) -> String:
  match f:
    case Fx.Fit{m, b}:
      Wr.put_nat(m, Wr.put_nat(b, rest))

# the reply to a whole request
def fs.reply(q: FFx.Req) -> String:
  match q:
    case FFx.Level{l, c, d}:
      Wr.put_nat(fs.budget(c, d, fs.lv(l)), "")
    case FFx.Room{b, m, a}:
      Wr.put_nat(fs.room(b, m, a), "")
    case FFx.Adjust{base, mm, l, c, d, a, w}:
      fs.put_fit(fs.fit(base, mm, fs.budget(c, d, fs.lv(l)), a, w), "")
    case FFx.Google{rule, c, l}:
      fs.put_gb(fs.gb(rule, c, l), "")
    case FFx.Aux{c, d, a, top}:
      Wr.put_nat(fs.aux(c, d, a, top), "")
    case FFx.Cap{x, mm, n, w}:
      fs.put_mnat(fs.cap(x, mm, n, w), "")

def fs.end(whole: Bool, q: FFx.Req) -> String:
  match whole:
    case True{}:
      fs.reply(q)
    case False{}:
      Wr.err("budget request: input left over")

def fs.run(r: Wr.Dec<FFx.Req>) -> String:
  match r:
    case Wr.Got{q, s}:
      fs.end(Wr.end(s), q)
    case Wr.Bad{}:
      Wr.err("budget request: malformed")

# the reply to the input s
def fs.spec(s: String) -> String:
  fs.run(fr.read(s))

# LAW facts_ffi_exact (R1-R3 of laws/facts/budgets.bend): on every input the entry answers the decision (as the laws of laws/facts/model.bend state it) on the request the input starts with, spelled as the Rust reader reads it, when nothing follows the request; "budget request: input left over" when something does; "budget request: malformed" when the input starts with no request
# EXCLUDES: a budget, a fit, a Google budget, an aux cap or an output cap
#   other than the laws' on any request (the default over the user's
#   budget, a ceiling past the model's cap, an unordered rule clamped, a
#   cap made up for an unknown max); a reply in another spelling; a value
#   for an input that is no request (an unknown tag, a short field, a
#   15-digit number) or for a request with input left over; another
#   error text
law facts_ffi_exact:
  for +s: String
  {FFx.ffi(s) == fs.spec(s) : String}
