# eukhe: lemmas the proofs of area cron share: the entry's reader
# (bend/ffi_cron.bend) answers what the laws' reader answers on every
# input, one lemma per stage, each a case split on the stage's input; and
# the entry reads back what the laws' spellers write.

import Base
import ../../../bend/cron.bend as Cr
import ../../../bend/cron_store.bend as CS
import ../../../bend/ffi_cron.bend as FC
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/cron.bend as Cron
import ../../base/wire.bend as LWire

# Logic
# -----

def ce.If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

def cre.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : ce.If(_, G)
  Unit{}

def cre.and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      cre.absurd({False{} == True{} : Bool}, e)

def cre.and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      cre.absurd({b == True{} : Bool}, e)

def cre.if_none(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

# a claim that Some is None proves anything
def cre.some_none(-A: Data, -x: A, -G: Type, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  %e : cre.if_none(A, _, G)
  Unit{}

# The reader, stage by stage
# --------------------------

def cre.status_tag(t: Nat, s: String) -> {Cron.read_status.tag(t, s) == FC.get_status.tag(t, s) : Wr.Dec<Cr.Status>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n+p:
      {==}

def cre.status(r: Wr.Dec<Nat>) -> {Cron.read_status(r) == FC.get_status(r) : Wr.Dec<Cr.Status>}:
  match r:
    case Wr.Got{t, s}:
      cre.status_tag(t, s)
    case Wr.Bad{}:
      {==}

def cre.plan_every(r: Wr.Dec<Nat>) -> {Cron.read_plan.every(r) == FC.get_plan.every(r) : Wr.Dec<CS.Plan>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cre.plan_tag(t: Nat, s: String) -> {Cron.read_plan.tag(t, s) == FC.get_plan.tag(t, s) : Wr.Dec<CS.Plan>}:
  match t:
    case 0n:
      {==}
    case 1n:
      cre.plan_every(Wr.get_nat(s))
    case 2n:
      {==}
    case 3n+p:
      {==}

def cre.plan(r: Wr.Dec<Nat>) -> {Cron.read_plan(r) == FC.get_plan(r) : Wr.Dec<CS.Plan>}:
  match r:
    case Wr.Got{t, s}:
      cre.plan_tag(t, s)
    case Wr.Bad{}:
      {==}

def cre.mnat_some(r: Wr.Dec<Nat>) -> {Cron.read_mnat.some(r) == FC.get_mnat.some(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cre.mnat_tag(t: Nat, s: String) -> {Cron.read_mnat.tag(t, s) == FC.get_mnat.tag(t, s) : Wr.Dec<Maybe<&2, Nat>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      cre.mnat_some(Wr.get_nat(s))
    case 2n+p:
      {==}

def cre.mnat(r: Wr.Dec<Nat>) -> {Cron.read_mnat(r) == FC.get_mnat(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{t, s}:
      cre.mnat_tag(t, s)
    case Wr.Bad{}:
      {==}

def cre.fact_streak(st: Cr.Status, p: CS.Plan, m: Maybe<&2, Nat>, r: Wr.Dec<Nat>) -> {Cron.read_fact.streak(st, p, m, r) == FC.get_fact.streak(st, p, m, r) : Wr.Dec<CS.Fact>}:
  match r:
    case Wr.Got{k, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cre.fact_next(st: Cr.Status, p: CS.Plan, r: Wr.Dec<Maybe<&2, Nat>>) -> {Cron.read_fact.next(st, p, r) == FC.get_fact.next(st, p, r) : Wr.Dec<CS.Fact>}:
  match r:
    case Wr.Got{m, s}:
      cre.fact_streak(st, p, m, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def cre.fact_plan(+st: Cr.Status, r: Wr.Dec<CS.Plan>) -> {Cron.read_fact.plan(st, r) == FC.get_fact.plan(st, r) : Wr.Dec<CS.Fact>}:
  match r:
    case Wr.Got{+p, +s}:
      %cre.mnat(Wr.get_nat(s)) : {Cron.read_fact.next(st, p, Cron.read_mnat(Wr.get_nat(s))) == FC.get_fact.next(st, p, _) : Wr.Dec<CS.Fact>}
      cre.fact_next(st, p, Cron.read_mnat(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def cre.fact_status(r: Wr.Dec<Cr.Status>) -> {Cron.read_fact.status(r) == FC.get_fact.status(r) : Wr.Dec<CS.Fact>}:
  match r:
    case Wr.Got{+st, +s}:
      %cre.plan(Wr.get_nat(s)) : {Cron.read_fact.plan(st, Cron.read_plan(Wr.get_nat(s))) == FC.get_fact.plan(st, _) : Wr.Dec<CS.Fact>}
      cre.fact_plan(st, Cron.read_plan(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def cre.fact(+s: String) -> {Cron.read_fact(s) == FC.get_fact(s) : Wr.Dec<CS.Fact>}:
  %cre.status(Wr.get_nat(s)) : {Cron.read_fact.status(Cron.read_status(Wr.get_nat(s))) == FC.get_fact.status(_) : Wr.Dec<CS.Fact>}
  cre.fact_status(Cron.read_status(Wr.get_nat(s)))

def cre.take_now(f: CS.Fact, c: Bool, d: Nat, r: Wr.Dec<Nat>) -> {Cron.read_take.now(f, c, d, r) == FC.get_take.now(f, c, d, r) : Wr.Dec<CS.Ask>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cre.take_due(f: CS.Fact, c: Bool, r: Wr.Dec<Nat>) -> {Cron.read_take.due(f, c, r) == FC.get_take.due(f, c, r) : Wr.Dec<CS.Ask>}:
  match r:
    case Wr.Got{d, s}:
      cre.take_now(f, c, d, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def cre.take_claimed(f: CS.Fact, r: Wr.Dec<Bool>) -> {Cron.read_take.claimed(f, r) == FC.get_take.claimed(f, r) : Wr.Dec<CS.Ask>}:
  match r:
    case Wr.Got{c, s}:
      cre.take_due(f, c, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def cre.take(r: Wr.Dec<CS.Fact>) -> {Cron.read_take(r) == FC.get_take(r) : Wr.Dec<CS.Ask>}:
  match r:
    case Wr.Got{f, s}:
      cre.take_claimed(f, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def cre.who_mine(r: Wr.Dec<Bool>) -> {Cron.read_who.mine(r) == FC.get_who.mine(r) : Wr.Dec<CS.Who>}:
  match r:
    case Wr.Got{b, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cre.who_theirs(r: Wr.Dec<Bool>) -> {Cron.read_who.theirs(r) == FC.get_who.theirs(r) : Wr.Dec<CS.Who>}:
  match r:
    case Wr.Got{b, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cre.who_tag(t: Nat, s: String) -> {Cron.read_who.tag(t, s) == FC.get_who.tag(t, s) : Wr.Dec<CS.Who>}:
  match t:
    case 0n:
      cre.who_mine(Wr.get_bool(s))
    case 1n:
      cre.who_theirs(Wr.get_bool(s))
    case 2n+p:
      {==}

def cre.who(r: Wr.Dec<Nat>) -> {Cron.read_who(r) == FC.get_who(r) : Wr.Dec<CS.Who>}:
  match r:
    case Wr.Got{t, s}:
      cre.who_tag(t, s)
    case Wr.Bad{}:
      {==}

def cre.clear(r: Wr.Dec<CS.Who>) -> {Cron.read_clear(r) == FC.get_clear(r) : Wr.Dec<CS.Ask>}:
  match r:
    case Wr.Got{w, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cre.recover_cleared(f: CS.Fact, r: Wr.Dec<Bool>) -> {Cron.read_recover.cleared(f, r) == FC.get_recover.cleared(f, r) : Wr.Dec<CS.Ask>}:
  match r:
    case Wr.Got{c, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cre.recover(r: Wr.Dec<CS.Fact>) -> {Cron.read_recover(r) == FC.get_recover(r) : Wr.Dec<CS.Ask>}:
  match r:
    case Wr.Got{f, s}:
      cre.recover_cleared(f, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def cre.finish_now(f: CS.Fact, a: Bool, b: Bool, r: Wr.Dec<Nat>) -> {Cron.read_finish.now(f, a, b, r) == FC.get_finish.now(f, a, b, r) : Wr.Dec<CS.Ask>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cre.finish_failed(f: CS.Fact, a: Bool, r: Wr.Dec<Bool>) -> {Cron.read_finish.failed(f, a, r) == FC.get_finish.failed(f, a, r) : Wr.Dec<CS.Ask>}:
  match r:
    case Wr.Got{b, s}:
      cre.finish_now(f, a, b, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def cre.finish_ran(f: CS.Fact, r: Wr.Dec<Bool>) -> {Cron.read_finish.ran(f, r) == FC.get_finish.ran(f, r) : Wr.Dec<CS.Ask>}:
  match r:
    case Wr.Got{a, s}:
      cre.finish_failed(f, a, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def cre.finish(r: Wr.Dec<CS.Fact>) -> {Cron.read_finish(r) == FC.get_finish(r) : Wr.Dec<CS.Ask>}:
  match r:
    case Wr.Got{f, s}:
      cre.finish_ran(f, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def cre.cancel(r: Wr.Dec<CS.Fact>) -> {Cron.read_cancel(r) == FC.get_cancel(r) : Wr.Dec<CS.Ask>}:
  match r:
    case Wr.Got{f, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cre.resume_now(f: CS.Fact, r: Wr.Dec<Nat>) -> {Cron.read_resume.now(f, r) == FC.get_resume.now(f, r) : Wr.Dec<CS.Ask>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cre.resume(r: Wr.Dec<CS.Fact>) -> {Cron.read_resume(r) == FC.get_resume(r) : Wr.Dec<CS.Ask>}:
  match r:
    case Wr.Got{f, s}:
      cre.resume_now(f, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def cre.ask_tag(t: Nat, +s: String) -> {Cron.read_ask.tag(t, s) == FC.get_ask.tag(t, s) : Wr.Dec<CS.Ask>}:
  match t:
    case 0n:
      %cre.fact(s) : {Cron.read_take(Cron.read_fact(s)) == FC.get_take(_) : Wr.Dec<CS.Ask>}
      cre.take(Cron.read_fact(s))
    case 1n:
      %cre.who(Wr.get_nat(s)) : {Cron.read_clear(Cron.read_who(Wr.get_nat(s))) == FC.get_clear(_) : Wr.Dec<CS.Ask>}
      cre.clear(Cron.read_who(Wr.get_nat(s)))
    case 2n:
      %cre.fact(s) : {Cron.read_recover(Cron.read_fact(s)) == FC.get_recover(_) : Wr.Dec<CS.Ask>}
      cre.recover(Cron.read_fact(s))
    case 3n:
      %cre.fact(s) : {Cron.read_finish(Cron.read_fact(s)) == FC.get_finish(_) : Wr.Dec<CS.Ask>}
      cre.finish(Cron.read_fact(s))
    case 4n:
      %cre.fact(s) : {Cron.read_cancel(Cron.read_fact(s)) == FC.get_cancel(_) : Wr.Dec<CS.Ask>}
      cre.cancel(Cron.read_fact(s))
    case 5n:
      %cre.fact(s) : {Cron.read_resume(Cron.read_fact(s)) == FC.get_resume(_) : Wr.Dec<CS.Ask>}
      cre.resume(Cron.read_fact(s))
    case 6n+p:
      {==}

# the entry reads every input as the laws' reader does
def cre.ask(r: Wr.Dec<Nat>) -> {Cron.read_ask.go(r) == FC.get_ask.go(r) : Wr.Dec<CS.Ask>}:
  match r:
    case Wr.Got{t, s}:
      cre.ask_tag(t, s)
    case Wr.Bad{}:
      {==}

# Round trips
# -----------

def crr.bool(b: Bool, rest: String) -> {Wr.Got{b, rest} == Wr.get_bool(Wr.put_bool(b, rest)) : Wr.Dec<Bool>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def crr.status(st: Cr.Status, rest: String) -> {Wr.Got{st, rest} == FC.get_status(Wr.get_nat(Cron.spell_status(st, rest))) : Wr.Dec<Cr.Status>}:
  match st:
    case Cr.Active{}:
      {==}
    case Cr.Paused{}:
      {==}
    case Cr.Finished{}:
      {==}
    case Cr.Cancelled{}:
      {==}

def crr.plan(p: CS.Plan, +rest: String, fits: {Cron.plan_fits(p) == True{} : Bool}) -> {Wr.Got{p, rest} == FC.get_plan(Wr.get_nat(Cron.spell_plan(p, rest))) : Wr.Dec<CS.Plan>}:
  match p:
    case CS.POnce{}:
      {==}
    case CS.PEvery{+ms}:
      %LWire.pw6.nat(ms, rest, fits) : {Wr.Got{CS.PEvery{ms}, rest} == FC.get_plan.every(_) : Wr.Dec<CS.Plan>}
      {==}
    case CS.PRule{}:
      {==}

def crr.mnat(m: Maybe<&2, Nat>, +rest: String, fits: {LawsBase.core_mfits(m) == True{} : Bool}) -> {Wr.Got{m, rest} == FC.get_mnat(Wr.get_nat(Cron.spell_mnat(m, rest))) : Wr.Dec<Maybe<&2, Nat>>}:
  match m:
    case None{}:
      {==}
    case Some{+n}:
      %LWire.pw6.nat(n, rest, fits) : {Wr.Got{Some{n}, rest} == FC.get_mnat.some(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}

# a fact the laws spell reads back, whatever follows it
def crr.fact(f: CS.Fact, +rest: String, +fits: {Cron.fact_fits(f) == True{} : Bool}) -> {Wr.Got{f, rest} == FC.get_fact(Cron.spell_fact(f, rest)) : Wr.Dec<CS.Fact>}:
  match f:
    case CS.Fact{+st, +p, +nx, +k}:
      +f2 = cre.and_r(Cron.plan_fits(p), Bool.and(LawsBase.core_mfits(nx), LawsBase.wire_fits(k)), fits)
      %crr.status(st, Cron.spell_plan(p, Cron.spell_mnat(nx, Wr.put_nat(k, rest)))) : {Wr.Got{CS.Fact{st, p, nx, k}, rest} == FC.get_fact.status(_) : Wr.Dec<CS.Fact>}
      %crr.plan(p, Cron.spell_mnat(nx, Wr.put_nat(k, rest)), cre.and_l(Cron.plan_fits(p), Bool.and(LawsBase.core_mfits(nx), LawsBase.wire_fits(k)), fits)) : {Wr.Got{CS.Fact{st, p, nx, k}, rest} == FC.get_fact.plan(st, _) : Wr.Dec<CS.Fact>}
      %crr.mnat(nx, Wr.put_nat(k, rest), cre.and_l(LawsBase.core_mfits(nx), LawsBase.wire_fits(k), f2)) : {Wr.Got{CS.Fact{st, p, nx, k}, rest} == FC.get_fact.next(st, p, _) : Wr.Dec<CS.Fact>}
      %LWire.pw6.nat(k, rest, cre.and_r(LawsBase.core_mfits(nx), LawsBase.wire_fits(k), f2)) : {Wr.Got{CS.Fact{st, p, nx, k}, rest} == FC.get_fact.streak(st, p, nx, _) : Wr.Dec<CS.Fact>}
      {==}
