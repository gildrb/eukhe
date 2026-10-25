# eukhe: the laws of area cron

import Base
import ../bend/cron.bend as Cr
import ../bend/cron_store.bend as CS
import ../bend/ffi_cron.bend as FC
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ./cron_store.bend as CronStore

# ---- cron ----

# LAWS (D2): the cron store shared by processes. Each law is an open claim
# about the model in bend/cron.bend; PROOF.bend proves them (as
# Cron.<law>) with the lemmas of proof/cron/.

# (D2) Cron
# ---------
# docs/state.md D2. The cron jobs file `cron-jobs.json` (bend/cron.bend),
# shared by any number of processes. Every input is free: any events of
# any processes in any order (make a job, claim the due jobs, recover
# claims, finish a run good, failed or skipped, unwind a pass, die), any
# user actions (cancel, resume), any time, any records this build cannot
# read, a corrupt file at any point.

# LAW cron_fires_once: after any events, each job is run by at most one process, and that
# run holds the claim on record; no occurrence of a job starts twice (the
# occurrences that started fall strictly, the newest first); a one-shot
# starts at most once
law cron_fires_once:
  for +evs: List<&2, Cr.Ev>
  Cr.FiresAll(Cr.S.recs(Cr.run(evs)))

# LAW cron_once_finished_after_end: after any events, a finished one-shot has no run: it is finished
# only after its run ended
law cron_once_finished_after_end:
  for +evs: List<&2, Cr.Ev>
  Cr.EndsAll(Cr.S.recs(Cr.run(evs)))

# LAW cron_never_drops: from any file (records read or not, corrupt or not), a step that
# is not the file's corruption keeps every record: each job record this
# build cannot read with the same bytes, each job, each claim record this
# build cannot read, the corrupt file (in place or moved aside, never
# written over), each file moved aside
law cron_never_drops:
  for +s: Cr.S
  for +e: Cr.Ev
  for +t: Nat
  for +i: Nat
  {Cr.Ev.is_corrupt(e) == False{} : Bool} -> Cr.Keeps(t, i, s, Cr.step(s, e))

# LAW cron_claim_owned: from any state, a step of process p removes the claim of process o
# on job i only when o is p or o is dead; no other step (but the file's
# corruption) removes a claim
law cron_claim_owned:
  for +s: Cr.S
  for +e: Cr.Ev
  for +i: Nat
  for +x: Nat
  for +o: Nat
  {Cr.Ev.is_corrupt(e) == False{} : Bool} -> {Cr.claim_of(i, Cr.S.recs(s)) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>} -> Or({Cr.claim_of(i, Cr.S.recs(Cr.step(s, e))) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}, Or({Cr.Ev.by(e) == Some{o} : Maybe<&2, Nat>}, {Cr.has(o, Cr.S.dead(s)) == True{} : Bool}))

# LAW cron_backoff_bounded: after any events, a job counted at most CAP failed runs in a row,
# and an active job fewer: so the CAP-th failure in a row stops it; a
# stopped (paused) job stays stopped through every step that is not a user
# action; the pause after the k-th failure is never shorter than after the
# (k-1)-th, and a failure never moves the next run before its pause ends
law cron_backoff_bounded:
  for +evs: List<&2, Cr.Ev>
  for +s: Cr.S
  for +e: Cr.Ev
  for +i: Nat
  for +k: Nat
  for +c: Nat
  for +nx: Maybe<&2, Nat>
  (Cr.StopsAll(Cr.S.recs(Cr.run(evs))) & (({Cr.Ev.is_user(e) == False{} : Bool} -> Cr.StaysPaused(i, s, Cr.step(s, e))) & ({Nat.is_le(Cr.delay(k), Cr.delay(1n+k)) == True{} : Bool} & {Nat.is_le(Nat.add(c, Cr.delay(k)), Cr.later(nx, Nat.add(c, Cr.delay(k)))) == True{} : Bool})))

# (D2.2) The per-job decisions, and the entry Rust calls
# ------------------------------------------------------
# crates/eukhe-core/src/cron/store/ (state.rs `claim_due_in_state`,
# `recover_interrupted_in_state`, jobs.rs `record_dispatch_result`,
# `cancel`, the resumes of heartbeat.rs and rlm_heartbeat.rs) reads the
# jobs file, gathers one job's facts and calls the entry
# bend/ffi_cron.bend, which runs bend/cron_store.bend on the store's clock
# (ms). The spec (laws/cron_store.bend) states each decision on a clock of
# any unit u, and pins the code to it; the spellers and the reader are the entry's wire grammar written with the
# wire primitives alone (laws/wire.bend proves their round trips); they
# never call the entry's codec. The `cron_*_refines` laws tie each
# decision, on every clock unit (the store's: a minute is 60000 ms), to
# the model's step of bend/cron.bend that the laws above speak of.

# Terms
# -----

# the store's clock unit: a minute in ms
def minute_spec() -> Nat:
  60000n

# Spellers: the request

def spell_status(st: Cr.Status, rest: String) -> String:
  match st:
    case Cr.Active{}:
      Wr.put_nat(0n, rest)
    case Cr.Paused{}:
      Wr.put_nat(1n, rest)
    case Cr.Finished{}:
      Wr.put_nat(2n, rest)
    case Cr.Cancelled{}:
      Wr.put_nat(3n, rest)

def spell_plan(p: CS.Plan, rest: String) -> String:
  match p:
    case CS.POnce{}:
      Wr.put_nat(0n, rest)
    case CS.PEvery{ms}:
      Wr.put_nat(1n, Wr.put_nat(ms, rest))
    case CS.PRule{}:
      Wr.put_nat(2n, rest)

def spell_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))

def spell_fact(f: CS.Fact, rest: String) -> String:
  match f:
    case CS.Fact{st, p, nx, k}:
      spell_status(st, spell_plan(p, spell_mnat(nx, Wr.put_nat(k, rest))))

def spell_who(w: CS.Who, rest: String) -> String:
  match w:
    case CS.Mine{b}:
      Wr.put_nat(0n, Wr.put_bool(b, rest))
    case CS.Theirs{b}:
      Wr.put_nat(1n, Wr.put_bool(b, rest))

# the request Rust writes for a
def spell_ask(a: CS.Ask) -> String:
  match a:
    case CS.AskTake{f, c, d, n}:
      Wr.put_nat(0n, spell_fact(f, Wr.put_bool(c, Wr.put_nat(d, Wr.put_nat(n, "")))))
    case CS.AskClear{w}:
      Wr.put_nat(1n, spell_who(w, ""))
    case CS.AskRecover{f, c}:
      Wr.put_nat(2n, spell_fact(f, Wr.put_bool(c, "")))
    case CS.AskFinish{f, r, b, n}:
      Wr.put_nat(3n, spell_fact(f, Wr.put_bool(r, Wr.put_bool(b, Wr.put_nat(n, "")))))
    case CS.AskCancel{f}:
      Wr.put_nat(4n, spell_fact(f, ""))
    case CS.AskResume{f, n}:
      Wr.put_nat(5n, spell_fact(f, Wr.put_nat(n, "")))

def plan_fits(p: CS.Plan) -> Bool:
  match p:
    case CS.POnce{}:
      True{}
    case CS.PEvery{ms}:
      LawsBase.wire_fits(ms)
    case CS.PRule{}:
      True{}

def fact_fits(f: CS.Fact) -> Bool:
  match f:
    case CS.Fact{st, p, nx, k}:
      Bool.and(plan_fits(p), Bool.and(LawsBase.core_mfits(nx), LawsBase.wire_fits(k)))

# every number of a fits the wire
def ask_fits(a: CS.Ask) -> Bool:
  match a:
    case CS.AskTake{f, c, d, n}:
      Bool.and(fact_fits(f), Bool.and(LawsBase.wire_fits(d), LawsBase.wire_fits(n)))
    case CS.AskClear{w}:
      True{}
    case CS.AskRecover{f, c}:
      fact_fits(f)
    case CS.AskFinish{f, r, b, n}:
      Bool.and(fact_fits(f), LawsBase.wire_fits(n))
    case CS.AskCancel{f}:
      fact_fits(f)
    case CS.AskResume{f, n}:
      Bool.and(fact_fits(f), LawsBase.wire_fits(n))

# Spellers: the reply

def spell_next(n: CS.Next, rest: String) -> String:
  match n:
    case CS.NNone{}:
      Wr.put_nat(0n, rest)
    case CS.NAt{x}:
      Wr.put_nat(1n, Wr.put_nat(x, rest))
    case CS.NRoll{}:
      Wr.put_nat(2n, rest)

def spell_took(t: CS.Took, rest: String) -> String:
  match t:
    case CS.Keep{}:
      Wr.put_nat(0n, rest)
    case CS.Roll{n}:
      Wr.put_nat(1n, spell_next(n, rest))
    case CS.Claimed{n}:
      Wr.put_nat(2n, spell_next(n, rest))

def spell_back(b: CS.Back, rest: String) -> String:
  match b:
    case CS.Kept{}:
      Wr.put_nat(0n, rest)
    case CS.Interrupted{st, m}:
      Wr.put_nat(1n, spell_status(st, spell_mnat(m, rest)))

def spell_fin(x: CS.Fin, rest: String) -> String:
  match x:
    case CS.Untouched{}:
      Wr.put_nat(0n, rest)
    case CS.Ran{st, n, k}:
      Wr.put_nat(1n, spell_status(st, spell_next(n, Wr.put_nat(k, rest))))
    case CS.Skipped{st, n, k}:
      Wr.put_nat(2n, spell_status(st, spell_next(n, Wr.put_nat(k, rest))))

def spell_cut(x: CS.Cut, rest: String) -> String:
  match x:
    case CS.Same{}:
      Wr.put_nat(0n, rest)
    case CS.Cut{st, m}:
      Wr.put_nat(1n, spell_status(st, spell_mnat(m, rest)))

def spell_again(x: CS.Again, rest: String) -> String:
  match x:
    case CS.Resumed{st, n, k}:
      Wr.put_nat(0n, spell_status(st, spell_next(n, Wr.put_nat(k, rest))))
    case CS.Ended{}:
      Wr.put_nat(1n, rest)
    case CS.NotRecurring{}:
      Wr.put_nat(2n, rest)

# the reply to a: the decision of the spec, on the store's clock
def spell_answer(a: CS.Ask) -> String:
  match a:
    case CS.AskTake{f, c, d, n}:
      spell_took(CronStore.take_spec(f, c, d, n), "")
    case CS.AskClear{w}:
      Wr.put_bool(CronStore.clear_spec(w), "")
    case CS.AskRecover{f, c}:
      spell_back(CronStore.recover_spec(f, c), "")
    case CS.AskFinish{f, r, b, n}:
      spell_fin(CronStore.finish_spec(minute_spec(), f, r, b, n), "")
    case CS.AskCancel{f}:
      spell_cut(CronStore.cancel_spec(f), "")
    case CS.AskResume{f, n}:
      spell_again(CronStore.resume_spec(f, n), "")

# Reader: the requests the entry accepts, read with the wire primitives

def read_status.tag(t: Nat, s: String) -> Wr.Dec<Cr.Status>:
  match t:
    case 0n:
      Wr.Got{Cr.Active{}, s}
    case 1n:
      Wr.Got{Cr.Paused{}, s}
    case 2n:
      Wr.Got{Cr.Finished{}, s}
    case 3n:
      Wr.Got{Cr.Cancelled{}, s}
    case 4n+p:
      Wr.Bad{}

def read_status(r: Wr.Dec<Nat>) -> Wr.Dec<Cr.Status>:
  match r:
    case Wr.Got{t, s}:
      read_status.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_plan.every(r: Wr.Dec<Nat>) -> Wr.Dec<CS.Plan>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{CS.PEvery{n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_plan.tag(t: Nat, s: String) -> Wr.Dec<CS.Plan>:
  match t:
    case 0n:
      Wr.Got{CS.POnce{}, s}
    case 1n:
      read_plan.every(Wr.get_nat(s))
    case 2n:
      Wr.Got{CS.PRule{}, s}
    case 3n+p:
      Wr.Bad{}

def read_plan(r: Wr.Dec<Nat>) -> Wr.Dec<CS.Plan>:
  match r:
    case Wr.Got{t, s}:
      read_plan.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_mnat.some(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{Some{n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_mnat.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      read_mnat.some(Wr.get_nat(s))
    case 2n+p:
      Wr.Bad{}

def read_mnat(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{t, s}:
      read_mnat.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_fact.streak(st: Cr.Status, p: CS.Plan, m: Maybe<&2, Nat>, r: Wr.Dec<Nat>) -> Wr.Dec<CS.Fact>:
  match r:
    case Wr.Got{k, s}:
      Wr.Got{CS.Fact{st, p, m, k}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_fact.next(st: Cr.Status, p: CS.Plan, r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<CS.Fact>:
  match r:
    case Wr.Got{m, s}:
      read_fact.streak(st, p, m, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_fact.plan(st: Cr.Status, r: Wr.Dec<CS.Plan>) -> Wr.Dec<CS.Fact>:
  match r:
    case Wr.Got{p, s}:
      read_fact.next(st, p, read_mnat(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_fact.status(r: Wr.Dec<Cr.Status>) -> Wr.Dec<CS.Fact>:
  match r:
    case Wr.Got{st, s}:
      read_fact.plan(st, read_plan(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_fact(s: String) -> Wr.Dec<CS.Fact>:
  read_fact.status(read_status(Wr.get_nat(s)))

def read_take.now(f: CS.Fact, c: Bool, d: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<CS.Ask>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{CS.AskTake{f, c, d, n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_take.due(f: CS.Fact, c: Bool, r: Wr.Dec<Nat>) -> Wr.Dec<CS.Ask>:
  match r:
    case Wr.Got{d, s}:
      read_take.now(f, c, d, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_take.claimed(f: CS.Fact, r: Wr.Dec<Bool>) -> Wr.Dec<CS.Ask>:
  match r:
    case Wr.Got{c, s}:
      read_take.due(f, c, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_take(r: Wr.Dec<CS.Fact>) -> Wr.Dec<CS.Ask>:
  match r:
    case Wr.Got{f, s}:
      read_take.claimed(f, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_who.mine(r: Wr.Dec<Bool>) -> Wr.Dec<CS.Who>:
  match r:
    case Wr.Got{b, s}:
      Wr.Got{CS.Mine{b}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_who.theirs(r: Wr.Dec<Bool>) -> Wr.Dec<CS.Who>:
  match r:
    case Wr.Got{b, s}:
      Wr.Got{CS.Theirs{b}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_who.tag(t: Nat, s: String) -> Wr.Dec<CS.Who>:
  match t:
    case 0n:
      read_who.mine(Wr.get_bool(s))
    case 1n:
      read_who.theirs(Wr.get_bool(s))
    case 2n+p:
      Wr.Bad{}

def read_who(r: Wr.Dec<Nat>) -> Wr.Dec<CS.Who>:
  match r:
    case Wr.Got{t, s}:
      read_who.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_clear(r: Wr.Dec<CS.Who>) -> Wr.Dec<CS.Ask>:
  match r:
    case Wr.Got{w, s}:
      Wr.Got{CS.AskClear{w}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_recover.cleared(f: CS.Fact, r: Wr.Dec<Bool>) -> Wr.Dec<CS.Ask>:
  match r:
    case Wr.Got{c, s}:
      Wr.Got{CS.AskRecover{f, c}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_recover(r: Wr.Dec<CS.Fact>) -> Wr.Dec<CS.Ask>:
  match r:
    case Wr.Got{f, s}:
      read_recover.cleared(f, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_finish.now(f: CS.Fact, a: Bool, b: Bool, r: Wr.Dec<Nat>) -> Wr.Dec<CS.Ask>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{CS.AskFinish{f, a, b, n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_finish.failed(f: CS.Fact, a: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<CS.Ask>:
  match r:
    case Wr.Got{b, s}:
      read_finish.now(f, a, b, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_finish.ran(f: CS.Fact, r: Wr.Dec<Bool>) -> Wr.Dec<CS.Ask>:
  match r:
    case Wr.Got{a, s}:
      read_finish.failed(f, a, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_finish(r: Wr.Dec<CS.Fact>) -> Wr.Dec<CS.Ask>:
  match r:
    case Wr.Got{f, s}:
      read_finish.ran(f, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_cancel(r: Wr.Dec<CS.Fact>) -> Wr.Dec<CS.Ask>:
  match r:
    case Wr.Got{f, s}:
      Wr.Got{CS.AskCancel{f}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_resume.now(f: CS.Fact, r: Wr.Dec<Nat>) -> Wr.Dec<CS.Ask>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{CS.AskResume{f, n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_resume(r: Wr.Dec<CS.Fact>) -> Wr.Dec<CS.Ask>:
  match r:
    case Wr.Got{f, s}:
      read_resume.now(f, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.tag(t: Nat, s: String) -> Wr.Dec<CS.Ask>:
  match t:
    case 0n:
      read_take(read_fact(s))
    case 1n:
      read_clear(read_who(Wr.get_nat(s)))
    case 2n:
      read_recover(read_fact(s))
    case 3n:
      read_finish(read_fact(s))
    case 4n:
      read_cancel(read_fact(s))
    case 5n:
      read_resume(read_fact(s))
    case 6n+p:
      Wr.Bad{}

def read_ask.go(r: Wr.Dec<Nat>) -> Wr.Dec<CS.Ask>:
  match r:
    case Wr.Got{t, s}:
      read_ask.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.end(whole: Bool, a: CS.Ask) -> Maybe<&2, CS.Ask>:
  match whole:
    case True{}:
      Some{a}
    case False{}:
      None{}

def read_ask.whole(r: Wr.Dec<CS.Ask>) -> Maybe<&2, CS.Ask>:
  match r:
    case Wr.Got{a, s}:
      read_ask.end(Wr.end(s), a)
    case Wr.Bad{}:
      None{}

# the request s is, when s is exactly one request
def read_ask(s: String) -> Maybe<&2, CS.Ask>:
  read_ask.whole(read_ask.go(Wr.get_nat(s)))

# The model's job as the store keeps it
# -------------------------------------
# A model job (bend/cron.bend, minutes) on a clock of unit u: its facts
# as Rust gathers them, and its view: status, next run, failures in a row
# and claim on record (times in units u). An answer's view is what the
# job becomes when Rust applies the answer.

def scale_opt(m: Maybe<&2, Nat>, +u: Nat) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{n}:
      Some{Nat.mul(n, u)}

def scale_claim(cl: Maybe<&2, Cr.Claim>, +u: Nat) -> Maybe<&2, Cr.Claim>:
  match cl:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Cr.Claim{o, w}:
          Some{Cr.Claim{Nat.mul(o, u), w}}

def plan_of(s: Cr.Sched, +u: Nat) -> CS.Plan:
  match s:
    case Cr.Once{d}:
      CS.POnce{}
    case Cr.Every{k}:
      CS.PEvery{Nat.mul(1n+k, u)}

# the facts Rust reads of a model job
def fact_of(j: Cr.Job, +u: Nat) -> CS.Fact:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      CS.Fact{st, plan_of(s, u), scale_opt(nx, u), k}

def claimed_of(j: Cr.Job) -> Bool:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match cl:
        case None{}:
          False{}
        case Some{x}:
          True{}

def View() -> Type:
  Cr.Status & (CS.Next & (Nat & Maybe<&2, Cr.Claim>))

# the view of a model job
def view(j: Cr.Job, +u: Nat) -> View():
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      (st, (CronStore.next_of_spec(scale_opt(nx, u)), (k, scale_claim(cl, u))))

# the claim a claim pass puts on record: the occurrence it starts (the
# next run it was due at) and the process p that runs it
def claim_new(m: Maybe<&2, Nat>, +p: Nat) -> Maybe<&2, Cr.Claim>:
  match m:
    case None{}:
      None{}
    case Some{n}:
      Some{Cr.Claim{n, p}}

# a claim pass of p, applied
def took_view(t: CS.Took, j: Cr.Job, +p: Nat, +u: Nat) -> View():
  match t:
    case CS.Keep{}:
      view(j, u)
    case CS.Roll{n}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          (st, (n, (k, scale_claim(cl, u))))
    case CS.Claimed{n}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          (st, (n, (k, claim_new(scale_opt(nx, u), p))))

def claim_after(cleared: Bool, cl: Maybe<&2, Cr.Claim>) -> Maybe<&2, Cr.Claim>:
  match cleared:
    case True{}:
      None{}
    case False{}:
      cl

# whose the claim of o is to p, with the runs rs of the job and the dead
# processes
def who_of.pick(own: Bool, +p: Nat, +o: Nat, rs: List<&2, Nat>, dead: List<&2, Nat>) -> CS.Who:
  match own:
    case True{}:
      CS.Mine{Cr.has(p, rs)}
    case False{}:
      CS.Theirs{Cr.has(o, dead)}

# whether a recovery of p clears the job's claim, by the verdict on it
def cleared_of(+p: Nat, +dead: List<&2, Nat>, j: Cr.Job) -> Bool:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match cl:
        case None{}:
          False{}
        case Some{x}:
          match x:
            case Cr.Claim{oc, +o}:
              CronStore.clear_spec(who_of.pick(Nat.is_eq(o, p), p, o, rs, dead))

# a recovery, applied: the claim goes when its verdict clears it
def back_view(b: CS.Back, cleared: Bool, j: Cr.Job, +u: Nat) -> View():
  match b:
    case CS.Kept{}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          (st, (CronStore.next_of_spec(scale_opt(nx, u)), (k, claim_after(cleared, scale_claim(cl, u)))))
    case CS.Interrupted{st2, m}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          (st2, (CronStore.next_of_spec(m), (k, claim_after(cleared, scale_claim(cl, u)))))

def ran_of(o: Cr.Out) -> Bool:
  match o:
    case Cr.Win{}:
      True{}
    case Cr.Loss{}:
      True{}
    case Cr.Skip{}:
      False{}

def failed_of(o: Cr.Out) -> Bool:
  match o:
    case Cr.Win{}:
      False{}
    case Cr.Loss{}:
      True{}
    case Cr.Skip{}:
      False{}

# a finish step, applied: its claim goes either way
def fin_view(x: CS.Fin, j: Cr.Job, +u: Nat) -> View():
  match x:
    case CS.Untouched{}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          (st, (CronStore.next_of_spec(scale_opt(nx, u)), (k, None{})))
    case CS.Ran{st2, n, k2}:
      (st2, (n, (k2, None{})))
    case CS.Skipped{st2, n, k2}:
      (st2, (n, (k2, None{})))

# a cancel, applied
def cut_view(x: CS.Cut, j: Cr.Job, +u: Nat) -> View():
  match x:
    case CS.Same{}:
      view(j, u)
    case CS.Cut{st2, m}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          (st2, (CronStore.next_of_spec(m), (k, scale_claim(cl, u))))

# a resume, applied
def again_view(x: CS.Again, j: Cr.Job, +u: Nat) -> View():
  match x:
    case CS.Resumed{st2, n, k2}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          (st2, (n, (k2, scale_claim(cl, u))))
    case CS.Ended{}:
      view(j, u)
    case CS.NotRecurring{}:
      view(j, u)

def runs_of(j: Cr.Job) -> List<&2, Nat>:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      rs

# Laws
# ----

# LAW cron_entry_answers: on every request Rust writes whose numbers fit the wire, the entry answers the spec's decision on the store's clock (a minute is 60000 ms): a claim pass, a claim's verdict, a recovery, a finish step, a cancel or a resume
law cron_entry_answers:
  for +a: CS.Ask
  for fits: {ask_fits(a) == True{} : Bool}
  {FC.ffi(spell_ask(a)) == spell_answer(a) : String}

# LAW cron_entry_malformed_exact: every input that is not exactly one request (input left over after it included) gets exactly the error form 'E ', then "cron: malformed request"
law cron_entry_malformed_exact:
  for +s: String
  for no: {read_ask(s) == None{} : Maybe<&2, CS.Ask>}
  {FC.ffi(s) == SCon{'E', SCon{' ', "cron: malformed request"}} : String}

# LAW cron_entry_example: anchor: the strings Rust sends, with small times (the proven kernel unfolds numbers one by one, so no anchor here runs the failure pause, a count of minutes times 60000 ms: cron_finish_exact pins it for every unit, cron_entry_answers at the entry's minute): a due unclaimed interval job is claimed, an eighth failure stops the job, an own claim no longer run is cleared, a recovered one-shot is finished, a skip rolls the interval, a cancelled job stays, a one-shot does not resume, a rule's resume asks for its next match; a request with input left over is refused
law cron_entry_example:
  {FC.ffi("0,0,1,6,1,10,0,F10,10,") == "2,1,16," : String} &
  {FC.ffi("3,0,1,6,1,10,7,TT50,") == "1,1,0,8," : String} &
  {FC.ffi("1,0,F") == "T" : String} &
  {FC.ffi("2,0,0,1,5,0,T") == "1,2,0," : String} &
  {FC.ffi("3,0,1,6,1,10,0,FF50,") == "2,0,1,56,0," : String} &
  {FC.ffi("4,3,0,0,0,") == "0," : String} &
  {FC.ffi("5,0,0,0,0,9,") == "2," : String} &
  {FC.ffi("5,1,2,0,7,9,") == "0,0,2,0," : String} &
  {read_ask("0,0,1,6,1,10,0,F10,10,x") == None{} : Maybe<&2, CS.Ask>} &
  {FC.ffi("0,0,1,6,1,10,0,F10,10,x") == "E cron: malformed request" : String}

# LAW cron_entry_fits_example: anchor: a request whose numbers fit the wire exists, so cron_entry_answers speaks of something
law cron_entry_fits_example:
  exs a: CS.Ask
  {ask_fits(a) == True{} : Bool}

# LAW cron_take_refines: on a clock of any unit u, a claim pass of p, applied to a model job (its facts as Rust reads them, due by and at the clock), is the model's claim step of p (Cr.take): the same status, next run, failures in a row and claim on record
law cron_take_refines:
  for +v: Nat
  for +p: Nat
  for +c: Nat
  for +j: Cr.Job
  {took_view(CronStore.take_spec(fact_of(j, 1n+v), claimed_of(j), Nat.mul(c, 1n+v), Nat.mul(c, 1n+v)), j, p, 1n+v) == view(Cr.take(p, c, j), 1n+v) : View()}

# LAW cron_recover_refines: on a clock of any unit u, a recovery of a live process p (the verdict on the job's claim from whose it is, whether p still runs it and whether its owner is dead), applied to a model job, is the model's recovery step of p (Cr.recover)
law cron_recover_refines:
  for +v: Nat
  for +p: Nat
  for +dead: List<&2, Nat>
  for +j: Cr.Job
  for alive: {Cr.has(p, dead) == False{} : Bool}
  {back_view(CronStore.recover_spec(fact_of(j, 1n+v), cleared_of(p, dead, j)), cleared_of(p, dead, j), j, 1n+v) == view(Cr.recover(p, dead, j), 1n+v) : View()}

# LAW cron_finish_refines: on a clock of any unit u, the finish step of p's run of a model job whose claim p holds (a good run: ran, not failed; a failure: ran and failed; a skip: neither), applied, is the model's finish step (Cr.finish)
law cron_finish_refines:
  for +v: Nat
  for +p: Nat
  for +c: Nat
  for +o: Cr.Out
  for +x: Nat
  for +j: Cr.Job
  for run: {Cr.has(p, runs_of(j)) == True{} : Bool}
  for own: {Cr.Job.claim(j) == Some{Cr.Claim{x, p}} : Maybe<&2, Cr.Claim>}
  {fin_view(CronStore.finish_spec(1n+v, fact_of(j, 1n+v), ran_of(o), failed_of(o), Nat.mul(c, 1n+v)), j, 1n+v) == view(Cr.finish(p, c, o, j), 1n+v) : View()}

# LAW cron_cancel_refines: on a clock of any unit u, a cancel applied to a model job is the model's cancel (Cr.cancel)
law cron_cancel_refines:
  for +v: Nat
  for +j: Cr.Job
  {cut_view(CronStore.cancel_spec(fact_of(j, 1n+v)), j, 1n+v) == view(Cr.cancel(j), 1n+v) : View()}

# LAW cron_resume_refines: on a clock of any unit u, a resume at the clock applied to a model job is the model's resume (Cr.resume)
law cron_resume_refines:
  for +v: Nat
  for +c: Nat
  for +j: Cr.Job
  {again_view(CronStore.resume_spec(fact_of(j, 1n+v), Nat.mul(c, 1n+v)), j, 1n+v) == view(Cr.resume(c, j), 1n+v) : View()}
