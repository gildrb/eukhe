# eukhe: the laws of area cron_serve: the store's updates, one by one

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_serve.bend as Sv
import ../cron_store.bend as CronStore

# (D2.3) The updates of the jobs file, as compiled Bend
# ----------------------------------------------------
# docs/state.md D2. The Rust store (crates/eukhe-core/src/cron/store/) is
# an event loop with no policy: under a jobs file's lock it reads the file,
# numbers the job ids and claim owners (this process included), and asks
# the stepper bend/ffi_cron_serve.bend what the whole new file is
# (bend/cron_serve.bend `serve`): every record's answer in file order, the
# claims to drop and to make, whether the unreadable file moves aside
# first, whether to write. The process's runs (the dispatch ids it runs
# now) are the stepper's state. These laws pin `serve` on every file, every
# runs, every process and every update: the spec below states it on its
# own, with the per-job decisions of laws/cron_store.bend (each tied to
# the model's step: laws/cron.bend `cron_*_refines`), and the laws after it
# state what no update breaks.

# Terms
# -----

# d is one of xs (String.eq is equality)
def sv_in(+d: String, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(String.eq(x, d), sv_in(d, t))

def sv_out.pick(b: Bool, x: String, r: List<&2, String>) -> List<&2, String>:
  match b:
    case True{}:
      r
    case False{}:
      x <> r

# xs without any d
def sv_out(+d: String, xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      sv_out.pick(String.eq(x, d), x, sv_out(d, t))

# n is one of xs
def sv_has(+n: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(Nat.is_eq(x, n), sv_has(n, t))

# every job record kept as read; every claim record kept
def sv_same(js: List<&2, Sv.JRec>) -> List<&2, Sv.JOut>:
  match js:
    case Nil{}:
      Nil{}
    case r <> t:
      Sv.JSame{} <> sv_same(t)

def sv_keep(cs: List<&2, Sv.CRec>) -> List<&2, Sv.COut>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      Sv.CKeep{} <> sv_keep(t)

# the job ids of the known claims on record, in file order
def sv_taken(cs: List<&2, Sv.CRec>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      match c:
        case Sv.CKnown{d, j, o}:
          j <> sv_taken(t)
        case Sv.CRaw{}:
          sv_taken(t)

# a record's answer changes the file: anything but kept as read, not due,
# kept (recovery), untouched (finish), already cancelled, nothing to resume
def sv_moves(o: Sv.JOut) -> Bool:
  match o:
    case Sv.JSame{}:
      False{}
    case Sv.JTook{t}:
      match t:
        case CS.Keep{}:
          False{}
        case CS.Roll{n}:
          True{}
        case CS.Claimed{n}:
          True{}
    case Sv.JBack{b}:
      match b:
        case CS.Kept{}:
          False{}
        case CS.Interrupted{st, n}:
          True{}
    case Sv.JFin{x}:
      match x:
        case CS.Untouched{}:
          False{}
        case CS.Ran{st, n, k}:
          True{}
        case CS.Skipped{st, n, k}:
          True{}
    case Sv.JCut{x}:
      match x:
        case CS.Same{}:
          False{}
        case CS.Cut{st, n}:
          True{}
    case Sv.JAgain{x}:
      match x:
        case CS.Resumed{st, n, k}:
          True{}
        case CS.Ended{}:
          False{}
        case CS.NotRecurring{}:
          False{}
    case Sv.JNew{}:
      True{}

def sv_jmoves(os: List<&2, Sv.JOut>) -> Bool:
  match os:
    case Nil{}:
      False{}
    case o <> t:
      Bool.or(sv_moves(o), sv_jmoves(t))

def sv_cmoves(os: List<&2, Sv.COut>) -> Bool:
  match os:
    case Nil{}:
      False{}
    case o <> t:
      match o:
        case Sv.CKeep{}:
          sv_cmoves(t)
        case Sv.CDrop{}:
          True{}
        case Sv.CNew{k, d}:
          True{}

# the answer: written exactly when a record changes
def sv_answer(aside: Bool, +jo: List<&2, Sv.JOut>, +co: List<&2, Sv.COut>) -> Sv.Out:
  Sv.Out{aside, Bool.or(sv_jmoves(jo), sv_cmoves(co)), jo, co}

# The claim pass: a due active job (CronStore.take_spec) with no claim on
# record (none read, none made earlier in the pass) is claimed with the
# next fresh dispatch id; with none left it stays as read

def sv_claims(t: CS.Took, fresh: List<&2, String>) -> Bool:
  match t:
    case CS.Keep{}:
      False{}
    case CS.Roll{n}:
      False{}
    case CS.Claimed{n}:
      match fresh:
        case Nil{}:
          False{}
        case d <> r:
          True{}

def sv_took(t: CS.Took, fresh: List<&2, String>) -> Sv.JOut:
  match t:
    case CS.Keep{}:
      Sv.JTook{CS.Keep{}}
    case CS.Roll{n}:
      Sv.JTook{CS.Roll{n}}
    case CS.Claimed{n}:
      match fresh:
        case Nil{}:
          Sv.JSame{}
        case d <> r:
          Sv.JTook{CS.Claimed{n}}

def sv_taken_after(b: Bool, +i: Nat, set: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      i <> set
    case False{}:
      set

def sv_fresh_after(b: Bool, fresh: List<&2, String>) -> List<&2, String>:
  match b:
    case True{}:
      match fresh:
        case Nil{}:
          Nil{}
        case d <> r:
          r
    case False{}:
      fresh

def sv_pass_put(o: Sv.JOut, p: Sv.Pass) -> Sv.Pass:
  match p:
    case Sv.Pass{jo, cn, ds}:
      Sv.Pass{o <> jo, cn, ds}

def sv_pass_new(+k: Nat, +d: String, o: Sv.JOut, p: Sv.Pass) -> Sv.Pass:
  match p:
    case Sv.Pass{jo, cn, ds}:
      Sv.Pass{o <> jo, Sv.CNew{k, d} <> cn, d <> ds}

def sv_pass_add(b: Bool, +k: Nat, fresh: List<&2, String>, o: Sv.JOut, p: Sv.Pass) -> Sv.Pass:
  match b:
    case True{}:
      match fresh:
        case Nil{}:
          sv_pass_put(o, p)
        case d <> r:
          sv_pass_new(k, d, o, p)
    case False{}:
      sv_pass_put(o, p)

# the claim pass over the job records from position k
def sv_pass(js: List<&2, Sv.JRec>, +k: Nat, +set: List<&2, Nat>, +fresh: List<&2, String>, +due: Nat, +now: Nat) -> Sv.Pass:
  match js:
    case Nil{}:
      Sv.Pass{Nil{}, Nil{}, Nil{}}
    case r <> t:
      match r:
        case Sv.JRaw{}:
          sv_pass_put(Sv.JSame{}, sv_pass(t, 1n+k, set, fresh, due, now))
        case Sv.JKnown{+i, f}:
          +tk = CronStore.take_spec(f, sv_has(i, set), due, now)
          +b = sv_claims(tk, fresh)
          sv_pass_add(b, k, fresh, sv_took(tk, fresh), sv_pass(t, 1n+k, sv_taken_after(b, i, set), sv_fresh_after(b, fresh), due, now))

def sv_claim_end(aside: Bool, +runs: List<&2, String>, cs: List<&2, Sv.CRec>, p: Sv.Pass) -> Sv.Served:
  match p:
    case Sv.Pass{jo, cn, ds}:
      Sv.Served{List.append(&2, String, ds, runs), sv_answer(aside, jo, List.append(&2, Sv.COut, sv_keep(cs), cn))}

# The recovery: process me clears its own known claim it no longer runs
# and a dead owner's (CronStore.clear_spec); a known job whose claim was
# cleared records it (CronStore.recover_spec)

def sv_who(own: Bool, +d: String, +o: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>) -> CS.Who:
  match own:
    case True{}:
      CS.Mine{sv_in(d, runs)}
    case False{}:
      CS.Theirs{sv_has(o, dead)}

def sv_clears(+me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, c: Sv.CRec) -> Bool:
  match c:
    case Sv.CKnown{+d, j, +o}:
      CronStore.clear_spec(sv_who(Nat.is_eq(o, me), d, o, runs, dead))
    case Sv.CRaw{}:
      False{}

def sv_cleared.pick(b: Bool, +j: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      j <> r
    case False{}:
      r

# the job ids of the claims cleared
def sv_cleared(+me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, cs: List<&2, Sv.CRec>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> t:
      match c:
        case Sv.CKnown{+d, +j, +o}:
          sv_cleared.pick(sv_clears(me, runs, dead, Sv.CKnown{d, j, o}), j, sv_cleared(me, runs, dead, t))
        case Sv.CRaw{}:
          sv_cleared(me, runs, dead, t)

def sv_drop_if(b: Bool) -> Sv.COut:
  match b:
    case True{}:
      Sv.CDrop{}
    case False{}:
      Sv.CKeep{}

def sv_recover_claims(+me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, cs: List<&2, Sv.CRec>) -> List<&2, Sv.COut>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> t:
      sv_drop_if(sv_clears(me, runs, dead, c)) <> sv_recover_claims(me, runs, dead, t)

def sv_recover_jobs(+ids: List<&2, Nat>, js: List<&2, Sv.JRec>) -> List<&2, Sv.JOut>:
  match js:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case Sv.JRaw{}:
          Sv.JSame{} <> sv_recover_jobs(ids, t)
        case Sv.JKnown{+i, f}:
          Sv.JBack{CronStore.recover_spec(f, sv_has(i, ids))} <> sv_recover_jobs(ids, t)

# The finish step: only of a dispatch this process runs; the run ends;
# the first known claim of the dispatch, when this process owns it, is
# dropped and every known job of its id counts the result
# (CronStore.finish_spec on the store's clock, a minute being 60000 ms)

def sv_claim_of.pick(b: Bool, j: Nat, o: Nat, r: Maybe<&2, Sv.Hit>) -> Maybe<&2, Sv.Hit>:
  match b:
    case True{}:
      Some{Sv.Hit{j, o}}
    case False{}:
      r

def sv_claim_of(+d: String, cs: List<&2, Sv.CRec>) -> Maybe<&2, Sv.Hit>:
  match cs:
    case Nil{}:
      None{}
    case c <> t:
      match c:
        case Sv.CKnown{+x, j, o}:
          sv_claim_of.pick(String.eq(x, d), j, o, sv_claim_of(d, t))
        case Sv.CRaw{}:
          sv_claim_of(d, t)

def sv_drop_first.pick(b: Bool, t: List<&2, Sv.CRec>, r: List<&2, Sv.COut>) -> List<&2, Sv.COut>:
  match b:
    case True{}:
      Sv.CDrop{} <> sv_keep(t)
    case False{}:
      Sv.CKeep{} <> r

def sv_drop_first(+d: String, cs: List<&2, Sv.CRec>) -> List<&2, Sv.COut>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> +t:
      match c:
        case Sv.CKnown{x, j, o}:
          sv_drop_first.pick(String.eq(x, d), t, sv_drop_first(d, t))
        case Sv.CRaw{}:
          Sv.CKeep{} <> sv_drop_first(d, t)

def sv_if(b: Bool, a: Sv.JOut) -> Sv.JOut:
  match b:
    case True{}:
      a
    case False{}:
      Sv.JSame{}

def sv_finish_jobs(+j: Nat, +ran: Bool, +failed: Bool, +now: Nat, js: List<&2, Sv.JRec>) -> List<&2, Sv.JOut>:
  match js:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case Sv.JRaw{}:
          Sv.JSame{} <> sv_finish_jobs(j, ran, failed, now, t)
        case Sv.JKnown{+i, f}:
          sv_if(Nat.is_eq(i, j), Sv.JFin{CronStore.finish_spec(60000n, f, ran, failed, now)}) <> sv_finish_jobs(j, ran, failed, now, t)

def sv_finish_own(own: Bool, aside: Bool, +j: Nat, +d: String, ran: Bool, failed: Bool, now: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>) -> Sv.Out:
  match own:
    case True{}:
      sv_answer(aside, sv_finish_jobs(j, ran, failed, now, js), sv_drop_first(d, cs))
    case False{}:
      Sv.Out{aside, False{}, sv_same(js), sv_keep(cs)}

def sv_finish_found(m: Maybe<&2, Sv.Hit>, +me: Nat, aside: Bool, +d: String, ran: Bool, failed: Bool, now: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>) -> Sv.Out:
  match m:
    case None{}:
      Sv.Out{aside, False{}, sv_same(js), sv_keep(cs)}
    case Some{p}:
      match p:
        case Sv.Hit{j, +o}:
          sv_finish_own(Nat.is_eq(o, me), aside, j, d, ran, failed, now, js, cs)

def sv_finish(run: Bool, +me: Nat, +runs: List<&2, String>, aside: Bool, +d: String, ran: Bool, failed: Bool, now: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>) -> Sv.Served:
  match run:
    case True{}:
      Sv.Served{sv_out(d, runs), sv_finish_found(sv_claim_of(d, cs), me, aside, d, ran, failed, now, js, cs)}
    case False{}:
      Sv.Served{runs, Sv.Out{aside, False{}, sv_same(js), sv_keep(cs)}}

# User actions: every known job of the id is cancelled or resumed
# (CronStore.cancel_spec, CronStore.resume_spec); a new job goes last

def sv_cancel_jobs(+n: Nat, js: List<&2, Sv.JRec>) -> List<&2, Sv.JOut>:
  match js:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case Sv.JRaw{}:
          Sv.JSame{} <> sv_cancel_jobs(n, t)
        case Sv.JKnown{+i, f}:
          sv_if(Nat.is_eq(i, n), Sv.JCut{CronStore.cancel_spec(f)}) <> sv_cancel_jobs(n, t)

def sv_resume_jobs(+n: Nat, +now: Nat, js: List<&2, Sv.JRec>) -> List<&2, Sv.JOut>:
  match js:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case Sv.JRaw{}:
          Sv.JSame{} <> sv_resume_jobs(n, now, t)
        case Sv.JKnown{+i, f}:
          sv_if(Nat.is_eq(i, n), Sv.JAgain{CronStore.resume_spec(f, now)}) <> sv_resume_jobs(n, now, t)

def sv_go(+runs: List<&2, String>, +me: Nat, aside: Bool, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>, op: Sv.Op) -> Sv.Served:
  match op:
    case Sv.OClaim{due, now, fresh}:
      sv_claim_end(aside, runs, cs, sv_pass(js, 0n, sv_taken(cs), fresh, due, now))
    case Sv.ORecover{+dead}:
      Sv.Served{runs, sv_answer(aside, sv_recover_jobs(sv_cleared(me, runs, dead, cs), js), sv_recover_claims(me, runs, dead, cs))}
    case Sv.OFinish{+d, ran, failed, now}:
      sv_finish(sv_in(d, runs), me, runs, aside, d, ran, failed, now, js, cs)
    case Sv.OCancel{n}:
      Sv.Served{runs, sv_answer(aside, sv_cancel_jobs(n, js), sv_keep(cs))}
    case Sv.OResume{n, now}:
      Sv.Served{runs, sv_answer(aside, sv_resume_jobs(n, now, js), sv_keep(cs))}
    case Sv.OCreate{n, f}:
      Sv.Served{runs, sv_answer(aside, List.append(&2, Sv.JOut, sv_same(js), [Sv.JNew{}]), sv_keep(cs))}

# the update op of process me with its runs on the file as read: an
# unreadable file is moved aside, and the update runs on an empty file
def sv_serve(+runs: List<&2, String>, +me: Nat, disk: Sv.Disk, op: Sv.Op) -> Sv.Served:
  match disk:
    case Sv.Missing{}:
      sv_go(runs, me, False{}, Nil{}, Nil{}, op)
    case Sv.Torn{}:
      sv_go(runs, me, True{}, Nil{}, Nil{}, op)
    case Sv.Parsed{js, cs}:
      sv_go(runs, me, False{}, js, cs, op)

def sv_due.took(t: CS.Took) -> Bool:
  match t:
    case CS.Keep{}:
      False{}
    case CS.Roll{n}:
      True{}
    case CS.Claimed{n}:
      True{}

# due at now: a claim pass at now (due by now) would claim the job or roll
# its next run
def sv_due(f: CS.Fact, +now: Nat) -> Bool:
  sv_due.took(CronStore.take_spec(f, False{}, now, now))

# Projections

def sv_after(r: Sv.Served) -> List<&2, String>:
  match r:
    case Sv.Served{runs, o}:
      runs

def sv_reply(r: Sv.Served) -> Sv.Out:
  match r:
    case Sv.Served{runs, o}:
      o

def sv_aside(o: Sv.Out) -> Bool:
  match o:
    case Sv.Out{a, w, js, cs}:
      a

def sv_write(o: Sv.Out) -> Bool:
  match o:
    case Sv.Out{a, w, js, cs}:
      w

def sv_jobs(o: Sv.Out) -> List<&2, Sv.JOut>:
  match o:
    case Sv.Out{a, w, js, cs}:
      js

def sv_claims_out(o: Sv.Out) -> List<&2, Sv.COut>:
  match o:
    case Sv.Out{a, w, js, cs}:
      cs

# The shape of an answer

# the answer o fits the job record r: a record this build cannot read is
# kept as read; a known one gets any answer but a new job
def sv_jplace(r: Sv.JRec, o: Sv.JOut) -> Bool:
  match r:
    case Sv.JRaw{}:
      match o:
        case Sv.JSame{}:
          True{}
        case Sv.JTook{x}:
          False{}
        case Sv.JBack{x}:
          False{}
        case Sv.JFin{x}:
          False{}
        case Sv.JCut{x}:
          False{}
        case Sv.JAgain{x}:
          False{}
        case Sv.JNew{}:
          False{}
    case Sv.JKnown{i, f}:
      match o:
        case Sv.JNew{}:
          False{}
        case Sv.JSame{}:
          True{}
        case Sv.JTook{x}:
          True{}
        case Sv.JBack{x}:
          True{}
        case Sv.JFin{x}:
          True{}
        case Sv.JCut{x}:
          True{}
        case Sv.JAgain{x}:
          True{}

# what follows the job records' answers: nothing, or for a create the new
# job alone
def sv_jtail(jo: List<&2, Sv.JOut>, create: Bool) -> Bool:
  match jo:
    case Nil{}:
      Bool.not(create)
    case o <> t:
      match o:
        case Sv.JNew{}:
          Bool.and(create, List.is_empty(&2, Sv.JOut, t))
        case Sv.JSame{}:
          False{}
        case Sv.JTook{x}:
          False{}
        case Sv.JBack{x}:
          False{}
        case Sv.JFin{x}:
          False{}
        case Sv.JCut{x}:
          False{}
        case Sv.JAgain{x}:
          False{}

# the answers keep every record this build cannot read where it is: the
# job answers pair with the job records one by one (a record not read
# with kept-as-read), and only a create adds one, last, the new job
def sv_jobs_placed(js: List<&2, Sv.JRec>, jo: List<&2, Sv.JOut>, create: Bool) -> Bool:
  match js:
    case Nil{}:
      sv_jtail(jo, create)
    case r <> rt:
      match jo:
        case Nil{}:
          False{}
        case o <> ot:
          Bool.and(sv_jplace(r, o), sv_jobs_placed(rt, ot, create))

# only new claims follow the claim records
def sv_all_new(co: List<&2, Sv.COut>) -> Bool:
  match co:
    case Nil{}:
      True{}
    case o <> t:
      match o:
        case Sv.CNew{k, d}:
          sv_all_new(t)
        case Sv.CKeep{}:
          False{}
        case Sv.CDrop{}:
          False{}

# the answer o fits the claim record c: a record this build cannot read is
# kept; a known one is kept or dropped
def sv_cplace(c: Sv.CRec, o: Sv.COut) -> Bool:
  match c:
    case Sv.CRaw{}:
      match o:
        case Sv.CKeep{}:
          True{}
        case Sv.CDrop{}:
          False{}
        case Sv.CNew{k, d}:
          False{}
    case Sv.CKnown{d, j, w}:
      match o:
        case Sv.CKeep{}:
          True{}
        case Sv.CDrop{}:
          True{}
        case Sv.CNew{k, x}:
          False{}

# the claim answers pair with the claim records one by one (a record not
# read is kept), then only new claims follow
def sv_claims_placed(cs: List<&2, Sv.CRec>, co: List<&2, Sv.COut>) -> Bool:
  match cs:
    case Nil{}:
      sv_all_new(co)
    case c <> ct:
      match co:
        case Nil{}:
          False{}
        case o <> ot:
          Bool.and(sv_cplace(c, o), sv_claims_placed(ct, ot))

def sv_is_create(op: Sv.Op) -> Bool:
  match op:
    case Sv.OClaim{due, now, fresh}:
      False{}
    case Sv.ORecover{dead}:
      False{}
    case Sv.OFinish{d, ran, failed, now}:
      False{}
    case Sv.OCancel{n}:
      False{}
    case Sv.OResume{n, now}:
      False{}
    case Sv.OCreate{n, f}:
      True{}

# Claims

# the claim records' answers at position k (None past them)
def sv_at(-A: Data, +k: Nat, xs: List<&2, A>) -> Maybe<&2, A>:
  List.get(&2, A, xs, k)

def sv_stays.own(own: Bool, mine: Bool, theirs: Bool) -> Bool:
  match own:
    case True{}:
      mine
    case False{}:
      theirs

# a claim of owner o and dispatch d stays through the update op of process
# me with the runs: another's claim unless a recovery finds its owner dead,
# this process's own claim of a dispatch it runs unless op is its finish
def sv_stays(+me: Nat, +runs: List<&2, String>, op: Sv.Op, +d: String, +o: Nat) -> Bool:
  match op:
    case Sv.ORecover{dead}:
      sv_stays.own(Nat.is_eq(o, me), sv_in(d, runs), Bool.not(sv_has(o, dead)))
    case Sv.OFinish{x, ran, failed, now}:
      sv_stays.own(Nat.is_eq(o, me), Bool.or(Bool.not(sv_in(d, runs)), Bool.not(String.eq(x, d))), True{})
    case Sv.OClaim{due, now, fresh}:
      True{}
    case Sv.OCancel{n}:
      True{}
    case Sv.OResume{n, now}:
      True{}
    case Sv.OCreate{n, f}:
      True{}

def sv_job_of(m: Maybe<&2, Sv.JRec>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{r}:
      match r:
        case Sv.JKnown{i, f}:
          Some{i}
        case Sv.JRaw{}:
          None{}

# the job id of the known job record at position k
def sv_job_at(js: List<&2, Sv.JRec>, +k: Nat) -> Maybe<&2, Nat>:
  sv_job_of(List.get(&2, Sv.JRec, js, k))

# a new claim of the job m (None: no known job there) is of a job not taken
def sv_new.ok(m: Maybe<&2, Nat>, +taken: List<&2, Nat>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{i}:
      Bool.not(sv_has(i, taken))

def sv_new.add(m: Maybe<&2, Nat>, taken: List<&2, Nat>) -> List<&2, Nat>:
  match m:
    case None{}:
      taken
    case Some{i}:
      i <> taken

# every new claim of co claims a known job none of whose claims is in
# taken (on record or made before it in the answer)
def sv_new_unclaimed(co: List<&2, Sv.COut>, +js: List<&2, Sv.JRec>, +taken: List<&2, Nat>) -> Bool:
  match co:
    case Nil{}:
      True{}
    case o <> t:
      match o:
        case Sv.CKeep{}:
          sv_new_unclaimed(t, js, taken)
        case Sv.CDrop{}:
          sv_new_unclaimed(t, js, taken)
        case Sv.CNew{+k, d}:
          Bool.and(sv_new.ok(sv_job_at(js, k), taken), sv_new_unclaimed(t, js, sv_new.add(sv_job_at(js, k), taken)))

# Laws
# ----

# LAW cron_serve_exact: the update the stepper runs (Sv.serve) is the spec's
# on every runs, process, file (missing, unreadable, or any records) and
# update: every record's answer, the claims dropped and made, the runs after
# EXCLUDES: any decision other than the spec's: a claim of a claimed job or
#   of a job that is not due, a second claim of one job in one pass, a
#   claim with no fresh id, a recovery that clears a live claim or keeps a
#   dead owner's, a finish of another's claim or of another job, a cancel
#   or resume of another job, an unreadable file written over, a record
#   dropped, moved or added, a write of an unchanged file, runs not updated
law cron_serve_exact:
  for +runs: List<&2, String>
  for +me: Nat
  for +disk: Sv.Disk
  for +op: Sv.Op
  {Sv.serve(runs, me, disk, op) == sv_serve(runs, me, disk, op) : Sv.Served}

# LAW cron_serve_end_exact: the end of a run removes its dispatch id, every
# copy, from the runs, and nothing else
# EXCLUDES: a run that stays live after its guard dropped, another run ended
law cron_serve_end_exact:
  for +d: String
  for +runs: List<&2, String>
  {Sv.end(d, runs) == sv_out(d, runs) : List<&2, String>}

# LAW cron_serve_due_exact: a job is due at now exactly when a claim pass
# at now would claim it or roll its next run
# EXCLUDES: a due question answered by another rule than the claim pass's
law cron_serve_due_exact:
  for +f: CS.Fact
  for +now: Nat
  {Sv.due(f, now) == sv_due(f, now) : Bool}

# LAW cron_serve_records_in_place: every update keeps every record this
# build cannot read where it is and in order: the job answers pair with the
# job records one by one (a record not read is kept as read) and only a
# create adds one record, last; the claim answers pair with the claim
# records one by one (a record not read is kept), then only new claims
# EXCLUDES: a record this build cannot read dropped, moved, reordered or
#   changed; a record lost or a stray one added; a new job not last
law cron_serve_records_in_place:
  for +runs: List<&2, String>
  for +me: Nat
  for +js: List<&2, Sv.JRec>
  for +cs: List<&2, Sv.CRec>
  for +op: Sv.Op
  {sv_jobs_placed(js, sv_jobs(sv_reply(Sv.serve(runs, me, Sv.Parsed{js, cs}, op))), sv_is_create(op)) == True{} : Bool} & {sv_claims_placed(cs, sv_claims_out(sv_reply(Sv.serve(runs, me, Sv.Parsed{js, cs}, op)))) == True{} : Bool}

# LAW cron_serve_torn_moved_aside: an unreadable file is moved aside before
# anything is written, and the update runs as on an empty file; a missing
# file is an empty file, and a file that was read is never moved aside
# EXCLUDES: an unreadable file written over or deleted, an update that
#   keeps reading it, a read file moved aside
law cron_serve_torn_moved_aside:
  for +runs: List<&2, String>
  for +me: Nat
  for +js: List<&2, Sv.JRec>
  for +cs: List<&2, Sv.CRec>
  for +op: Sv.Op
  {Sv.serve(runs, me, Sv.Torn{}, op) == Sv.Served{sv_after(Sv.serve(runs, me, Sv.Parsed{Nil{}, Nil{}}, op)), Sv.Out{True{}, sv_write(sv_reply(Sv.serve(runs, me, Sv.Parsed{Nil{}, Nil{}}, op))), sv_jobs(sv_reply(Sv.serve(runs, me, Sv.Parsed{Nil{}, Nil{}}, op))), sv_claims_out(sv_reply(Sv.serve(runs, me, Sv.Parsed{Nil{}, Nil{}}, op)))}} : Sv.Served} & {Sv.serve(runs, me, Sv.Missing{}, op) == Sv.serve(runs, me, Sv.Parsed{Nil{}, Nil{}}, op) : Sv.Served} & {sv_aside(sv_reply(Sv.serve(runs, me, Sv.Parsed{js, cs}, op))) == False{} : Bool}

# LAW cron_serve_live_claim_kept: a known claim of another process stays
# through every update but a recovery that finds its owner dead; this
# process's own claim of a dispatch it runs stays through every update but
# that dispatch's finish
# EXCLUDES: a live claim of another live process cleared (a double
#   dispatch: the job is claimed again while it runs), this process's live
#   claim cleared, a finish that drops another claim
law cron_serve_live_claim_kept:
  for +runs: List<&2, String>
  for +me: Nat
  for +js: List<&2, Sv.JRec>
  for +cs: List<&2, Sv.CRec>
  for +op: Sv.Op
  for +k: Nat
  for +d: String
  for +j: Nat
  for +o: Nat
  for at: {sv_at(Sv.CRec, k, cs) == Some{Sv.CKnown{d, j, o}} : Maybe<&2, Sv.CRec>}
  for stays: {sv_stays(me, runs, op, d, o) == True{} : Bool}
  {sv_at(Sv.COut, k, sv_claims_out(sv_reply(Sv.serve(runs, me, Sv.Parsed{js, cs}, op)))) == Some{Sv.CKeep{}} : Maybe<&2, Sv.COut>}

# LAW cron_serve_dead_claim_cleared: a recovery clears the known claim of
# an owner it finds dead, and this process's own claim of a dispatch it no
# longer runs
# EXCLUDES: a dead process's claim kept forever (its job never runs
#   again), an unwound run's claim kept
law cron_serve_dead_claim_cleared:
  for +runs: List<&2, String>
  for +me: Nat
  for +js: List<&2, Sv.JRec>
  for +cs: List<&2, Sv.CRec>
  for +dead: List<&2, Nat>
  for +k: Nat
  for +d: String
  for +j: Nat
  for +o: Nat
  for at: {sv_at(Sv.CRec, k, cs) == Some{Sv.CKnown{d, j, o}} : Maybe<&2, Sv.CRec>}
  for gone: {sv_stays(me, runs, Sv.ORecover{dead}, d, o) == False{} : Bool}
  {sv_at(Sv.COut, k, sv_claims_out(sv_reply(Sv.serve(runs, me, Sv.Parsed{js, cs}, Sv.ORecover{dead})))) == Some{Sv.CDrop{}} : Maybe<&2, Sv.COut>}

# LAW cron_serve_finish_unknown: the finish of a dispatch this process does
# not run, or of which no known claim is on record, changes no record and
# writes nothing (the run, if any, ends)
# EXCLUDES: a finish applied to another claim or job, a stale finish that
#   counts a result twice
law cron_serve_finish_unknown:
  for +runs: List<&2, String>
  for +me: Nat
  for +js: List<&2, Sv.JRec>
  for +cs: List<&2, Sv.CRec>
  for +d: String
  for +ran: Bool
  for +failed: Bool
  for +now: Nat
  for none: {Bool.and(sv_in(d, runs), Bool.not(Maybe.is_none(&2, Sv.Hit, sv_claim_of(d, cs)))) == False{} : Bool}
  {sv_reply(Sv.serve(runs, me, Sv.Parsed{js, cs}, Sv.OFinish{d, ran, failed, now})) == Sv.Out{False{}, False{}, sv_same(js), sv_keep(cs)} : Sv.Out}

# LAW cron_serve_claims_unclaimed: every claim a claim pass makes claims a
# known job with no known claim on record, and no job twice
# EXCLUDES: a double dispatch in one pass or against a claim on record, a
#   claim of a record this build cannot read, a claim at a stray position
law cron_serve_claims_unclaimed:
  for +runs: List<&2, String>
  for +me: Nat
  for +js: List<&2, Sv.JRec>
  for +cs: List<&2, Sv.CRec>
  for +due: Nat
  for +now: Nat
  for +fresh: List<&2, String>
  {sv_new_unclaimed(sv_claims_out(sv_reply(Sv.serve(runs, me, Sv.Parsed{js, cs}, Sv.OClaim{due, now, fresh}))), js, sv_taken(cs)) == True{} : Bool}

# LAW cron_serve_witness: anchor: the premises of the laws above hold on a
# concrete file, so none is vacuous: another live process's claim and this
# process's running claim stay, a dead owner's claim and an unwound claim
# go, a finish of a dispatch nobody runs is unknown
# EXCLUDES: cron_serve_live_claim_kept, cron_serve_dead_claim_cleared or
#   cron_serve_finish_unknown made vacuous by premises no file meets
law cron_serve_witness:
  {sv_stays(0n, ["a"], Sv.ORecover{[2n]}, "b", 1n) == True{} : Bool} &
  {sv_stays(0n, ["a"], Sv.ORecover{[2n]}, "a", 0n) == True{} : Bool} &
  {sv_stays(0n, ["a"], Sv.ORecover{[2n]}, "c", 2n) == False{} : Bool} &
  {sv_stays(0n, ["a"], Sv.ORecover{[2n]}, "x", 0n) == False{} : Bool} &
  {Bool.and(sv_in("z", ["a"]), Bool.not(Maybe.is_none(&2, Sv.Hit, sv_claim_of("z", [Sv.CKnown{"a", 0n, 0n}])))) == False{} : Bool}
