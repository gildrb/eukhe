# cron_serve: every update of the cron job store (`AgentCronJobStore`,
# crates/eukhe-core/src/cron/store/) as one function the Rust host runs,
# Bank style: the jobs file is the state, each update is one event, and
# this function decides the whole new file. The host takes the file's lock,
# reads the file (missing, unreadable, or its records), numbers what the
# decisions compare (job ids and claim owners, by first appearance), calls
# `serve` through the stepper bend/ffi_cron_serve.bend, then does what the
# answer says: moves an unreadable file aside, writes each record as the
# answer gives it (in the answer's order), or writes nothing.
#
# The per-job decisions are bend/cron_store.bend's (laws/cron_store.bend
# pins them; laws/cron.bend ties each to the model's step,
# `cron_*_refines`). This file decides the rest the model bend/cron.bend
# states: which jobs a claim pass claims (a due active job with no claim on
# record, at most one claim per job), whose claims a recovery clears (this
# process's own that it no longer runs, a dead owner's), which claim and
# job a finish step settles (only this process's own run), which records
# a cancel or a resume changes, that an unreadable file is moved aside
# before any write and the update starts from an empty file, and that
# every record this build cannot read stays where it is.
#
# The process's live runs are its state: the dispatch ids this process
# runs now. A claim adds the dispatches it makes; a finish of its own run,
# or the run's end (the host's guard drops), removes one.

import Base
import ./cron.bend as Cr
import ./cron_store.bend as CS

# The file
# --------

# a job record: one this build reads (its id as the host numbered it, and
# the facts the decisions read) or one it cannot read
type JRec is Data:
  JKnown{id: Nat, f: CS.Fact}
  JRaw{}

# a claim record: one this build reads (its dispatch id, its job's id and
# its owner, as the host numbered them) or one it cannot read
type CRec is Data:
  CKnown{d: String, job: Nat, owner: Nat}
  CRaw{}

# the jobs file as an update reads it: missing, there but unreadable (torn,
# not JSON, lists that are not lists), or its job and claim records in
# file order
type Disk is Data:
  Missing{}
  Torn{}
  Parsed{jobs: List<&2, JRec>, claims: List<&2, CRec>}

# The update
# ----------

# what the host asks, with the facts it gathered: a claim pass at `now`
# over the jobs due by `due`, with fresh dispatch ids to use in order; a
# recovery, with the claim owners on record that are dead; the finish of
# the run of dispatch d (ran or skipped, failed or not); a cancel or a
# resume of job `job`; a new job record `f` with the fresh id `job`
type Op is Data:
  OClaim{due: Nat, now: Nat, fresh: List<&2, String>}
  ORecover{dead: List<&2, Nat>}
  OFinish{d: String, ran: Bool, failed: Bool, now: Nat}
  OCancel{job: Nat}
  OResume{job: Nat, now: Nat}
  OCreate{job: Nat, f: CS.Fact}

# The answer
# ----------

# what a job record of the file becomes, in file order: kept as read, or
# what the decision on it answers; a new job record goes last
type JOut is Data:
  JSame{}
  JTook{t: CS.Took}
  JBack{b: CS.Back}
  JFin{x: CS.Fin}
  JCut{x: CS.Cut}
  JAgain{x: CS.Again}
  JNew{}

# what a claim record becomes, in file order: kept or dropped; a new claim
# (of the job record at position k, dispatch d, owned by this process)
# goes after them
type COut is Data:
  CKeep{}
  CDrop{}
  CNew{k: Nat, d: String}

# move the unreadable file aside first; write the records (else leave the
# file as it is); the job records; the claim records
type Out is Data:
  Out{aside: Bool, write: Bool, jobs: List<&2, JOut>, claims: List<&2, COut>}

# the process's runs after the update, and the answer
type Served is Data:
  Served{runs: List<&2, String>, out: Out}

# Small parts
# -----------

# d is in xs
def has_str(+d: String, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(String.eq(x, d), has_str(d, t))

def drop_str.put(b: Bool, x: String, r: List<&2, String>) -> List<&2, String>:
  match b:
    case True{}:
      r
    case False{}:
      x <> r

# xs without d
def drop_str(+d: String, xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      drop_str.put(String.eq(x, d), x, drop_str(d, t))

# every job record kept as read
def same(js: List<&2, JRec>) -> List<&2, JOut>:
  match js:
    case Nil{}:
      Nil{}
    case r <> t:
      JSame{} <> same(t)

# every claim record kept
def keep(cs: List<&2, CRec>) -> List<&2, COut>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      CKeep{} <> keep(t)

# the job ids of the known claims in cs
def claim_jobs(cs: List<&2, CRec>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      match c:
        case CKnown{d, j, o}:
          j <> claim_jobs(t)
        case CRaw{}:
          claim_jobs(t)

# whether a record's answer changes the file
def jout_moves(o: JOut) -> Bool:
  match o:
    case JSame{}:
      False{}
    case JTook{t}:
      match t:
        case CS.Keep{}:
          False{}
        case CS.Roll{n}:
          True{}
        case CS.Claimed{n}:
          True{}
    case JBack{b}:
      match b:
        case CS.Kept{}:
          False{}
        case CS.Interrupted{st, n}:
          True{}
    case JFin{x}:
      match x:
        case CS.Untouched{}:
          False{}
        case CS.Ran{st, n, k}:
          True{}
        case CS.Skipped{st, n, k}:
          True{}
    case JCut{x}:
      match x:
        case CS.Same{}:
          False{}
        case CS.Cut{st, n}:
          True{}
    case JAgain{x}:
      match x:
        case CS.Resumed{st, n, k}:
          True{}
        case CS.Ended{}:
          False{}
        case CS.NotRecurring{}:
          False{}
    case JNew{}:
      True{}

def jouts_move(os: List<&2, JOut>) -> Bool:
  match os:
    case Nil{}:
      False{}
    case o <> t:
      Bool.or(jout_moves(o), jouts_move(t))

def couts_move(os: List<&2, COut>) -> Bool:
  match os:
    case Nil{}:
      False{}
    case o <> t:
      match o:
        case CKeep{}:
          couts_move(t)
        case CDrop{}:
          True{}
        case CNew{k, d}:
          True{}

# the answer: the file is written when a record changes
def out(aside: Bool, +jo: List<&2, JOut>, +co: List<&2, COut>) -> Out:
  Out{aside, Bool.or(jouts_move(jo), couts_move(co)), jo, co}

# A claim pass
# ------------

# the job records' answers, the new claims and their dispatch ids
type Pass is Data:
  Pass{jobs: List<&2, JOut>, news: List<&2, COut>, ds: List<&2, String>}

# a due job is claimed when a fresh dispatch id is left
def claim.takes(t: CS.Took, fresh: List<&2, String>) -> Bool:
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

# the answer of a job record: with no fresh id left a due job stays as read
def claim.out(t: CS.Took, fresh: List<&2, String>) -> JOut:
  match t:
    case CS.Keep{}:
      JTook{CS.Keep{}}
    case CS.Roll{n}:
      JTook{CS.Roll{n}}
    case CS.Claimed{n}:
      match fresh:
        case Nil{}:
          JSame{}
        case d <> r:
          JTook{CS.Claimed{n}}

def claim.set(b: Bool, +i: Nat, set: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      i <> set
    case False{}:
      set

def claim.rest(b: Bool, fresh: List<&2, String>) -> List<&2, String>:
  match b:
    case True{}:
      match fresh:
        case Nil{}:
          Nil{}
        case d <> r:
          r
    case False{}:
      fresh

def claim.put(o: JOut, p: Pass) -> Pass:
  match p:
    case Pass{jo, cn, ds}:
      Pass{o <> jo, cn, ds}

def claim.new(+k: Nat, +d: String, o: JOut, p: Pass) -> Pass:
  match p:
    case Pass{jo, cn, ds}:
      Pass{o <> jo, CNew{k, d} <> cn, d <> ds}

def claim.add(b: Bool, +k: Nat, fresh: List<&2, String>, o: JOut, p: Pass) -> Pass:
  match b:
    case True{}:
      match fresh:
        case Nil{}:
          claim.put(o, p)
        case d <> r:
          claim.new(k, d, o, p)
    case False{}:
      claim.put(o, p)

# the job records from position k: a due active job with no claim on
# record (none read, none made in this pass) is claimed with the next fresh
# dispatch id (CS.take)
def claim(js: List<&2, JRec>, +k: Nat, +set: List<&2, Nat>, +fresh: List<&2, String>, +due: Nat, +now: Nat) -> Pass:
  match js:
    case Nil{}:
      Pass{Nil{}, Nil{}, Nil{}}
    case r <> t:
      match r:
        case JRaw{}:
          claim.put(JSame{}, claim(t, 1n+k, set, fresh, due, now))
        case JKnown{+i, f}:
          +tk = CS.take(f, Cr.has(i, set), due, now)
          +b = claim.takes(tk, fresh)
          claim.add(b, k, fresh, claim.out(tk, fresh), claim(t, 1n+k, claim.set(b, i, set), claim.rest(b, fresh), due, now))

def claim.end(aside: Bool, +runs: List<&2, String>, cs: List<&2, CRec>, p: Pass) -> Served:
  match p:
    case Pass{jo, cn, ds}:
      Served{List.append(&2, String, ds, runs), out(aside, jo, List.append(&2, COut, keep(cs), cn))}

# A recovery
# ----------

def who(own: Bool, +d: String, +o: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>) -> CS.Who:
  match own:
    case True{}:
      CS.Mine{has_str(d, runs)}
    case False{}:
      CS.Theirs{Cr.has(o, dead)}

# a recovery of process me clears the known claim c (CS.clear): its own
# claim that it no longer runs, a dead owner's
def clears(+me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, c: CRec) -> Bool:
  match c:
    case CKnown{+d, j, +o}:
      CS.clear(who(Nat.is_eq(o, me), d, o, runs, dead))
    case CRaw{}:
      False{}

def cleared.pick(b: Bool, +j: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      j <> r
    case False{}:
      r

# the job ids of the claims a recovery clears
def cleared(+me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, cs: List<&2, CRec>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> t:
      match c:
        case CKnown{+d, +j, +o}:
          cleared.pick(clears(me, runs, dead, CKnown{d, j, o}), j, cleared(me, runs, dead, t))
        case CRaw{}:
          cleared(me, runs, dead, t)

def recover.claim(b: Bool) -> COut:
  match b:
    case True{}:
      CDrop{}
    case False{}:
      CKeep{}

def recover.claims(+me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, cs: List<&2, CRec>) -> List<&2, COut>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> t:
      recover.claim(clears(me, runs, dead, c)) <> recover.claims(me, runs, dead, t)

# every known job records whether its claim was cleared (CS.recover)
def recover.jobs(+ids: List<&2, Nat>, js: List<&2, JRec>) -> List<&2, JOut>:
  match js:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case JRaw{}:
          JSame{} <> recover.jobs(ids, t)
        case JKnown{+i, f}:
          JBack{CS.recover(f, Cr.has(i, ids))} <> recover.jobs(ids, t)

# The finish step
# ---------------

# a known claim's job and owner
type Hit is Data:
  Hit{job: Nat, owner: Nat}

def claim_of.pick(b: Bool, j: Nat, o: Nat, r: Maybe<&2, Hit>) -> Maybe<&2, Hit>:
  match b:
    case True{}:
      Some{Hit{j, o}}
    case False{}:
      r

# the job and owner of the first known claim of dispatch d
def claim_of(+d: String, cs: List<&2, CRec>) -> Maybe<&2, Hit>:
  match cs:
    case Nil{}:
      None{}
    case c <> t:
      match c:
        case CKnown{+x, j, o}:
          claim_of.pick(String.eq(x, d), j, o, claim_of(d, t))
        case CRaw{}:
          claim_of(d, t)

def drop_first.pick(b: Bool, t: List<&2, CRec>, r: List<&2, COut>) -> List<&2, COut>:
  match b:
    case True{}:
      CDrop{} <> keep(t)
    case False{}:
      CKeep{} <> r

# the first known claim of dispatch d dropped, every other kept
def drop_first(+d: String, cs: List<&2, CRec>) -> List<&2, COut>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> +t:
      match c:
        case CKnown{x, j, o}:
          drop_first.pick(String.eq(x, d), t, drop_first(d, t))
        case CRaw{}:
          CKeep{} <> drop_first(d, t)

def finish.pick(b: Bool, a: JOut) -> JOut:
  match b:
    case True{}:
      a
    case False{}:
      JSame{}

# every known job of id j counts the result (CS.finish on the store's clock)
def finish.jobs(+j: Nat, +ran: Bool, +failed: Bool, +now: Nat, js: List<&2, JRec>) -> List<&2, JOut>:
  match js:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case JRaw{}:
          JSame{} <> finish.jobs(j, ran, failed, now, t)
        case JKnown{+i, f}:
          finish.pick(Nat.is_eq(i, j), JFin{CS.finish(CS.MINUTE(), f, ran, failed, now)}) <> finish.jobs(j, ran, failed, now, t)

def finish.own(own: Bool, aside: Bool, +j: Nat, +d: String, ran: Bool, failed: Bool, now: Nat, +js: List<&2, JRec>, +cs: List<&2, CRec>) -> Out:
  match own:
    case True{}:
      out(aside, finish.jobs(j, ran, failed, now, js), drop_first(d, cs))
    case False{}:
      Out{aside, False{}, same(js), keep(cs)}

def finish.found(m: Maybe<&2, Hit>, +me: Nat, aside: Bool, +d: String, ran: Bool, failed: Bool, now: Nat, +js: List<&2, JRec>, +cs: List<&2, CRec>) -> Out:
  match m:
    case None{}:
      Out{aside, False{}, same(js), keep(cs)}
    case Some{p}:
      match p:
        case Hit{j, +o}:
          finish.own(Nat.is_eq(o, me), aside, j, d, ran, failed, now, js, cs)

# the finish of this process's run of dispatch d: the run ends; its claim,
# when this process owns it, goes, and its job counts the result; a
# dispatch this process does not run changes nothing
def finish(run: Bool, +me: Nat, +runs: List<&2, String>, aside: Bool, +d: String, ran: Bool, failed: Bool, now: Nat, +js: List<&2, JRec>, +cs: List<&2, CRec>) -> Served:
  match run:
    case True{}:
      Served{drop_str(d, runs), finish.found(claim_of(d, cs), me, aside, d, ran, failed, now, js, cs)}
    case False{}:
      Served{runs, Out{aside, False{}, same(js), keep(cs)}}

# User actions
# ------------

def cancel.jobs(+n: Nat, js: List<&2, JRec>) -> List<&2, JOut>:
  match js:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case JRaw{}:
          JSame{} <> cancel.jobs(n, t)
        case JKnown{+i, f}:
          finish.pick(Nat.is_eq(i, n), JCut{CS.cancel(f)}) <> cancel.jobs(n, t)

def resume.jobs(+n: Nat, +now: Nat, js: List<&2, JRec>) -> List<&2, JOut>:
  match js:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case JRaw{}:
          JSame{} <> resume.jobs(n, now, t)
        case JKnown{+i, f}:
          finish.pick(Nat.is_eq(i, n), JAgain{CS.resume(f, now)}) <> resume.jobs(n, now, t)

# One update
# ----------

def go(+runs: List<&2, String>, +me: Nat, aside: Bool, +js: List<&2, JRec>, +cs: List<&2, CRec>, op: Op) -> Served:
  match op:
    case OClaim{due, now, fresh}:
      claim.end(aside, runs, cs, claim(js, 0n, claim_jobs(cs), fresh, due, now))
    case ORecover{+dead}:
      Served{runs, out(aside, recover.jobs(cleared(me, runs, dead, cs), js), recover.claims(me, runs, dead, cs))}
    case OFinish{+d, ran, failed, now}:
      finish(has_str(d, runs), me, runs, aside, d, ran, failed, now, js, cs)
    case OCancel{n}:
      Served{runs, out(aside, cancel.jobs(n, js), keep(cs))}
    case OResume{n, now}:
      Served{runs, out(aside, resume.jobs(n, now, js), keep(cs))}
    case OCreate{n, f}:
      Served{runs, out(aside, List.append(&2, JOut, same(js), [JNew{}]), keep(cs))}

# the update op of process me (its runs `runs`) on the file as read: an
# unreadable file is moved aside and the update starts from an empty file
def serve(+runs: List<&2, String>, +me: Nat, disk: Disk, op: Op) -> Served:
  match disk:
    case Missing{}:
      go(runs, me, False{}, Nil{}, Nil{}, op)
    case Torn{}:
      go(runs, me, True{}, Nil{}, Nil{}, op)
    case Parsed{js, cs}:
      go(runs, me, False{}, js, cs, op)

# the end of the run of dispatch d (its guard dropped): it is no longer run
def end(+d: String, runs: List<&2, String>) -> List<&2, String>:
  drop_str(d, runs)

# The due question
# ----------------

def due.took(t: CS.Took) -> Bool:
  match t:
    case CS.Keep{}:
      False{}
    case CS.Roll{n}:
      True{}
    case CS.Claimed{n}:
      True{}

# a job is due at now: a claim pass at now would claim it or roll its next
# run (CS.take)
def due(f: CS.Fact, +now: Nat) -> Bool:
  due.took(CS.take(f, False{}, now, now))
