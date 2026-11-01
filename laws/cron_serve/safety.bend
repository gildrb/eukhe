# eukhe: the laws of area cron_serve: what no order of updates by any
# number of processes breaks

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_serve.bend as Sv
import ./serve.bend as CronServe

# (D2.3) One jobs file, any number of processes
# ---------------------------------------------
# The world: one jobs file shared by any number of processes, the
# processes found dead, and the corrupt files moved aside. Each process
# updates the file with the stepper the entry runs (Sv.serve: the entry's
# step is pinned to it by cron_serve_is_entry), with any runs (so every
# state of every process's stepper is covered), and the store renders the
# answer onto the file as crates/eukhe-core/src/cron/store/serve.rs
# `render` does: every claim answer by its index (kept, dropped, or a new
# claim of the job record at a position, owned by the process, only in a
# claim pass), every job answer by its index (kept as read, or the answer
# on a record it reads; the new job only past the records, only in a
# create), any other answer refused (nothing written); an unreadable file
# moved aside first when the answer says so; written only when the answer
# says so. A recovery asks with the processes the world found dead. Other
# events: a process dies; another writer adds a record this build cannot
# read; any writer changes a job's facts (the decisions' renderings, the
# user's edits: every fact is covered); the file becomes corrupt (not a
# step of ours). The laws hold for every event, from every world (the
# per-event laws), or after any events from the empty world.
#
# A record this build cannot read carries its bytes `t` here, so the laws
# can say it is kept byte for byte; a corrupt file carries its bytes.

# The world
# ---------

type SfJ is Data:
  SfJK{i: Nat, f: CS.Fact}
  SfJR{t: Nat}

type SfC is Data:
  SfCK{d: String, j: Nat, o: Nat}
  SfCR{t: Nat}

type SfFile is Data:
  SfMissing{}
  SfTorn{t: Nat}
  SfRead{js: List<&2, SfJ>, cs: List<&2, SfC>}

type SfWorld is Data:
  SfWorld{file: SfFile, dead: List<&2, Nat>, aside: List<&2, Nat>}

# events, the newest first in a run
type SfEv is Data:
  SfUp{p: Nat, runs: List<&2, String>, op: Sv.Op}
  SfDie{p: Nat}
  SfRawJob{t: Nat}
  SfRawClaim{t: Nat}
  SfFacts{k: Nat, f: CS.Fact}
  SfCorrupt{t: Nat}

def sf_empty() -> SfWorld:
  SfWorld{SfMissing{}, Nil{}, Nil{}}

# What an update reads
# --------------------

def sf_pj(r: SfJ) -> Sv.JRec:
  match r:
    case SfJK{i, f}:
      Sv.JKnown{i, f}
    case SfJR{t}:
      Sv.JRaw{}

def sf_pjs(js: List<&2, SfJ>) -> List<&2, Sv.JRec>:
  match js:
    case Nil{}:
      Nil{}
    case r <> t:
      sf_pj(r) <> sf_pjs(t)

def sf_pc(c: SfC) -> Sv.CRec:
  match c:
    case SfCK{d, j, o}:
      Sv.CKnown{d, j, o}
    case SfCR{t}:
      Sv.CRaw{}

def sf_pcs(cs: List<&2, SfC>) -> List<&2, Sv.CRec>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      sf_pc(c) <> sf_pcs(t)

def sf_disk(f: SfFile) -> Sv.Disk:
  match f:
    case SfMissing{}:
      Sv.Missing{}
    case SfTorn{t}:
      Sv.Torn{}
    case SfRead{js, cs}:
      Sv.Parsed{sf_pjs(js), sf_pcs(cs)}

# the records an update renders its answer onto (none when the file is
# missing or unreadable)
def sf_jobs(f: SfFile) -> List<&2, SfJ>:
  match f:
    case SfMissing{}:
      Nil{}
    case SfTorn{t}:
      Nil{}
    case SfRead{js, cs}:
      js

def sf_claims_of(f: SfFile) -> List<&2, SfC>:
  match f:
    case SfMissing{}:
      Nil{}
    case SfTorn{t}:
      Nil{}
    case SfRead{js, cs}:
      cs

# a recovery asks with the processes the world found dead
def sf_op(op: Sv.Op, dead: List<&2, Nat>) -> Sv.Op:
  match op:
    case Sv.OClaim{due, now, fresh}:
      Sv.OClaim{due, now, fresh}
    case Sv.ORecover{x}:
      Sv.ORecover{dead}
    case Sv.OFinish{d, ran, failed, now}:
      Sv.OFinish{d, ran, failed, now}
    case Sv.OCancel{n}:
      Sv.OCancel{n}
    case Sv.OResume{n, now}:
      Sv.OResume{n, now}
    case Sv.OCreate{n, f}:
      Sv.OCreate{n, f}

def sf_isc(op: Sv.Op) -> Bool:
  match op:
    case Sv.OClaim{due, now, fresh}:
      True{}
    case Sv.ORecover{x}:
      False{}
    case Sv.OFinish{d, ran, failed, now}:
      False{}
    case Sv.OCancel{n}:
      False{}
    case Sv.OResume{n, now}:
      False{}
    case Sv.OCreate{n, f}:
      False{}

def sf_made(op: Sv.Op) -> Maybe<&2, SfJ>:
  match op:
    case Sv.OClaim{due, now, fresh}:
      None{}
    case Sv.ORecover{x}:
      None{}
    case Sv.OFinish{d, ran, failed, now}:
      None{}
    case Sv.OCancel{n}:
      None{}
    case Sv.OResume{n, now}:
      None{}
    case Sv.OCreate{n, f}:
      Some{SfJK{n, f}}

# Rendering an answer
# -------------------

def sf_cons(-A: Data, x: A, m: Maybe<&2, List<&2, A>>) -> Maybe<&2, List<&2, A>>:
  match m:
    case None{}:
      None{}
    case Some{xs}:
      Some{x <> xs}

def sf_tail(-A: Data, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      t

def sf_new_claim(isc: Bool, m: Maybe<&2, Nat>, d: String, +me: Nat, r: Maybe<&2, List<&2, SfC>>) -> Maybe<&2, List<&2, SfC>>:
  match isc:
    case False{}:
      None{}
    case True{}:
      match m:
        case None{}:
          None{}
        case Some{i}:
          sf_cons(SfC, SfCK{d, i, me}, r)

# the claim records the answers co make of the claim records cs, by index:
# kept, dropped, or a new claim of the known job record at position k of
# the file as read (pjs), owned by me (only in a claim pass); any other
# answer refused
def sf_render_c(co: List<&2, Sv.COut>, cs: List<&2, SfC>, +pjs: List<&2, Sv.JRec>, +me: Nat, +isc: Bool) -> Maybe<&2, List<&2, SfC>>:
  match co:
    case Nil{}:
      match cs:
        case Nil{}:
          Some{Nil{}}
        case c <> t:
          None{}
    case o <> ot:
      match o:
        case Sv.CKeep{}:
          match cs:
            case Nil{}:
              None{}
            case c <> t:
              sf_cons(SfC, c, sf_render_c(ot, t, pjs, me, isc))
        case Sv.CDrop{}:
          match cs:
            case Nil{}:
              None{}
            case c <> t:
              sf_render_c(ot, t, pjs, me, isc)
        case Sv.CNew{+k, d}:
          sf_new_claim(isc, CronServe.sv_job_at(pjs, k), d, me, sf_render_c(ot, sf_tail(SfC, cs), pjs, me, isc))

def sf_rj.made(mk: Maybe<&2, SfJ>, r: Maybe<&2, List<&2, SfJ>>) -> Maybe<&2, List<&2, SfJ>>:
  match mk:
    case None{}:
      None{}
    case Some{x}:
      sf_cons(SfJ, x, r)

def sf_rj.answer(x: SfJ, r: Maybe<&2, List<&2, SfJ>>) -> Maybe<&2, List<&2, SfJ>>:
  match x:
    case SfJK{i, f}:
      sf_cons(SfJ, SfJK{i, f}, r)
    case SfJR{t}:
      None{}

# the job records the answers jo make of the job records js, by index:
# kept as read; an answer on a record this build reads (its facts are the
# writers' to change: SfFacts); the new job (mk) past the records; any
# other answer refused
def sf_render_j(jo: List<&2, Sv.JOut>, js: List<&2, SfJ>, +mk: Maybe<&2, SfJ>) -> Maybe<&2, List<&2, SfJ>>:
  match jo:
    case Nil{}:
      match js:
        case Nil{}:
          Some{Nil{}}
        case x <> t:
          None{}
    case o <> ot:
      match o:
        case Sv.JSame{}:
          match js:
            case Nil{}:
              None{}
            case x <> t:
              sf_cons(SfJ, x, sf_render_j(ot, t, mk))
        case Sv.JNew{}:
          match js:
            case Nil{}:
              sf_rj.made(mk, sf_render_j(ot, Nil{}, mk))
            case x <> t:
              None{}
        case Sv.JTook{y}:
          match js:
            case Nil{}:
              None{}
            case x <> t:
              sf_rj.answer(x, sf_render_j(ot, t, mk))
        case Sv.JBack{y}:
          match js:
            case Nil{}:
              None{}
            case x <> t:
              sf_rj.answer(x, sf_render_j(ot, t, mk))
        case Sv.JFin{y}:
          match js:
            case Nil{}:
              None{}
            case x <> t:
              sf_rj.answer(x, sf_render_j(ot, t, mk))
        case Sv.JCut{y}:
          match js:
            case Nil{}:
              None{}
            case x <> t:
              sf_rj.answer(x, sf_render_j(ot, t, mk))
        case Sv.JAgain{y}:
          match js:
            case Nil{}:
              None{}
            case x <> t:
              sf_rj.answer(x, sf_render_j(ot, t, mk))

# the file once an unreadable one is moved aside
def sf_base(a: Bool, f: SfFile) -> SfFile:
  match a:
    case True{}:
      SfMissing{}
    case False{}:
      f

def sf_put(mj: Maybe<&2, List<&2, SfJ>>, mc: Maybe<&2, List<&2, SfC>>, b: SfFile) -> SfFile:
  match mj:
    case None{}:
      b
    case Some{js}:
      match mc:
        case None{}:
          b
        case Some{cs}:
          SfRead{js, cs}

def sf_written(w: Bool, a: Bool, f: SfFile, mj: Maybe<&2, List<&2, SfJ>>, mc: Maybe<&2, List<&2, SfC>>) -> SfFile:
  match w:
    case True{}:
      sf_put(mj, mc, sf_base(a, f))
    case False{}:
      sf_base(a, f)

def sf_moved(a: Bool, f: SfFile, aside: List<&2, Nat>) -> List<&2, Nat>:
  match a:
    case False{}:
      aside
    case True{}:
      match f:
        case SfMissing{}:
          aside
        case SfTorn{t}:
          t <> aside
        case SfRead{js, cs}:
          aside

# the world after process me's update answered o on the file f
def sf_apply(o: Sv.Out, +f: SfFile, +op: Sv.Op, +me: Nat, dead: List<&2, Nat>, aside: List<&2, Nat>) -> SfWorld:
  match o:
    case Sv.Out{+a, w, jo, co}:
      SfWorld{sf_written(w, a, f, sf_render_j(jo, sf_jobs(f), sf_made(op)), sf_render_c(co, sf_claims_of(f), sf_pjs(sf_jobs(f)), me, sf_isc(op))), dead, sf_moved(a, f, aside)}

# Other writers
# -------------

def sf_add_job(+t: Nat, f: SfFile) -> SfFile:
  match f:
    case SfMissing{}:
      SfRead{[SfJR{t}], Nil{}}
    case SfTorn{x}:
      SfTorn{x}
    case SfRead{js, cs}:
      SfRead{List.append(&2, SfJ, js, [SfJR{t}]), cs}

def sf_add_claim(+t: Nat, f: SfFile) -> SfFile:
  match f:
    case SfMissing{}:
      SfRead{Nil{}, [SfCR{t}]}
    case SfTorn{x}:
      SfTorn{x}
    case SfRead{js, cs}:
      SfRead{js, List.append(&2, SfC, cs, [SfCR{t}])}

def sf_set_fact(k: Nat, +f: CS.Fact, js: List<&2, SfJ>) -> List<&2, SfJ>:
  match k js:
    case _ Nil{}:
      Nil{}
    case 0n r <> t:
      match r:
        case SfJK{i, g}:
          SfJK{i, f} <> t
        case SfJR{x}:
          SfJR{x} <> t
    case 1n+p r <> t:
      r <> sf_set_fact(p, f, t)

def sf_facts(+k: Nat, +g: CS.Fact, f: SfFile) -> SfFile:
  match f:
    case SfMissing{}:
      SfMissing{}
    case SfTorn{x}:
      SfTorn{x}
    case SfRead{js, cs}:
      SfRead{sf_set_fact(k, g, js), cs}

# One event
# ---------

def sf_step(w: SfWorld, e: SfEv) -> SfWorld:
  match w:
    case SfWorld{+f, +dead, +aside}:
      match e:
        case SfUp{+p, +runs, op}:
          +op2 = sf_op(op, dead)
          sf_apply(CronServe.sv_reply(Sv.serve(runs, p, sf_disk(f), op2)), f, op2, p, dead, aside)
        case SfDie{p}:
          SfWorld{f, p <> dead, aside}
        case SfRawJob{t}:
          SfWorld{sf_add_job(t, f), dead, aside}
        case SfRawClaim{t}:
          SfWorld{sf_add_claim(t, f), dead, aside}
        case SfFacts{k, g}:
          SfWorld{sf_facts(k, g, f), dead, aside}
        case SfCorrupt{t}:
          SfWorld{SfTorn{t}, dead, aside}

# the world after evs (the newest first), from the empty world
def sf_run(evs: List<&2, SfEv>) -> SfWorld:
  match evs:
    case Nil{}:
      sf_empty()
    case e <> t:
      sf_step(sf_run(t), e)

# What the laws speak of
# ----------------------

def sf_file(w: SfWorld) -> SfFile:
  match w:
    case SfWorld{f, dead, aside}:
      f

def sf_dead(w: SfWorld) -> List<&2, Nat>:
  match w:
    case SfWorld{f, dead, aside}:
      dead

def sf_claims(w: SfWorld) -> List<&2, SfC>:
  sf_claims_of(sf_file(w))

# a known claim of job j is in cs
def sf_has_job(+j: Nat, cs: List<&2, SfC>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case c <> t:
      match c:
        case SfCK{d, x, o}:
          Bool.or(Nat.is_eq(x, j), sf_has_job(j, t))
        case SfCR{x}:
          sf_has_job(j, t)

# no two known claims of cs are of one job
def sf_one_each(cs: List<&2, SfC>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case c <> +t:
      match c:
        case SfCK{d, +j, o}:
          Bool.and(Bool.not(sf_has_job(j, t)), sf_one_each(t))
        case SfCR{x}:
          sf_one_each(t)

# the known claim of dispatch d, job j, owner o is in cs
def sf_has_claim(+d: String, +j: Nat, +o: Nat, cs: List<&2, SfC>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case c <> t:
      match c:
        case SfCK{x, y, z}:
          Bool.or(Bool.and(String.eq(x, d), Bool.and(Nat.is_eq(y, j), Nat.is_eq(z, o))), sf_has_claim(d, j, o, t))
        case SfCR{x}:
          sf_has_claim(d, j, o, t)

# no known claim of cs is owned by a process in dead
def sf_none_dead(cs: List<&2, SfC>, +dead: List<&2, Nat>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case c <> t:
      match c:
        case SfCK{d, j, o}:
          Bool.and(Bool.not(Cr.has(o, dead)), sf_none_dead(t, dead))
        case SfCR{x}:
          sf_none_dead(t, dead)

# the bytes of the records this build cannot read, in file order
def sf_raw_jobs.of(js: List<&2, SfJ>) -> List<&2, Nat>:
  match js:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case SfJK{i, f}:
          sf_raw_jobs.of(t)
        case SfJR{x}:
          x <> sf_raw_jobs.of(t)

def sf_raw_claims.of(cs: List<&2, SfC>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      match c:
        case SfCK{d, j, o}:
          sf_raw_claims.of(t)
        case SfCR{x}:
          x <> sf_raw_claims.of(t)

def sf_raw_jobs(w: SfWorld) -> List<&2, Nat>:
  sf_raw_jobs.of(sf_jobs(sf_file(w)))

def sf_raw_claims(w: SfWorld) -> List<&2, Nat>:
  sf_raw_claims.of(sf_claims(w))

# xs is ys's start
def sf_prefix(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} _:
      True{}
    case x <> t Nil{}:
      False{}
    case x <> t y <> u:
      Bool.and(Nat.is_eq(x, y), sf_prefix(t, u))

def sf_corrupts(e: SfEv) -> Bool:
  match e:
    case SfUp{p, runs, op}:
      False{}
    case SfDie{p}:
      False{}
    case SfRawJob{t}:
      False{}
    case SfRawClaim{t}:
      False{}
    case SfFacts{k, f}:
      False{}
    case SfCorrupt{t}:
      True{}

# the corrupt file t is the file, or was moved aside
def sf_keeps_torn(+t: Nat, w: SfWorld) -> Bool:
  match w:
    case SfWorld{f, dead, aside}:
      match f:
        case SfTorn{x}:
          Bool.or(Nat.is_eq(x, t), Cr.has(t, aside))
        case SfMissing{}:
          Cr.has(t, aside)
        case SfRead{js, cs}:
          Cr.has(t, aside)

# e leaves the claim of dispatch d of owner o standing: an update by any
# process that the claim stays through (CronServe.sv_stays: another's
# claim through all but a recovery that finds its owner dead, the owner's
# own claim of a dispatch it runs through all but that dispatch's finish),
# any other writer's event, a death; not the file's corruption
def sf_spares(w: SfWorld, e: SfEv, +d: String, +o: Nat) -> Bool:
  match e:
    case SfUp{p, runs, op}:
      CronServe.sv_stays(p, runs, sf_op(op, sf_dead(w)), d, o)
    case SfDie{p}:
      True{}
    case SfRawJob{t}:
      True{}
    case SfRawClaim{t}:
      True{}
    case SfFacts{k, f}:
      True{}
    case SfCorrupt{t}:
      False{}

# Laws
# ----

# LAW cron_serve_one_claim_per_job: after any events in any order (any
# processes claiming, recovering, finishing, cancelling, resuming,
# creating, dying; other writers; corruption), no two known claims on the
# file are of one job
# EXCLUDES: a double dispatch: a job claimed while a claim of it is on
#   record, two claims of one job in one pass, a claim made after a
#   recovery that kept the old one
law cron_serve_one_claim_per_job:
  for +evs: List<&2, SfEv>
  {sf_one_each(sf_claims(sf_run(evs))) == True{} : Bool}

# LAW cron_serve_live_claim_survives: from any world, through any event
# that spares it (another process's update but a recovery that finds the
# owner dead; the owner's own update but the finish of that dispatch it
# runs, or a recovery when it no longer runs it; any other writer; a
# death), a known claim on the file stays on the file
# EXCLUDES: a live claim of a live process cleared by another process (the
#   job claimed again while it runs), a finish that drops another claim,
#   a write that loses a claim
law cron_serve_live_claim_survives:
  for +w: SfWorld
  for +e: SfEv
  for +d: String
  for +j: Nat
  for +o: Nat
  for on: {sf_has_claim(d, j, o, sf_claims(w)) == True{} : Bool}
  for spares: {sf_spares(w, e, d, o) == True{} : Bool}
  {sf_has_claim(d, j, o, sf_claims(sf_step(w, e))) == True{} : Bool}

# LAW cron_serve_dead_claims_cleared: from any world, after a recovery by
# a live process, no known claim on the file is owned by a dead process
# EXCLUDES: a dead process's claim kept (its job never runs again), a
#   recovery that writes nothing while a dead claim is on record
law cron_serve_dead_claims_cleared:
  for +w: SfWorld
  for +p: Nat
  for +runs: List<&2, String>
  for +x: List<&2, Nat>
  for alive: {Cr.has(p, sf_dead(w)) == False{} : Bool}
  {sf_none_dead(sf_claims(sf_step(w, SfUp{p, runs, Sv.ORecover{x}})), sf_dead(w)) == True{} : Bool}

# LAW cron_serve_raw_records_kept: from any world, through any event but
# the file's corruption, the records this build cannot read (job records
# and claim records) stay byte for byte and in order; only another writer
# adds one, last
# EXCLUDES: a record this build cannot read dropped, changed or reordered
#   by any update, or written over by a write of the records it reads
law cron_serve_raw_records_kept:
  for +w: SfWorld
  for +e: SfEv
  for nc: {sf_corrupts(e) == False{} : Bool}
  {sf_prefix(sf_raw_jobs(w), sf_raw_jobs(sf_step(w, e))) == True{} : Bool} & {sf_prefix(sf_raw_claims(w), sf_raw_claims(sf_step(w, e))) == True{} : Bool}

# LAW cron_serve_corrupt_kept: from any world, through any event but a new
# corruption, a corrupt file stays the file or is moved aside: never
# written over or dropped
# EXCLUDES: a corrupt file written over by an update, deleted, or moved
#   aside without its bytes
law cron_serve_corrupt_kept:
  for +w: SfWorld
  for +e: SfEv
  for +t: Nat
  for nc: {sf_corrupts(e) == False{} : Bool}
  for kept: {sf_keeps_torn(t, w) == True{} : Bool}
  {sf_keeps_torn(t, sf_step(w, e)) == True{} : Bool}

# LAW cron_serve_safety_witness: anchor: the premises of the laws above
# hold on concrete worlds, and the runs do something: process 1 claims a
# due job created by process 0 (a claim of job 0 owned by 1 is on the
# file, with a record this build cannot read kept before it); another
# process's update spares it; process 1 dies and a recovery by 0 clears
# it; a corrupt file is moved aside by the next update
# EXCLUDES: cron_serve_live_claim_survives, cron_serve_dead_claims_cleared
#   or cron_serve_corrupt_kept made vacuous by premises no world meets, a
#   world where no claim is ever made
law cron_serve_safety_witness:
  {sf_claims(sf_run([SfUp{1n, Nil{}, Sv.OClaim{5n, 5n, ["a"]}}, SfRawClaim{7n}, SfUp{0n, Nil{}, Sv.OCreate{0n, CS.Fact{Cr.Active{}, CS.POnce{}, Some{5n}, 0n}}}])) == [SfCR{7n}, SfCK{"a", 0n, 1n}] : List<&2, SfC>} &
  {sf_spares(sf_run(Nil{}), SfUp{0n, Nil{}, Sv.ORecover{Nil{}}}, "a", 1n) == True{} : Bool} &
  {sf_claims(sf_run([SfUp{0n, Nil{}, Sv.ORecover{Nil{}}}, SfDie{1n}, SfUp{1n, Nil{}, Sv.OClaim{5n, 5n, ["a"]}}, SfUp{0n, Nil{}, Sv.OCreate{0n, CS.Fact{Cr.Active{}, CS.POnce{}, Some{5n}, 0n}}}])) == Nil{} : List<&2, SfC>} &
  {Cr.has(0n, sf_dead(sf_run([SfDie{1n}]))) == False{} : Bool} &
  {sf_keeps_torn(3n, sf_run([SfUp{0n, Nil{}, Sv.OCancel{0n}}, SfCorrupt{3n}])) == True{} : Bool} &
  {sf_corrupts(SfRawJob{1n}) == False{} : Bool}
