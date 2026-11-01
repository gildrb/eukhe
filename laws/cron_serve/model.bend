# eukhe: the laws of area cron_serve: each update the stepper runs is the
# model's step

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_serve.bend as Sv
import ../cron.bend as Cron
import ./serve.bend as CronServe

# (D2.3) The update the stepper runs is the model's step
# ------------------------------------------------------
# bend/cron.bend is the model of the shared file (minutes); the store
# counts ms (a minute is 60000 ms). A file the store reads holds a model
# file's job records in order, each known job as its id and its facts as
# Rust gathers them (Cron.fact_of), each record this build cannot read as
# such (cm_pj). These laws state, for every known job j at every position
# of such a file, that the answer the stepper's serve (Sv.serve, the one
# the entry runs: cron_serve_is_entry) gives on j, applied to j as the
# store applies it (cm_applied: Cron.took_view and the other views of
# laws/cron.bend), is the model's step on j (Cr.job: the step Cr.step runs
# on every known record): a claim pass is Take, a recovery Recover, a
# cancel Cancel, a resume Resume, at the model's clock; a create adds one
# new job last, as Cr.step's Create. The premises state what makes the
# file the model's: job ids distinct (the model's are), the claim records
# holding a claim of j's id exactly when j has a claim, and for a
# recovery j's claim record with its dispatch and owner, the dispatch run
# here exactly when the process runs j.

# The file of a model's records
# -----------------------------

def cm_pj(rs: List<&2, Cr.Rec>) -> List<&2, Sv.JRec>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case Cr.Known{+j}:
          Sv.JKnown{Cr.Job.id(j), Cron.fact_of(j, 60000n)} <> cm_pj(t)
        case Cr.Raw{x}:
          Sv.JRaw{} <> cm_pj(t)

# a known job of rs has id i
def cm_has_id(+i: Nat, rs: List<&2, Cr.Rec>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> t:
      match r:
        case Cr.Known{j}:
          Bool.or(Nat.is_eq(Cr.Job.id(j), i), cm_has_id(i, t))
        case Cr.Raw{x}:
          cm_has_id(i, t)

# no two known jobs of rs have one id
def cm_distinct(rs: List<&2, Cr.Rec>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> +t:
      match r:
        case Cr.Known{j}:
          Bool.and(Bool.not(cm_has_id(Cr.Job.id(j), t)), cm_distinct(t))
        case Cr.Raw{x}:
          cm_distinct(t)

def cm_cpick(b: Bool, c: Sv.CRec, r: List<&2, Sv.CRec>) -> List<&2, Sv.CRec>:
  match b:
    case True{}:
      c <> r
    case False{}:
      r

# the known claim records of job i, in file order
def cm_claims_of(+i: Nat, cs: List<&2, Sv.CRec>) -> List<&2, Sv.CRec>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      match c:
        case Sv.CKnown{+d, +x, +o}:
          cm_cpick(Nat.is_eq(x, i), Sv.CKnown{d, x, o}, cm_claims_of(i, t))
        case Sv.CRaw{}:
          cm_claims_of(i, t)

# the claim records of job j as the model's claim of j: none when it has
# none, else one claim of dispatch d owned by the claim's owner
def cm_claim_rec(j: Cr.Job, +d: String) -> List<&2, Sv.CRec>:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match cl:
        case None{}:
          Nil{}
        case Some{x}:
          match x:
            case Cr.Claim{oc, o}:
              [Sv.CKnown{d, i, o}]

# the first known claim of the finished dispatch, if any, is of job i
def cm_hits(m: Maybe<&2, Sv.Hit>, +i: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{h}:
      match h:
        case Sv.Hit{jh, o}:
          Nat.is_eq(jh, i)

def cm_beq(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

# the first known claim of the finished dispatch is j's claim: none when j
# has none, else one of the same owner
def cm_hit_is(j: Cr.Job, m: Maybe<&2, Sv.Hit>) -> Bool:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match cl:
        case None{}:
          match m:
            case None{}:
              True{}
            case Some{x}:
              False{}
        case Some{x}:
          match x:
            case Cr.Claim{oc, o2}:
              match m:
                case None{}:
                  False{}
                case Some{y}:
                  match y:
                    case Sv.Hit{jh, o}:
                      Nat.is_eq(o, o2)

# when j is the finished job (b): the dispatch runs here exactly when the
# process runs j (run, prun), and its first known claim is j's claim
def cm_its(b: Bool, run: Bool, prun: Bool, m: Maybe<&2, Sv.Hit>, j: Cr.Job) -> Bool:
  match b:
    case False{}:
      True{}
    case True{}:
      Bool.and(cm_beq(run, prun), cm_hit_is(j, m))

# What the store does with an answer
# ----------------------------------

# the view of job j once the store applies the answer o (cl: a recovery
# drops j's claim)
def cm_applied(o: Sv.JOut, +j: Cr.Job, +p: Nat, cl: Bool) -> Cron.View():
  match o:
    case Sv.JSame{}:
      Cron.view(j, 60000n)
    case Sv.JTook{t}:
      Cron.took_view(t, j, p, 60000n)
    case Sv.JBack{b}:
      Cron.back_view(b, cl, j, 60000n)
    case Sv.JFin{x}:
      Cron.fin_view(x, j, 60000n)
    case Sv.JCut{x}:
      Cron.cut_view(x, j, 60000n)
    case Sv.JAgain{x}:
      Cron.again_view(x, j, 60000n)
    case Sv.JNew{}:
      Cron.view(j, 60000n)

# the answer on the job record at position k
def cm_at(r: Sv.Served, +k: Nat) -> Maybe<&2, Sv.JOut>:
  List.get(&2, Sv.JOut, CronServe.sv_jobs(CronServe.sv_reply(r)), k)

# Laws
# ----

# LAW cron_serve_claim_is_model: a claim pass of process p at the model's
# clock c, on a model file (distinct ids, a claim of j's id on record
# exactly when j has one, a fresh dispatch id per record), answers each
# known job j what, applied, is the model's claim step of p on j (Take)
# EXCLUDES: a claim pass that claims a job with a claim on record or rolls
#   one without, that skips a due job for want of an id another job used,
#   that reads another record's claim, or answers at another position
law cron_serve_claim_is_model:
  for +rs: List<&2, Cr.Rec>
  for +cs: List<&2, Sv.CRec>
  for +runs: List<&2, String>
  for +p: Nat
  for +c: Nat
  for +dead: List<&2, Nat>
  for +fresh: List<&2, String>
  for +k: Nat
  for +j: Cr.Job
  for at: {List.get(&2, Cr.Rec, rs, k) == Some{Cr.Known{j}} : Maybe<&2, Cr.Rec>}
  for ids: {cm_distinct(rs) == True{} : Bool}
  for cl: {CronServe.sv_has(Cr.Job.id(j), CronServe.sv_taken(cs)) == Cron.claimed_of(j) : Bool}
  for enough: {Nat.is_le(List.length(&2, Cr.Rec, rs), List.length(&2, String, fresh)) == True{} : Bool}
  exs o: Sv.JOut
  {cm_at(Sv.serve(runs, p, Sv.Parsed{cm_pj(rs), cs}, Sv.OClaim{Nat.mul(c, 60000n), Nat.mul(c, 60000n), fresh}), k) == Some{o} : Maybe<&2, Sv.JOut>} & {cm_applied(o, j, p, False{}) == Cron.view(Cr.job(Cr.Take{p}, c, dead, j), 60000n) : Cron.View()}

# LAW cron_serve_recover_is_model: a recovery of a live process p, on a
# model file where j's claim records are the model's claim of j (dispatch
# d, run here exactly when p runs j), drops j's claim exactly when the
# model clears it, and answers j what, applied, is the model's recovery
# step of p on j (Recover)
# EXCLUDES: a recovery that clears a claim the model keeps or keeps one it
#   clears, a verdict read from another job's claim, an interrupted run
#   recorded on a job whose claim stays
law cron_serve_recover_is_model:
  for +rs: List<&2, Cr.Rec>
  for +cs: List<&2, Sv.CRec>
  for +runs: List<&2, String>
  for +p: Nat
  for +c: Nat
  for +dead: List<&2, Nat>
  for +k: Nat
  for +j: Cr.Job
  for +d: String
  for at: {List.get(&2, Cr.Rec, rs, k) == Some{Cr.Known{j}} : Maybe<&2, Cr.Rec>}
  for alive: {Cr.has(p, dead) == False{} : Bool}
  for rec: {cm_claims_of(Cr.Job.id(j), cs) == cm_claim_rec(j, d) : List<&2, Sv.CRec>}
  for run: {CronServe.sv_in(d, runs) == Cr.has(p, Cron.runs_of(j)) : Bool}
  exs o: Sv.JOut
  {cm_at(Sv.serve(runs, p, Sv.Parsed{cm_pj(rs), cs}, Sv.ORecover{dead}), k) == Some{o} : Maybe<&2, Sv.JOut>} & {CronServe.sv_has(Cr.Job.id(j), CronServe.sv_cleared(p, runs, dead, cs)) == Cron.cleared_of(p, dead, j) : Bool} & {cm_applied(o, j, p, Cron.cleared_of(p, dead, j)) == Cron.view(Cr.job(Cr.Recover{p}, c, dead, j), 60000n) : Cron.View()}

# LAW cron_serve_finish_is_model: the finish of process p's run of
# dispatch d at the model's clock c, the model's finish of job i (the
# first known claim of d, if any, is of job i; on job i the dispatch runs
# here exactly when p runs it, and that claim is i's claim), answers each
# known job j of a model file what, applied, is the model's finish step
# (a good run, a failure or a skip) on j
# EXCLUDES: a finish counted on another job, by a process that does not
#   own the claim or no longer runs it, a result counted as another, a
#   finish that touches a job it is not of
law cron_serve_finish_is_model:
  for +rs: List<&2, Cr.Rec>
  for +cs: List<&2, Sv.CRec>
  for +runs: List<&2, String>
  for +p: Nat
  for +c: Nat
  for +dead: List<&2, Nat>
  for +k: Nat
  for +j: Cr.Job
  for +i: Nat
  for +out: Cr.Out
  for +d: String
  for at: {List.get(&2, Cr.Rec, rs, k) == Some{Cr.Known{j}} : Maybe<&2, Cr.Rec>}
  for hits: {cm_hits(CronServe.sv_claim_of(d, cs), i) == True{} : Bool}
  for its: {cm_its(Nat.is_eq(Cr.Job.id(j), i), CronServe.sv_in(d, runs), Cr.has(p, Cron.runs_of(j)), CronServe.sv_claim_of(d, cs), j) == True{} : Bool}
  exs o: Sv.JOut
  {cm_at(Sv.serve(runs, p, Sv.Parsed{cm_pj(rs), cs}, Sv.OFinish{d, Cron.ran_of(out), Cron.failed_of(out), Nat.mul(c, 60000n)}), k) == Some{o} : Maybe<&2, Sv.JOut>} & {cm_applied(o, j, p, False{}) == Cron.view(Cr.job(Cr.Finish{p, i, out}, c, dead, j), 60000n) : Cron.View()}

# LAW cron_serve_finish_witness: anchor: the premises of
# cron_serve_finish_is_model hold on a concrete file where they say
# something: job 1, claimed and run by process 1, finished by it
# EXCLUDES: cron_serve_finish_is_model made vacuous by premises no file
#   meets
law cron_serve_finish_witness:
  {cm_hits(CronServe.sv_claim_of("a", [Sv.CKnown{"a", 1n, 1n}]), 1n) == True{} : Bool} &
  {cm_its(True{}, CronServe.sv_in("a", ["a"]), Cr.has(1n, Cron.runs_of(Cr.Job{1n, Cr.Every{0n}, Cr.Active{}, Some{0n}, 0n, Some{Cr.Claim{0n, 1n}}, [1n], Nil{}, Nil{}})), CronServe.sv_claim_of("a", [Sv.CKnown{"a", 1n, 1n}]), Cr.Job{1n, Cr.Every{0n}, Cr.Active{}, Some{0n}, 0n, Some{Cr.Claim{0n, 1n}}, [1n], Nil{}, Nil{}}) == True{} : Bool}

# LAW cron_serve_cancel_is_model: a cancel of job n answers each known job
# j of a model file what, applied, is the model's cancel step on j
# EXCLUDES: a cancel of another job, a cancel that misses a job of the id
law cron_serve_cancel_is_model:
  for +rs: List<&2, Cr.Rec>
  for +cs: List<&2, Sv.CRec>
  for +runs: List<&2, String>
  for +p: Nat
  for +n: Nat
  for +c: Nat
  for +dead: List<&2, Nat>
  for +k: Nat
  for +j: Cr.Job
  for at: {List.get(&2, Cr.Rec, rs, k) == Some{Cr.Known{j}} : Maybe<&2, Cr.Rec>}
  exs o: Sv.JOut
  {cm_at(Sv.serve(runs, p, Sv.Parsed{cm_pj(rs), cs}, Sv.OCancel{n}), k) == Some{o} : Maybe<&2, Sv.JOut>} & {cm_applied(o, j, p, False{}) == Cron.view(Cr.job(Cr.Cancel{p, n}, c, dead, j), 60000n) : Cron.View()}

# LAW cron_serve_resume_is_model: a resume of job n at the model's clock c
# answers each known job j of a model file what, applied, is the model's
# resume step on j
# EXCLUDES: a resume of another job, at another time, a resume that
#   misses a job of the id
law cron_serve_resume_is_model:
  for +rs: List<&2, Cr.Rec>
  for +cs: List<&2, Sv.CRec>
  for +runs: List<&2, String>
  for +p: Nat
  for +n: Nat
  for +c: Nat
  for +dead: List<&2, Nat>
  for +k: Nat
  for +j: Cr.Job
  for at: {List.get(&2, Cr.Rec, rs, k) == Some{Cr.Known{j}} : Maybe<&2, Cr.Rec>}
  exs o: Sv.JOut
  {cm_at(Sv.serve(runs, p, Sv.Parsed{cm_pj(rs), cs}, Sv.OResume{n, Nat.mul(c, 60000n)}), k) == Some{o} : Maybe<&2, Sv.JOut>} & {cm_applied(o, j, p, False{}) == Cron.view(Cr.job(Cr.Resume{p, n}, c, dead, j), 60000n) : Cron.View()}

# LAW cron_serve_create_is_model: a create on a model file keeps every
# record as read and every claim, and adds the new job alone, last; the
# model's create of a live process on a readable file adds its new job
# alone, last
# EXCLUDES: a create that changes, drops or reorders a record, adds the
#   new job elsewhere or twice
law cron_serve_create_is_model:
  for +rs: List<&2, Cr.Rec>
  for +cs: List<&2, Sv.CRec>
  for +runs: List<&2, String>
  for +p: Nat
  for +f: CS.Fact
  for +rd: List<&2, Nat>
  for +dead: List<&2, Nat>
  for +c: Nat
  for +n: Nat
  for +aside: List<&2, Nat>
  for +sc: Cr.Sched
  for alive: {Cr.has(p, dead) == False{} : Bool}
  {CronServe.sv_reply(Sv.serve(runs, p, Sv.Parsed{cm_pj(rs), cs}, Sv.OCreate{n, f})) == Sv.Out{False{}, True{}, List.append(&2, Sv.JOut, CronServe.sv_same(cm_pj(rs)), [Sv.JNew{}]), CronServe.sv_keep(cs)} : Sv.Out} & {Cr.S.recs(Cr.step(Cr.S{None{}, rs, rd, dead, c, n, aside}, Cr.Create{p, sc})) == List.append(&2, Cr.Rec, rs, [Cr.Known{Cr.Job{n, sc, Cr.Active{}, Some{Cr.first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}}}]) : List<&2, Cr.Rec>}

# LAW cron_serve_model_witness: anchor: the premises of the laws above hold
# on a concrete model file: a due job 0 with no claim and a job 1 claimed
# by process 1 that it runs, distinct ids, the claim records the model's
# EXCLUDES: cron_serve_claim_is_model or cron_serve_recover_is_model made
#   vacuous by premises no file meets
law cron_serve_model_witness:
  {cm_distinct([Cr.Known{Cr.Job{0n, Cr.Every{0n}, Cr.Active{}, Some{0n}, 0n, None{}, Nil{}, Nil{}, Nil{}}}, Cr.Known{Cr.Job{1n, Cr.Every{0n}, Cr.Active{}, Some{0n}, 0n, Some{Cr.Claim{0n, 1n}}, [1n], Nil{}, Nil{}}}]) == True{} : Bool} &
  {CronServe.sv_has(1n, CronServe.sv_taken([Sv.CKnown{"a", 1n, 1n}])) == Cron.claimed_of(Cr.Job{1n, Cr.Every{0n}, Cr.Active{}, Some{0n}, 0n, Some{Cr.Claim{0n, 1n}}, [1n], Nil{}, Nil{}}) : Bool} &
  {cm_claims_of(1n, [Sv.CKnown{"a", 1n, 1n}]) == cm_claim_rec(Cr.Job{1n, Cr.Every{0n}, Cr.Active{}, Some{0n}, 0n, Some{Cr.Claim{0n, 1n}}, [1n], Nil{}, Nil{}}, "a") : List<&2, Sv.CRec>} &
  {CronServe.sv_in("a", ["a"]) == Cr.has(1n, Cron.runs_of(Cr.Job{1n, Cr.Every{0n}, Cr.Active{}, Some{0n}, 0n, Some{Cr.Claim{0n, 1n}}, [1n], Nil{}, Nil{}})) : Bool}
