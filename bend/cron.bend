# cron: the model of the cron job store shared by processes
# (docs/state.md D2). The Rust code is `AgentCronJobStore` in
# crates/eukhe-core/src/cron/store/; its per-job decisions run as
# bend/cron_store.bend (entry bend/ffi_cron.bend), tied to this model's
# steps by the `cron_*_refines` laws; the bridge (bridge/bridge_cron.bend,
# crates/eukhe-core/src/cron/store/bridge.rs) runs the store's shell and
# this model on the same events of several processes.
#
# One jobs file, shared by any number of processes. Each job record holds
# its schedule, its status, its next run, its failures in a row, and the
# claim on record (the occurrence it started and the process that runs
# it). The file can also hold records this build cannot read (`Raw`, kept
# as their bytes `t`), and it can be corrupt (`bad`): then the next update
# moves it aside (`aside`) and starts from an empty file.
#
# Time counts in minutes. A one-shot `Once{d}` runs once, 1+d minutes
# after it is made; `Every{k}` runs each 1+k minutes.
#
# Each job also carries ghost state that the Rust code does not store, so
# that the laws can speak of it: `runs`, the processes that run the job
# now (a process runs a claimed dispatch until it records the result, its
# pass unwinds, or it dies); `starts`, the occurrences that started, the
# newest first; `hist`, the results the job counted, the newest first.
#
# Events: a process makes a job, claims the due jobs, recovers claims,
# finishes a run (good, failed, or skipped), unwinds its pass, dies; the
# user cancels or resumes a job; time passes; another writer adds records
# this build cannot read; the file becomes corrupt. A dead process does
# nothing.

import Base

# The record
# ----------

type Sched is Data:
  Once{d: Nat}
  Every{k: Nat}

type Status is Data:
  Active{}
  Paused{}
  Finished{}
  Cancelled{}

# the result of a run
type Out is Data:
  Win{}
  Loss{}
  Skip{}

# what a job counted: a good run, a failed run, a resume by the user
type Mark is Data:
  MWin{}
  MLoss{}
  MReset{}

# the claim on record: the occurrence it started, the process that owns it
type Claim is Data:
  Claim{occ: Nat, owner: Nat}

type Job is Data:
  Job{id: Nat, sched: Sched, status: Status, next: Maybe<&2, Nat>, streak: Nat, claim: Maybe<&2, Claim>, runs: List<&2, Nat>, starts: List<&2, Nat>, hist: List<&2, Mark>}

type Rec is Data:
  Known{j: Job}
  Raw{t: Nat}

# the file (corrupt with bytes t, or read), the records, the claim records
# this build cannot read, the dead processes, the clock, the next job id,
# and the corrupt files moved aside (the newest first)
type S is Data:
  S{bad: Maybe<&2, Nat>, recs: List<&2, Rec>, rawd: List<&2, Nat>, dead: List<&2, Nat>, clock: Nat, ids: Nat, aside: List<&2, Nat>}

type Ev is Data:
  Create{p: Nat, s: Sched}
  Take{p: Nat}
  Recover{p: Nat}
  Finish{p: Nat, i: Nat, o: Out}
  Abort{p: Nat}
  Die{p: Nat}
  Cancel{p: Nat, i: Nat}
  Resume{p: Nat, i: Nat}
  Tick{d: Nat}
  RawJob{t: Nat}
  RawClaim{t: Nat}
  Corrupt{t: Nat}

def S.empty() -> S:
  S{None{}, Nil{}, Nil{}, Nil{}, 0n, 0n, Nil{}}

# The failure backoff
# -------------------

# failed runs in a row after which a job stops
def CAP() -> Nat:
  8n

# the pause in minutes after the k-th failure in a row: 2, 4, 8, 16, 32,
# then 60
def delay(k: Nat) -> Nat:
  match k:
    case 0n:
      2n
    case 1n+a:
      match a:
        case 0n:
          2n
        case 1n+b:
          match b:
            case 0n:
              4n
            case 1n+c:
              match c:
                case 0n:
                  8n
                case 1n+e:
                  match e:
                    case 0n:
                      16n
                    case 1n+f:
                      match f:
                        case 0n:
                          32n
                        case 1n+g:
                          60n

def later.pick(b: Bool, n: Nat, u: Nat) -> Nat:
  match b:
    case True{}:
      u
    case False{}:
      n

# the next run after a failure: the pause end u, or a later next run
def later(nx: Maybe<&2, Nat>, +u: Nat) -> Nat:
  match nx:
    case None{}:
      u
    case Some{+n}:
      later.pick(Nat.is_lt(n, u), n, u)

# Small parts
# -----------

# p is in xs
def has(+p: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(Nat.is_eq(x, p), has(p, t))

def drop.put(b: Bool, x: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      r
    case False{}:
      x <> r

# xs without p
def drop(+p: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      drop.put(Nat.is_eq(x, p), x, drop(p, t))

# the next run of a schedule after a run at c
def adv(s: Sched, +c: Nat) -> Maybe<&2, Nat>:
  match s:
    case Once{d}:
      None{}
    case Every{k}:
      Some{Nat.add(c, 1n+k)}

# the first run of a new job made at c
def first(s: Sched, +c: Nat) -> Nat:
  match s:
    case Once{d}:
      Nat.add(c, 1n+d)
    case Every{k}:
      Nat.add(c, 1n+k)

def is_once(s: Sched) -> Bool:
  match s:
    case Once{d}:
      True{}
    case Every{k}:
      False{}

# A claim
# -------

def take.due(due: Bool, +p: Nat, +c: Nat, i: Nat, +s: Sched, +n: Nat, k: Nat, cl: Maybe<&2, Claim>, rs: List<&2, Nat>, ss: List<&2, Nat>, h: List<&2, Mark>) -> Job:
  match due:
    case False{}:
      Job{i, s, Active{}, Some{n}, k, cl, rs, ss, h}
    case True{}:
      match cl:
        case None{}:
          Job{i, s, Active{}, adv(s, c), k, Some{Claim{n, p}}, p <> rs, n <> ss, h}
        case Some{x}:
          Job{i, s, Active{}, adv(s, c), k, Some{x}, rs, ss, h}

def take.next(+p: Nat, +c: Nat, i: Nat, +s: Sched, nx: Maybe<&2, Nat>, k: Nat, cl: Maybe<&2, Claim>, rs: List<&2, Nat>, ss: List<&2, Nat>, h: List<&2, Mark>) -> Job:
  match nx:
    case None{}:
      Job{i, s, Active{}, None{}, k, cl, rs, ss, h}
    case Some{+n}:
      take.due(Nat.is_le(n, c), p, c, i, s, n, k, cl, rs, ss, h)

# p claims a due active job with no claim; a due job with a claim only
# rolls its next run
def take(+p: Nat, +c: Nat, j: Job) -> Job:
  match j:
    case Job{i, +s, st, nx, k, cl, rs, ss, h}:
      match st:
        case Active{}:
          take.next(p, c, i, s, nx, k, cl, rs, ss, h)
        case Paused{}:
          Job{i, s, Paused{}, nx, k, cl, rs, ss, h}
        case Finished{}:
          Job{i, s, Finished{}, nx, k, cl, rs, ss, h}
        case Cancelled{}:
          Job{i, s, Cancelled{}, nx, k, cl, rs, ss, h}

# A recovery
# ----------

# p may clear the claim of o: its own claim with no run of it, or the
# claim of a dead process
def clears(+p: Nat, +o: Nat, rs: List<&2, Nat>, dead: List<&2, Nat>) -> Bool:
  Bool.or(Bool.and(Nat.is_eq(o, p), Bool.not(has(p, rs))), has(o, dead))

def recover.end(once: Bool, i: Nat, s: Sched, nx: Maybe<&2, Nat>, k: Nat, rs: List<&2, Nat>, ss: List<&2, Nat>, h: List<&2, Mark>) -> Job:
  match once:
    case True{}:
      Job{i, s, Finished{}, None{}, k, None{}, rs, ss, h}
    case False{}:
      Job{i, s, Active{}, nx, k, None{}, rs, ss, h}

def recover.go(b: Bool, i: Nat, +s: Sched, st: Status, nx: Maybe<&2, Nat>, k: Nat, x: Claim, rs: List<&2, Nat>, ss: List<&2, Nat>, h: List<&2, Mark>) -> Job:
  match b:
    case False{}:
      Job{i, s, st, nx, k, Some{x}, rs, ss, h}
    case True{}:
      match st:
        case Active{}:
          recover.end(is_once(s), i, s, nx, k, rs, ss, h)
        case Paused{}:
          Job{i, s, Paused{}, nx, k, None{}, rs, ss, h}
        case Finished{}:
          Job{i, s, Finished{}, nx, k, None{}, rs, ss, h}
        case Cancelled{}:
          Job{i, s, Cancelled{}, nx, k, None{}, rs, ss, h}

# the claim it clears ends its run: an active one-shot is finished
def recover(+p: Nat, +dead: List<&2, Nat>, j: Job) -> Job:
  match j:
    case Job{i, +s, st, nx, k, cl, +rs, ss, h}:
      match cl:
        case None{}:
          Job{i, s, st, nx, k, None{}, rs, ss, h}
        case Some{x}:
          match x:
            case Claim{+x_occ, +o}:
              recover.go(clears(p, o, rs, dead), i, s, st, nx, k, Claim{x_occ, o}, rs, ss, h)

# The finish step
# ---------------

def count.streak(o: Out, k: Nat) -> Nat:
  match o:
    case Win{}:
      0n
    case Loss{}:
      1n+k
    case Skip{}:
      k

def count.hist(o: Out, h: List<&2, Mark>) -> List<&2, Mark>:
  match o:
    case Win{}:
      MWin{} <> h
    case Loss{}:
      MLoss{} <> h
    case Skip{}:
      h

# a failed run: back off, or stop at the cap
def finish.fail(under: Bool, +c: Nat, i: Nat, s: Sched, nx: Maybe<&2, Nat>, +k: Nat, rs: List<&2, Nat>, ss: List<&2, Nat>, h: List<&2, Mark>) -> Job:
  match under:
    case True{}:
      Job{i, s, Active{}, Some{later(nx, Nat.add(c, delay(k)))}, k, None{}, rs, ss, h}
    case False{}:
      Job{i, s, Paused{}, None{}, k, None{}, rs, ss, h}

# an active job counts the result; a one-shot is finished
def finish.count(once: Bool, +c: Nat, +o: Out, i: Nat, +s: Sched, nx: Maybe<&2, Nat>, +k: Nat, rs: List<&2, Nat>, ss: List<&2, Nat>, h: List<&2, Mark>) -> Job:
  match once:
    case True{}:
      Job{i, s, Finished{}, None{}, count.streak(o, k), None{}, rs, ss, count.hist(o, h)}
    case False{}:
      match o:
        case Win{}:
          Job{i, s, Active{}, nx, 0n, None{}, rs, ss, MWin{} <> h}
        case Skip{}:
          Job{i, s, Active{}, adv(s, c), k, None{}, rs, ss, h}
        case Loss{}:
          finish.fail(Nat.is_lt(1n+k, CAP()), c, i, s, nx, 1n+k, rs, ss, MLoss{} <> h)

def finish.own(own: Bool, x: Claim, +c: Nat, o: Out, i: Nat, +s: Sched, st: Status, nx: Maybe<&2, Nat>, k: Nat, rs: List<&2, Nat>, ss: List<&2, Nat>, h: List<&2, Mark>) -> Job:
  match own:
    case False{}:
      Job{i, s, st, nx, k, Some{x}, rs, ss, h}
    case True{}:
      match st:
        case Active{}:
          finish.count(is_once(s), c, o, i, s, nx, k, rs, ss, h)
        case Paused{}:
          Job{i, s, Paused{}, nx, k, None{}, rs, ss, h}
        case Finished{}:
          Job{i, s, Finished{}, nx, k, None{}, rs, ss, h}
        case Cancelled{}:
          Job{i, s, Cancelled{}, nx, k, None{}, rs, ss, h}

# the claim is p's own: release it and count the result
def finish.claim(cl: Maybe<&2, Claim>, +p: Nat, +c: Nat, o: Out, i: Nat, +s: Sched, st: Status, nx: Maybe<&2, Nat>, k: Nat, rs: List<&2, Nat>, ss: List<&2, Nat>, h: List<&2, Mark>) -> Job:
  match cl:
    case None{}:
      Job{i, s, st, nx, k, None{}, rs, ss, h}
    case Some{x}:
      match x:
        case Claim{+x_occ, +w}:
          finish.own(Nat.is_eq(w, p), Claim{x_occ, w}, c, o, i, s, st, nx, k, rs, ss, h)

def finish.run(run: Bool, +p: Nat, +c: Nat, o: Out, i: Nat, +s: Sched, st: Status, nx: Maybe<&2, Nat>, k: Nat, cl: Maybe<&2, Claim>, rs: List<&2, Nat>, ss: List<&2, Nat>, h: List<&2, Mark>) -> Job:
  match run:
    case False{}:
      Job{i, s, st, nx, k, cl, rs, ss, h}
    case True{}:
      finish.claim(cl, p, c, o, i, s, st, nx, k, drop(p, rs), ss, h)

# p records the result o of its run of the job: the claim is released, and
# an active job counts the result
def finish(+p: Nat, +c: Nat, +o: Out, j: Job) -> Job:
  match j:
    case Job{i, +s, st, nx, k, cl, +rs, ss, h}:
      finish.run(has(p, rs), p, c, o, i, s, st, nx, k, cl, rs, ss, h)

# User actions
# ------------

def cancel(j: Job) -> Job:
  match j:
    case Job{i, s, st, nx, k, cl, rs, ss, h}:
      match st:
        case Cancelled{}:
          Job{i, s, Cancelled{}, nx, k, cl, rs, ss, h}
        case Active{}:
          Job{i, s, Cancelled{}, None{}, k, cl, rs, ss, h}
        case Paused{}:
          Job{i, s, Cancelled{}, None{}, k, cl, rs, ss, h}
        case Finished{}:
          Job{i, s, Cancelled{}, None{}, k, cl, rs, ss, h}

# a repeating job that is active or paused runs again on its schedule,
# its failures in a row forgotten
def resume(+c: Nat, j: Job) -> Job:
  match j:
    case Job{i, s, st, nx, k, cl, rs, ss, h}:
      match s:
        case Once{d}:
          Job{i, Once{d}, st, nx, k, cl, rs, ss, h}
        case Every{+n}:
          match st:
            case Active{}:
              Job{i, Every{n}, Active{}, Some{Nat.add(c, 1n+n)}, 0n, cl, rs, ss, MReset{} <> h}
            case Paused{}:
              Job{i, Every{n}, Active{}, Some{Nat.add(c, 1n+n)}, 0n, cl, rs, ss, MReset{} <> h}
            case Finished{}:
              Job{i, Every{n}, Finished{}, nx, k, cl, rs, ss, h}
            case Cancelled{}:
              Job{i, Every{n}, Cancelled{}, nx, k, cl, rs, ss, h}

# Runs of a process end
# ---------------------

def unrun(+p: Nat, j: Job) -> Job:
  match j:
    case Job{i, s, st, nx, k, cl, rs, ss, h}:
      Job{i, s, st, nx, k, cl, drop(p, rs), ss, h}

# One step
# --------

def Job.id(j: Job) -> Nat:
  match j:
    case Job{i, s, st, nx, k, cl, rs, ss, h}:
      i

def Job.claim(j: Job) -> Maybe<&2, Claim>:
  match j:
    case Job{i, s, st, nx, k, cl, rs, ss, h}:
      cl

def Job.status(j: Job) -> Status:
  match j:
    case Job{i, s, st, nx, k, cl, rs, ss, h}:
      st

def job.pick(b: Bool, a: Job, j: Job) -> Job:
  match b:
    case True{}:
      a
    case False{}:
      j

# what event e does to one job, at clock c with the dead processes dead
def job(+e: Ev, +c: Nat, +dead: List<&2, Nat>, +j: Job) -> Job:
  match e:
    case Take{p}:
      take(p, c, j)
    case Recover{p}:
      recover(p, dead, j)
    case Finish{p, i, o}:
      job.pick(Nat.is_eq(Job.id(j), i), finish(p, c, o, j), j)
    case Abort{p}:
      unrun(p, j)
    case Die{p}:
      unrun(p, j)
    case Cancel{p, i}:
      job.pick(Nat.is_eq(Job.id(j), i), cancel(j), j)
    case Resume{p, i}:
      job.pick(Nat.is_eq(Job.id(j), i), resume(c, j), j)
    case Create{p, s}:
      j
    case Tick{d}:
      j
    case RawJob{t}:
      j
    case RawClaim{t}:
      j
    case Corrupt{t}:
      j

# e on every record; a record this build cannot read stays as it is
def recs(+e: Ev, +c: Nat, +dead: List<&2, Nat>, rs: List<&2, Rec>) -> List<&2, Rec>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case Known{j}:
          Known{job(e, c, dead, j)} <> recs(e, c, dead, t)
        case Raw{x}:
          Raw{x} <> recs(e, c, dead, t)

# an update reads the file: a corrupt one is moved aside first
def heal(bad: Maybe<&2, Nat>, aside: List<&2, Nat>) -> List<&2, Nat>:
  match bad:
    case None{}:
      aside
    case Some{t}:
      t <> aside

def Ev.by(e: Ev) -> Maybe<&2, Nat>:
  match e:
    case Create{p, s}:
      Some{p}
    case Take{p}:
      Some{p}
    case Recover{p}:
      Some{p}
    case Finish{p, i, o}:
      Some{p}
    case Abort{p}:
      Some{p}
    case Die{p}:
      Some{p}
    case Cancel{p, i}:
      Some{p}
    case Resume{p, i}:
      Some{p}
    case Tick{d}:
      None{}
    case RawJob{t}:
      None{}
    case RawClaim{t}:
      None{}
    case Corrupt{t}:
      None{}

# a dead process does nothing
def step.alive(dead: Bool, a: S, s: S) -> S:
  match dead:
    case False{}:
      a
    case True{}:
      s

# another writer adds to a file it can read
def step.raw(bad: Maybe<&2, Nat>, a: S, s: S) -> S:
  match bad:
    case None{}:
      a
    case Some{t}:
      s

# the event of a process that is alive
def step(s: S, +e: Ev) -> S:
  match s:
    case S{+bad, +rs, +rd, +dead, +c, +n, +aside}:
      match e:
        case Create{p, sc}:
          step.alive(has(p, dead), S{None{}, List.append(&2, Rec, rs, [Known{Job{n, sc, Active{}, Some{first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}}}]), rd, dead, c, 1n+n, heal(bad, aside)}, S{bad, rs, rd, dead, c, n, aside})
        case Take{p}:
          step.alive(has(p, dead), S{None{}, recs(e, c, dead, rs), rd, dead, c, n, heal(bad, aside)}, S{bad, rs, rd, dead, c, n, aside})
        case Recover{p}:
          step.alive(has(p, dead), S{None{}, recs(e, c, dead, rs), rd, dead, c, n, heal(bad, aside)}, S{bad, rs, rd, dead, c, n, aside})
        case Finish{p, i, o}:
          step.alive(has(p, dead), S{None{}, recs(e, c, dead, rs), rd, dead, c, n, heal(bad, aside)}, S{bad, rs, rd, dead, c, n, aside})
        case Abort{p}:
          step.alive(has(p, dead), S{bad, recs(e, c, dead, rs), rd, dead, c, n, aside}, S{bad, rs, rd, dead, c, n, aside})
        case Die{p}:
          S{bad, recs(e, c, dead, rs), rd, p <> dead, c, n, aside}
        case Cancel{p, i}:
          step.alive(has(p, dead), S{bad, recs(e, c, dead, rs), rd, dead, c, n, aside}, S{bad, rs, rd, dead, c, n, aside})
        case Resume{p, i}:
          step.alive(has(p, dead), S{bad, recs(e, c, dead, rs), rd, dead, c, n, aside}, S{bad, rs, rd, dead, c, n, aside})
        case Tick{d}:
          S{bad, rs, rd, dead, Nat.add(c, d), n, aside}
        case RawJob{t}:
          step.raw(bad, S{None{}, List.append(&2, Rec, rs, [Raw{t}]), rd, dead, c, n, aside}, S{bad, rs, rd, dead, c, n, aside})
        case RawClaim{t}:
          step.raw(bad, S{None{}, rs, List.append(&2, Nat, rd, [t]), dead, c, n, aside}, S{bad, rs, rd, dead, c, n, aside})
        case Corrupt{t}:
          S{Some{t}, Nil{}, Nil{}, dead, c, n, aside}

# the state after evs, from s
def go(evs: List<&2, Ev>, s: S) -> S:
  match evs:
    case Nil{}:
      s
    case e <> rest:
      go(rest, step(s, e))

def run(evs: List<&2, Ev>) -> S:
  go(evs, S.empty())

# What the laws speak of
# ----------------------

def S.recs(s: S) -> List<&2, Rec>:
  match s:
    case S{b, rs, rd, dead, c, n, a}:
      rs

def S.rawd(s: S) -> List<&2, Nat>:
  match s:
    case S{b, rs, rd, dead, c, n, a}:
      rd

def S.bad(s: S) -> Maybe<&2, Nat>:
  match s:
    case S{b, rs, rd, dead, c, n, a}:
      b

def S.dead(s: S) -> List<&2, Nat>:
  match s:
    case S{b, rs, rd, dead, c, n, a}:
      dead

def S.aside(s: S) -> List<&2, Nat>:
  match s:
    case S{b, rs, rd, dead, c, n, a}:
      a

# the number of failed runs the job counted in a row, the newest first: up
# to its last good run or resume
def trail(h: List<&2, Mark>) -> Nat:
  match h:
    case Nil{}:
      0n
    case m <> t:
      match m:
        case MWin{}:
          0n
        case MReset{}:
          0n
        case MLoss{}:
          1n+trail(t)

# Ev.is_corrupt: the event that destroys the file (not a step of ours)
def Ev.is_corrupt(e: Ev) -> Bool:
  match e:
    case Corrupt{t}:
      True{}
    case Create{p, s}:
      False{}
    case Take{p}:
      False{}
    case Recover{p}:
      False{}
    case Finish{p, i, o}:
      False{}
    case Abort{p}:
      False{}
    case Die{p}:
      False{}
    case Cancel{p, i}:
      False{}
    case Resume{p, i}:
      False{}
    case Tick{d}:
      False{}
    case RawJob{t}:
      False{}
    case RawClaim{t}:
      False{}

# Ev.is_user: a user action (only these may restart a stopped job)
def Ev.is_user(e: Ev) -> Bool:
  match e:
    case Cancel{p, i}:
      True{}
    case Resume{p, i}:
      True{}
    case Create{p, s}:
      True{}
    case Take{p}:
      False{}
    case Recover{p}:
      False{}
    case Finish{p, i, o}:
      False{}
    case Abort{p}:
      False{}
    case Die{p}:
      False{}
    case Tick{d}:
      False{}
    case RawJob{t}:
      False{}
    case RawClaim{t}:
      False{}
    case Corrupt{t}:
      False{}

def claim_of.pick(b: Bool, cl: Maybe<&2, Claim>, r: Maybe<&2, Claim>) -> Maybe<&2, Claim>:
  match b:
    case True{}:
      cl
    case False{}:
      r

# the claim on record of the first job with id i
def claim_of(+i: Nat, rs: List<&2, Rec>) -> Maybe<&2, Claim>:
  match rs:
    case Nil{}:
      None{}
    case r <> t:
      match r:
        case Raw{x}:
          claim_of(i, t)
        case Known{+j}:
          claim_of.pick(Nat.is_eq(Job.id(j), i), Job.claim(j), claim_of(i, t))

def status_of.pick(b: Bool, st: Status, r: Maybe<&2, Status>) -> Maybe<&2, Status>:
  match b:
    case True{}:
      Some{st}
    case False{}:
      r

# the status of the first job with id i
def status_of(+i: Nat, rs: List<&2, Rec>) -> Maybe<&2, Status>:
  match rs:
    case Nil{}:
      None{}
    case r <> t:
      match r:
        case Raw{x}:
          status_of(i, t)
        case Known{+j}:
          status_of.pick(Nat.is_eq(Job.id(j), i), Job.status(j), status_of(i, t))

# a job with id i is in rs
def has_job(+i: Nat, rs: List<&2, Rec>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> t:
      match r:
        case Raw{x}:
          has_job(i, t)
        case Known{j}:
          Bool.or(Nat.is_eq(Job.id(j), i), has_job(i, t))

# the raw record t is in rs
def has_raw(+t: Nat, rs: List<&2, Rec>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> rest:
      match r:
        case Raw{x}:
          Bool.or(Nat.is_eq(x, t), has_raw(t, rest))
        case Known{j}:
          has_raw(t, rest)

# The laws' predicates
# --------------------

# the claim on record is o's
def Owns(cl: Maybe<&2, Claim>, +o: Nat) -> Type:
  match cl:
    case None{}:
      Empty
    case Some{x}:
      match x:
        case Claim{occ, w}:
          {w == o : Nat}

# at most one process runs the job, and that run holds the claim on record
def Held(rs: List<&2, Nat>, +cl: Maybe<&2, Claim>) -> Type:
  match rs:
    case Nil{}:
      Unit
    case o <> t:
      match t:
        case Nil{}:
          Owns(cl, o)
        case x <> u:
          Empty

# the occurrences after x fall strictly
def DescFrom(+x: Nat, t: List<&2, Nat>) -> Type:
  match t:
    case Nil{}:
      Unit
    case +y <> u:
      ({Nat.is_lt(y, x) == True{} : Bool} & DescFrom(y, u))

# the occurrences that started fall strictly, the newest first: none
# started twice
def Desc(ss: List<&2, Nat>) -> Type:
  match ss:
    case Nil{}:
      Unit
    case +x <> t:
      DescFrom(x, t)

# a one-shot started at most once
def OnceOnce(s: Sched, ss: List<&2, Nat>) -> Type:
  match s:
    case Once{d}:
      match ss:
        case Nil{}:
          Unit
        case x <> t:
          {t == Nil{} : List<&2, Nat>}
    case Every{k}:
      Unit

def Fires(j: Job) -> Type:
  match j:
    case Job{i, +s, st, nx, k, +cl, rs, +ss, h}:
      (Held(rs, cl) & (Desc(ss) & OnceOnce(s, ss)))

def FiresAll(rs: List<&2, Rec>) -> Type:
  match rs:
    case Nil{}:
      Unit
    case r <> t:
      match r:
        case Known{j}:
          (Fires(j) & FiresAll(t))
        case Raw{x}:
          FiresAll(t)

# an active job has fewer failures in a row than the cap
def Act(st: Status, +n: Nat) -> Type:
  match st:
    case Active{}:
      {Nat.is_lt(n, CAP()) == True{} : Bool}
    case Paused{}:
      Unit
    case Finished{}:
      Unit
    case Cancelled{}:
      Unit

def Stops(j: Job) -> Type:
  match j:
    case Job{i, s, st, nx, k, cl, rs, ss, +h}:
      ({Nat.is_le(trail(h), CAP()) == True{} : Bool} & Act(st, trail(h)))

def StopsAll(rs: List<&2, Rec>) -> Type:
  match rs:
    case Nil{}:
      Unit
    case r <> t:
      match r:
        case Known{j}:
          (Stops(j) & StopsAll(t))
        case Raw{x}:
          StopsAll(t)

# a finished one-shot has no run
def EndsOf(s: Sched, st: Status, rs: List<&2, Nat>) -> Type:
  match s:
    case Once{d}:
      match st:
        case Finished{}:
          {rs == Nil{} : List<&2, Nat>}
        case Active{}:
          Unit
        case Paused{}:
          Unit
        case Cancelled{}:
          Unit
    case Every{n}:
      Unit

def Ends(j: Job) -> Type:
  match j:
    case Job{i, s, st, nx, k, cl, rs, ss, h}:
      EndsOf(s, st, rs)

def EndsAll(rs: List<&2, Rec>) -> Type:
  match rs:
    case Nil{}:
      Unit
    case r <> t:
      match r:
        case Known{j}:
          (Ends(j) & EndsAll(t))
        case Raw{x}:
          EndsAll(t)

# every record of s the step to s2 does not destroy is kept: a raw job
# record t (byte for byte), a job i, a raw claim record t, the corrupt file
# t (still in place or moved aside), a file moved aside t
def Keeps(+t: Nat, +i: Nat, +s: S, +s2: S) -> Type:
  (({has_raw(t, S.recs(s)) == True{} : Bool} -> {has_raw(t, S.recs(s2)) == True{} : Bool}) &
  (({has_job(i, S.recs(s)) == True{} : Bool} -> {has_job(i, S.recs(s2)) == True{} : Bool}) &
  (({has(t, S.rawd(s)) == True{} : Bool} -> {has(t, S.rawd(s2)) == True{} : Bool}) &
  (({S.bad(s) == Some{t} : Maybe<&2, Nat>} -> Or({S.bad(s2) == Some{t} : Maybe<&2, Nat>}, {has(t, S.aside(s2)) == True{} : Bool})) &
  ({has(t, S.aside(s)) == True{} : Bool} -> {has(t, S.aside(s2)) == True{} : Bool})))))

# a paused job i stays paused (or is gone with a corrupt file)
def StaysPaused(+i: Nat, +s: S, +s2: S) -> Type:
  {status_of(i, S.recs(s)) == Some{Paused{}} : Maybe<&2, Status>} -> Or({status_of(i, S.recs(s2)) == Some{Paused{}} : Maybe<&2, Status>}, {status_of(i, S.recs(s2)) == None{} : Maybe<&2, Status>})
