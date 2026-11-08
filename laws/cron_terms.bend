# eukhe: the laws of area cron (the model's terms, pinned)
#
# The D2 laws and the D2.2 refines laws of laws/cron.bend read the model
# (bend/cron.bend) through its small terms: membership `has`, the job and
# state accessors, what an event is, the claim on record of a job, the
# failure pause and `later`. A third fresh adversary (SpecCheckCron3) made
# `has` always False: every law still checked, cron_recover_refines read
# `has` on both sides and cron_finish_refines became vacuous (a model that
# ignored failures passed). Each term is pinned here to a spec in the laws.

import Base
import ../bend/cron.bend as Cr

# p is one of xs
def has_spec(+p: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(Nat.is_eq(x, p), has_spec(p, t))

def job_id_spec(j: Cr.Job) -> Nat:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      i

def job_claim_spec(j: Cr.Job) -> Maybe<&2, Cr.Claim>:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      cl

def job_status_spec(j: Cr.Job) -> Cr.Status:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      st

def recs_spec(s: Cr.S) -> List<&2, Cr.Rec>:
  match s:
    case Cr.S{b, rs, rd, dead, c, n, a}:
      rs

def dead_spec(s: Cr.S) -> List<&2, Nat>:
  match s:
    case Cr.S{b, rs, rd, dead, c, n, a}:
      dead

# the process an event is by (none: time, another writer, a corrupt file)
def by_spec(e: Cr.Ev) -> Maybe<&2, Nat>:
  match e:
    case Cr.Create{p, s}:
      Some{p}
    case Cr.Take{p}:
      Some{p}
    case Cr.Recover{p}:
      Some{p}
    case Cr.Finish{p, i, o}:
      Some{p}
    case Cr.Abort{p}:
      Some{p}
    case Cr.Die{p}:
      Some{p}
    case Cr.Cancel{p, i}:
      Some{p}
    case Cr.Resume{p, i}:
      Some{p}
    case Cr.Tick{d}:
      None{}
    case Cr.RawJob{t}:
      None{}
    case Cr.RawClaim{t}:
      None{}
    case Cr.Corrupt{t}:
      None{}
    case Cr.Pause{p, i}:
      Some{p}
    case Cr.Stop{p, i}:
      Some{p}
    case Cr.Delete{p, i}:
      Some{p}
    case Cr.Edit{p, i, k}:
      Some{p}

def corrupt_spec(e: Cr.Ev) -> Bool:
  match e:
    case Cr.Create{p, s}:
      False{}
    case Cr.Take{p}:
      False{}
    case Cr.Recover{p}:
      False{}
    case Cr.Finish{p, i, o}:
      False{}
    case Cr.Abort{p}:
      False{}
    case Cr.Die{p}:
      False{}
    case Cr.Cancel{p, i}:
      False{}
    case Cr.Resume{p, i}:
      False{}
    case Cr.Tick{d}:
      False{}
    case Cr.RawJob{t}:
      False{}
    case Cr.RawClaim{t}:
      False{}
    case Cr.Corrupt{t}:
      True{}
    case Cr.Pause{p, i}:
      False{}
    case Cr.Stop{p, i}:
      False{}
    case Cr.Delete{p, i}:
      False{}
    case Cr.Edit{p, i, k}:
      False{}

# a user action: a create, a cancel, a resume, a pause, a stop, a delete,
# an edit
def user_spec(e: Cr.Ev) -> Bool:
  match e:
    case Cr.Create{p, s}:
      True{}
    case Cr.Take{p}:
      False{}
    case Cr.Recover{p}:
      False{}
    case Cr.Finish{p, i, o}:
      False{}
    case Cr.Abort{p}:
      False{}
    case Cr.Die{p}:
      False{}
    case Cr.Cancel{p, i}:
      True{}
    case Cr.Resume{p, i}:
      True{}
    case Cr.Tick{d}:
      False{}
    case Cr.RawJob{t}:
      False{}
    case Cr.RawClaim{t}:
      False{}
    case Cr.Corrupt{t}:
      False{}
    case Cr.Pause{p, i}:
      True{}
    case Cr.Stop{p, i}:
      True{}
    case Cr.Delete{p, i}:
      True{}
    case Cr.Edit{p, i, k}:
      True{}

def claim_spec.pick(b: Bool, cl: Maybe<&2, Cr.Claim>, rest: Maybe<&2, Cr.Claim>) -> Maybe<&2, Cr.Claim>:
  match b:
    case True{}:
      cl
    case False{}:
      rest

# the claim on record of the first readable job with id i
def claim_spec(+i: Nat, rs: List<&2, Cr.Rec>) -> Maybe<&2, Cr.Claim>:
  match rs:
    case Nil{}:
      None{}
    case r <> t:
      match r:
        case Cr.Raw{x}:
          claim_spec(i, t)
        case Cr.Known{j}:
          match j:
            case Cr.Job{+id, s, st, nx, k, cl, ru, ss, h}:
              claim_spec.pick(Nat.is_eq(id, i), cl, claim_spec(i, t))

# the pause in minutes after the k-th failure in a row: 2, 2, 4, 8, 16, 32, then 60
def delay_spec(k: Nat) -> Nat:
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
                case 1n+d:
                  match d:
                    case 0n:
                      16n
                    case 1n+e:
                      match e:
                        case 0n:
                          32n
                        case 1n+f:
                          60n

# the next run after a failure: the pause end u, or a later next run
def later_spec(nx: Maybe<&2, Nat>, +u: Nat) -> Nat:
  match nx:
    case None{}:
      u
    case Some{n}:
      Nat.max(n, u)

# LAW cron_terms_exact: the model's terms the cron laws read mean what they say: membership, a
# job's id, claim and status, a state's records and dead processes, the process an event is by,
# a corrupt file, a user action, the claim on record of a job, the failure pause (2, 2, 4, 8,
# 16, 32, then 60 minutes) and the later of a next run and a pause end
# EXCLUDES: a trivial term (has always False) that makes cron_recover_refines read the model on
#   both sides and cron_finish_refines vacuous, or the D2 laws say less than their names
law cron_terms_exact:
  for +p: Nat
  for +xs: List<&2, Nat>
  for +j: Cr.Job
  for +s: Cr.S
  for +e: Cr.Ev
  for +i: Nat
  for +rs: List<&2, Cr.Rec>
  for +k: Nat
  for +nx: Maybe<&2, Nat>
  for +u: Nat
  {Cr.has(p, xs) == has_spec(p, xs) : Bool} & {Cr.Job.id(j) == job_id_spec(j) : Nat} & {Cr.Job.claim(j) == job_claim_spec(j) : Maybe<&2, Cr.Claim>} & {Cr.Job.status(j) == job_status_spec(j) : Cr.Status} & {Cr.S.recs(s) == recs_spec(s) : List<&2, Cr.Rec>} & {Cr.S.dead(s) == dead_spec(s) : List<&2, Nat>} & {Cr.Ev.by(e) == by_spec(e) : Maybe<&2, Nat>} & {Cr.Ev.is_corrupt(e) == corrupt_spec(e) : Bool} & {Cr.Ev.is_user(e) == user_spec(e) : Bool} & {Cr.claim_of(i, rs) == claim_spec(i, rs) : Maybe<&2, Cr.Claim>} & {Cr.delay(k) == delay_spec(k) : Nat} & {Cr.later(nx, u) == later_spec(nx, u) : Nat}

# The laws' predicates, as Bools
# ------------------------------
# The D2 laws cron_fires_once, cron_once_finished_after_end,
# cron_never_drops and cron_backoff_bounded state a model predicate
# (Cr.FiresAll, Cr.EndsAll, Cr.Keeps, Cr.StopsAll, Cr.StaysPaused): a
# predicate rewritten to `Unit` makes its law vacuous. Each is pinned here,
# both ways, to a Bool in the laws.

# a implies b
def imp_spec(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      True{}

def is_nil_spec(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      False{}

# the claim on record is o's
def owns_spec(cl: Maybe<&2, Cr.Claim>, +o: Nat) -> Bool:
  match cl:
    case None{}:
      False{}
    case Some{x}:
      match x:
        case Cr.Claim{occ, w}:
          Nat.is_eq(w, o)

# at most one process runs the job, and that run holds the claim on record
def held_spec(rs: List<&2, Nat>, cl: Maybe<&2, Cr.Claim>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case o <> t:
      match t:
        case Nil{}:
          owns_spec(cl, o)
        case x <> u:
          False{}

# every occurrence in t is below x, each below the one before
def desc_from_spec(t: List<&2, Nat>, x: Nat) -> Bool:
  match t:
    case Nil{}:
      True{}
    case +y <> u:
      Bool.and(Nat.is_lt(y, x), desc_from_spec(u, y))

# the occurrences that started fall strictly, the newest first
def desc_spec(ss: List<&2, Nat>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case x <> t:
      desc_from_spec(t, x)

# a one-shot started at most once (an interval job any number of times)
def once_once_spec(s: Cr.Sched, ss: List<&2, Nat>) -> Bool:
  match s:
    case Cr.Once{d}:
      match ss:
        case Nil{}:
          True{}
        case x <> t:
          is_nil_spec(t)
    case Cr.Every{k}:
      True{}

def fires_spec(j: Cr.Job) -> Bool:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, +ss, h}:
      Bool.and(held_spec(rs, cl), Bool.and(desc_spec(ss), once_once_spec(s, ss)))

# every job record fires as cron_fires_once says
def fires_all_spec(rs: List<&2, Cr.Rec>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> t:
      match r:
        case Cr.Known{j}:
          Bool.and(fires_spec(j), fires_all_spec(t))
        case Cr.Raw{x}:
          fires_all_spec(t)

# a finished one-shot has no run
def ends_spec(j: Cr.Job) -> Bool:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match s:
        case Cr.Once{d}:
          match st:
            case Cr.Active{}:
              True{}
            case Cr.Paused{}:
              True{}
            case Cr.Finished{}:
              is_nil_spec(rs)
            case Cr.Cancelled{}:
              True{}
        case Cr.Every{n}:
          True{}

def ends_all_spec(rs: List<&2, Cr.Rec>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> t:
      match r:
        case Cr.Known{j}:
          Bool.and(ends_spec(j), ends_all_spec(t))
        case Cr.Raw{x}:
          ends_all_spec(t)

# failed runs after which a job stops
def cap_spec() -> Nat:
  8n

# the failed runs the job counted in a row, the newest first: up to its
# last good run or resume
def trail_spec(h: List<&2, Cr.Mark>) -> Nat:
  match h:
    case Nil{}:
      0n
    case m <> t:
      match m:
        case Cr.MWin{}:
          0n
        case Cr.MLoss{}:
          1n+trail_spec(t)
        case Cr.MReset{}:
          0n

# an active job has fewer failures in a row than the cap
def act_spec(st: Cr.Status, n: Nat) -> Bool:
  match st:
    case Cr.Active{}:
      Nat.is_lt(n, cap_spec())
    case Cr.Paused{}:
      True{}
    case Cr.Finished{}:
      True{}
    case Cr.Cancelled{}:
      True{}

# at most the cap of failures in a row, fewer while active
def stops_spec(j: Cr.Job) -> Bool:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, +h}:
      Bool.and(Nat.is_le(trail_spec(h), cap_spec()), act_spec(st, trail_spec(h)))

def stops_all_spec(rs: List<&2, Cr.Rec>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> t:
      match r:
        case Cr.Known{j}:
          Bool.and(stops_spec(j), stops_all_spec(t))
        case Cr.Raw{x}:
          stops_all_spec(t)

# a job record this build cannot read with bytes t is in rs
def has_raw_spec(+t: Nat, rs: List<&2, Cr.Rec>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> rest:
      match r:
        case Cr.Raw{x}:
          Bool.or(Nat.is_eq(x, t), has_raw_spec(t, rest))
        case Cr.Known{j}:
          has_raw_spec(t, rest)

# a job with id i is in rs
def has_job_spec(+i: Nat, rs: List<&2, Cr.Rec>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> rest:
      match r:
        case Cr.Raw{x}:
          has_job_spec(i, rest)
        case Cr.Known{j}:
          Bool.or(Nat.is_eq(job_id_spec(j), i), has_job_spec(i, rest))

# the file is the corrupt file t
def is_bad_spec(m: Maybe<&2, Nat>, +t: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      Nat.is_eq(x, t)

# the step from s to s2 keeps the raw job record t, the job i, the raw
# claim record t, the corrupt file t (in place or moved aside) and the
# file moved aside t
def keeps_spec(+t: Nat, +i: Nat, s: Cr.S, s2: Cr.S) -> Bool:
  match s:
    case Cr.S{b, +rs, rd, dead, c, n, a}:
      match s2:
        case Cr.S{b2, +rs2, rd2, dead2, c2, n2, +a2}:
          Bool.and(imp_spec(has_raw_spec(t, rs), has_raw_spec(t, rs2)), Bool.and(imp_spec(has_job_spec(i, rs), has_job_spec(i, rs2)), Bool.and(imp_spec(has_spec(t, rd), has_spec(t, rd2)), Bool.and(imp_spec(is_bad_spec(b, t), Bool.or(is_bad_spec(b2, t), has_spec(t, a2))), imp_spec(has_spec(t, a), has_spec(t, a2))))))

def status_spec.pick(b: Bool, st: Cr.Status, rest: Maybe<&2, Cr.Status>) -> Maybe<&2, Cr.Status>:
  match b:
    case True{}:
      Some{st}
    case False{}:
      rest

# the status of the first readable job with id i
def status_spec(+i: Nat, rs: List<&2, Cr.Rec>) -> Maybe<&2, Cr.Status>:
  match rs:
    case Nil{}:
      None{}
    case r <> t:
      match r:
        case Cr.Raw{x}:
          status_spec(i, t)
        case Cr.Known{j}:
          match j:
            case Cr.Job{+id, s, st, nx, k, cl, ru, ss, h}:
              status_spec.pick(Nat.is_eq(id, i), st, status_spec(i, t))

def paused_spec(m: Maybe<&2, Cr.Status>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{st}:
      match st:
        case Cr.Active{}:
          False{}
        case Cr.Paused{}:
          True{}
        case Cr.Finished{}:
          False{}
        case Cr.Cancelled{}:
          False{}

def gone_spec(m: Maybe<&2, Cr.Status>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{st}:
      False{}

# a paused job i stays paused from s to s2, or is gone
def stays_paused_spec(+i: Nat, s: Cr.S, s2: Cr.S) -> Bool:
  match s:
    case Cr.S{b, rs, rd, dead, c, n, a}:
      match s2:
        case Cr.S{b2, +rs2, rd2, dead2, c2, n2, a2}:
          imp_spec(paused_spec(status_spec(i, rs)), Bool.or(paused_spec(status_spec(i, rs2)), gone_spec(status_spec(i, rs2))))

# LAW cron_type_terms_exact: the model's predicates the D2 laws state hold exactly when their Bools in the laws are true: every job record fires once (one run at most, holding the claim; starts falling strictly; a one-shot started at most once); every finished one-shot has no run; every job counts at most the cap (8) of failures in a row, fewer while active; a step keeps every record and file of the five kinds; a paused job stays paused or is gone
# EXCLUDES: a Cr.FiresAll, Cr.EndsAll, Cr.StopsAll, Cr.Keeps or Cr.StaysPaused rewritten to `Unit` (or to any weaker or stronger type), which makes cron_fires_once, cron_once_finished_after_end, cron_backoff_bounded or cron_never_drops vacuous
law cron_type_terms_exact:
  for +rs: List<&2, Cr.Rec>
  for +t: Nat
  for +i: Nat
  for +s: Cr.S
  for +s2: Cr.S
  ((Cr.FiresAll(rs) -> {fires_all_spec(rs) == True{} : Bool}) & ({fires_all_spec(rs) == True{} : Bool} -> Cr.FiresAll(rs))) & ((Cr.EndsAll(rs) -> {ends_all_spec(rs) == True{} : Bool}) & ({ends_all_spec(rs) == True{} : Bool} -> Cr.EndsAll(rs))) & ((Cr.StopsAll(rs) -> {stops_all_spec(rs) == True{} : Bool}) & ({stops_all_spec(rs) == True{} : Bool} -> Cr.StopsAll(rs))) & ((Cr.Keeps(t, i, s, s2) -> {keeps_spec(t, i, s, s2) == True{} : Bool}) & ({keeps_spec(t, i, s, s2) == True{} : Bool} -> Cr.Keeps(t, i, s, s2))) & ((Cr.StaysPaused(i, s, s2) -> {stays_paused_spec(i, s, s2) == True{} : Bool}) & ({stays_paused_spec(i, s, s2) == True{} : Bool} -> Cr.StaysPaused(i, s, s2)))
