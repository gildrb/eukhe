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

# a user action: a create, a cancel, a resume
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
