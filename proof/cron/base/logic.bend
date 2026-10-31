# eukhe: lemmas the proofs of area cron share: logic

import Base
import ../../../bend/cron.bend as Cr

# ---- cron ----

# proof_cron: the cron laws of LAWS.bend section cron (D2). Every event keeps an
# invariant of the reachable states, job by job (`pc.G`): at most one
# process runs a job, its run holds the claim on record and its process
# is alive; the occurrences that started fall strictly and lie at or
# before the clock and before the next run; a one-shot that started has
# no next run; the failures in a row match the job's counted results and
# stay under the cap while the job is active; a finished one-shot has no
# run. From it: `cron_fires_once`, `cron_once_finished_after_end` and the
# first part of `cron_backoff_bounded`. The other laws are about one step
# from any state: `cron_never_drops`, `cron_claim_owned`, and the rest of
# `cron_backoff_bounded`.

# Logic and numbers
# -----------------

def cron.pc.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def cron.pc.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : cron.pc.BD(_, Unit, A)
  Unit{}

def cron.pc.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : cron.pc.BD(_, A, Unit)
  Unit{}

def cron.pc.or_false_r(a: Bool, h: {Bool.or(a, False{}) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

# ---- cron_step ----

# proof_cron_step: the cron laws of LAWS.bend section cron (D2) about one step from
# any state (bend/cron.bend): no step but the file's corruption drops a
# record (`cron_never_drops`); a step of p removes the claim of o only when
# o is p or dead (`cron_claim_owned`); a paused job stays paused through
# every step that is not a user action, and the failure backoff never
# shrinks (the rest of `cron_backoff_bounded`). The invariant laws are in
# PROOF.bend section cron.

# Logic, from PROOF.bend section cron
# --------------------------------

def cron_step.pc.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  cron.pc.absurd(A, e)

def cron.pc.eq_of(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      cron.pc.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      cron.pc.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      +e = cron.pc.eq_of(p, q, h)
      %e : {1n+p == 1n+_ : Nat}
      {==}

def pc.Below(+x: Nat, nx: Maybe<&2, Nat>) -> Type:
  match nx:
    case None{}:
      Unit
    case Some{n}:
      {Nat.is_lt(x, n) == True{} : Bool}

# The invariant of a job
# ----------------------

# the processes that run the job are alive
def pc.Live(rs: List<&2, Nat>, +dead: List<&2, Nat>) -> Type:
  match rs:
    case Nil{}:
      Unit
    case +o <> t:
      ({Cr.has(o, dead) == False{} : Bool} & pc.Live(t, dead))

# the newest occurrence that started is at or before the clock and
# before the next run
def pc.Top(ss: List<&2, Nat>, +c: Nat, +nx: Maybe<&2, Nat>) -> Type:
  match ss:
    case Nil{}:
      Unit
    case +x <> t:
      ({Nat.is_le(x, c) == True{} : Bool} & pc.Below(x, nx))

# Shapes the invariant keeps
# --------------------------

def pc.top_none(+ss: List<&2, Nat>, +c: Nat, -nx: Maybe<&2, Nat>, t: pc.Top(ss, c, nx)) -> pc.Top(ss, c, None{}):
  match ss:
    case Nil{}:
      Unit{}
    case +x <> +u:
      (a, b) = t
      (a, Unit{})

def pc.dead_after(e: Cr.Ev, +dead: List<&2, Nat>) -> List<&2, Nat>:
  match e:
    case Cr.Die{p}:
      p <> dead
    case Cr.Take{p}:
      dead
    case Cr.Create{p, s}:
      dead
    case Cr.Recover{p}:
      dead
    case Cr.Finish{p, i, o}:
      dead
    case Cr.Abort{p}:
      dead
    case Cr.Cancel{p, i}:
      dead
    case Cr.Resume{p, i}:
      dead
    case Cr.Tick{d}:
      dead
    case Cr.RawJob{t}:
      dead
    case Cr.RawClaim{t}:
      dead
    case Cr.Corrupt{t}:
      dead
    case Cr.Pause{p, i}:
      dead
    case Cr.Stop{p, i}:
      dead
    case Cr.Delete{p, i}:
      dead
    case Cr.Edit{p, i, k}:
      dead

def cron.pc.void(-A: Type, e: Empty) -> A:
  match e:

def cron.pc.MD(m: Maybe<&2, Nat>, A: Type) -> Type:
  match m:
    case None{}:
      A
    case Some{x}:
      Unit

def pc.some_none(-A: Type, -x: Nat, e: {Some{x} == None{} : Maybe<&2, Nat>}) -> A:
  %e : cron.pc.MD(_, A)
  Unit{}

# a one-shot that started has no next run
def pc.OnceG(s: Cr.Sched, ss: List<&2, Nat>, +nx: Maybe<&2, Nat>) -> Type:
  match s:
    case Cr.Once{d}:
      match ss:
        case Nil{}:
          Unit
        case x <> t:
          ({t == Nil{} : List<&2, Nat>} & {nx == None{} : Maybe<&2, Nat>})
    case Cr.Every{q}:
      Unit

def pc.Act2(st: Cr.Status, +k: Nat) -> Data:
  match st:
    case Cr.Active{}:
      {Nat.is_lt(k, Cr.CAP()) == True{} : Bool}
    case Cr.Paused{}:
      {Nat.is_le(k, Cr.CAP()) == True{} : Bool}
    case Cr.Finished{}:
      {Nat.is_le(k, Cr.CAP()) == True{} : Bool}
    case Cr.Cancelled{}:
      {Nat.is_le(k, Cr.CAP()) == True{} : Bool}

# the failures in a row are the counted ones, under the cap while active
def pc.Cnt(+st: Cr.Status, +k: Nat, +h: List<&2, Cr.Mark>) -> Type:
  ({k == Cr.trail(h) : Nat} & pc.Act2(st, k))

def pc.G(+c: Nat, +dead: List<&2, Nat>, j: Cr.Job) -> Type:
  match j:
    case Cr.Job{i, +s, +st, +nx, k, cl, +rs, +ss, h}:
      (Cr.Held(rs, cl) & (pc.Live(rs, dead) & (Cr.Desc(ss) & (pc.Top(ss, c, nx) & (pc.OnceG(s, ss, nx) & (pc.Cnt(st, k, h) & Cr.EndsOf(s, st, rs)))))))

def pc.AllG(+c: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>) -> Type:
  match rs:
    case Nil{}:
      Unit
    case r <> t:
      match r:
        case Cr.Known{j}:
          (pc.G(c, dead, j) & pc.AllG(c, dead, t))
        case Cr.Raw{x}:
          pc.AllG(c, dead, t)

def pc.Inv(s: Cr.S) -> Type:
  match s:
    case Cr.S{b, rs, rd, dead, c, n, a}:
      pc.AllG(c, dead, rs)

def pc.once_none(+s: Cr.Sched, +ss: List<&2, Nat>, -nx: Maybe<&2, Nat>, o: pc.OnceG(s, ss, nx)) -> pc.OnceG(s, ss, None{}):
  match s:
    case Cr.Once{d}:
      match ss:
        case Nil{}:
          Unit{}
        case +x <> +t:
          (a, b) = o
          (a, {==})
    case Cr.Every{q}:
      Unit{}

# Every event keeps the invariant
# -------------------------------

# what an event needs of its process: a claim, that it is alive
def pc.Alive(e: Cr.Ev, +dead: List<&2, Nat>) -> Data:
  match e:
    case Cr.Take{p}:
      {Cr.has(p, dead) == False{} : Bool}
    case Cr.Create{p, s}:
      Unit
    case Cr.Recover{p}:
      Unit
    case Cr.Finish{p, i, o}:
      Unit
    case Cr.Abort{p}:
      Unit
    case Cr.Die{p}:
      Unit
    case Cr.Cancel{p, i}:
      Unit
    case Cr.Resume{p, i}:
      Unit
    case Cr.Tick{d}:
      Unit
    case Cr.RawJob{t}:
      Unit
    case Cr.RawClaim{t}:
      Unit
    case Cr.Corrupt{t}:
      Unit
    case Cr.Pause{p, i}:
      Unit
    case Cr.Stop{p, i}:
      Unit
    case Cr.Delete{p, i}:
      Unit
    case Cr.Edit{p, i, k}:
      Unit

def pc.once_empty(+s: Cr.Sched, -nx: Maybe<&2, Nat>) -> pc.OnceG(s, Nil{}, nx):
  match s:
    case Cr.Once{d}:
      Unit{}
    case Cr.Every{q}:
      Unit{}
