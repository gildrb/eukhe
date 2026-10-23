# eukhe: lemmas the proofs of area cron share: bool

import Base

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

# A recovery keeps the invariant
# ------------------------------

def pc.no_clear(b: Bool, +hd: Bool, live: {hd == False{} : Bool}) -> {Bool.or(Bool.and(b, Bool.not(Bool.or(b, False{}))), hd) == False{} : Bool}:
  match b:
    case True{}:
      live
    case False{}:
      live

# A pass that unwinds, or a process that dies, keeps the invariant
# ----------------------------------------------------------------

def pc.or_ff(a: Bool, +b: Bool, ha: {a == False{} : Bool}, hb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case True{}:
      cron.pc.absurd({Bool.or(True{}, b) == False{} : Bool}, ha)
    case False{}:
      hb

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
