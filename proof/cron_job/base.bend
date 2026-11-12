# eukhe: lemmas of the cron_job proofs
# The model's leave of the runs (Cr.drop) is the spec's drop_spec; its
# membership (Cr.has) and its clear verdict (Cr.clears) are the spec's.

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron_job.bend as CronJob
import ../../laws/cron_terms.bend as CronTerms
import ../../laws/cron_step.bend as CronStep

def cj.keep(b: Bool, x: Nat, r: List<&2, Nat>) -> {Cr.drop.put(b, x, r) == CronStep.keep_run_spec(b, x, r) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cj.drop(+p: Nat, xs: List<&2, Nat>) -> {Cr.drop(p, xs) == CronStep.drop_spec(p, xs) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %cj.drop(p, t) : {Cr.drop.put(Nat.is_eq(x, p), x, Cr.drop(p, t)) == CronStep.keep_run_spec(Nat.is_eq(x, p), x, _) : List<&2, Nat>}
      cj.keep(Nat.is_eq(x, p), x, Cr.drop(p, t))

def cj.has(+p: Nat, xs: List<&2, Nat>) -> {Cr.has(p, xs) == CronTerms.has_spec(p, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %cj.has(p, t) : {Bool.or(Nat.is_eq(x, p), Cr.has(p, t)) == Bool.or(Nat.is_eq(x, p), _) : Bool}
      {==}

def cj.clears(+p: Nat, +o: Nat, +rs: List<&2, Nat>, +dead: List<&2, Nat>) -> {Cr.clears(p, o, rs, dead) == CronJob.clears_spec(p, o, rs, dead) : Bool}:
  %cj.has(p, rs) : {Bool.or(Bool.and(Nat.is_eq(o, p), Bool.not(Cr.has(p, rs))), Cr.has(o, dead)) == Bool.or(Bool.and(Nat.is_eq(o, p), Bool.not(_)), CronTerms.has_spec(o, dead)) : Bool}
  %cj.has(o, dead) : {Bool.or(Bool.and(Nat.is_eq(o, p), Bool.not(Cr.has(p, rs))), Cr.has(o, dead)) == Bool.or(Bool.and(Nat.is_eq(o, p), Bool.not(Cr.has(p, rs))), _) : Bool}
  {==}
