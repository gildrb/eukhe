# eukhe: lemmas of the cron_job proofs
# The model's leave of the runs (Cr.drop) is the spec's drop_spec.

import Base
import ../../bend/cron.bend as Cr
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
