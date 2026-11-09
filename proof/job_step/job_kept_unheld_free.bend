# eukhe: the proof of LAW job_kept_unheld_free
# The check of a slot whose id is not held passes at once.

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep
import ./base.bend as LA

def JobStep.job_kept_unheld_free(i, r, s, keep, free):
  match s:
    case Jb.Slot{+h, +q}:
      %Equal.sym(Bool, Jb.elem(keep, i), False{}, free) : {Bool.and(Bool.or(Bool.not(_), Bool.and(Nat.is_eq(i, h), Jb.b.eq(r, q))), True{}) == True{} : Bool}
      {==}
