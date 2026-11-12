# eukhe: the proof of LAW cron_finish_unowned
# The premise `run` takes the model's finish step to the claim on record
# (Cr.finish.run, then Cr.finish.claim with p out of the runs). No claim:
# the job is built again with those runs, as Cr.unrun builds it. A claim
# of w: the premise `unowned` says w is not p (cfu.own), and the claim
# stays with the job.

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron.bend as Cron
import ../../laws/cron_terms.bend as CronTerms
import ../../laws/cron_job.bend as CronJob
import ../cron/base/logic.bend as LALogic

# a claim that is not p's stays, and the job with it
def cfu.own(b: Bool, +x: Cr.Claim, +c: Nat, +o: Cr.Out, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, no: {b == False{} : Bool}) -> {Cr.finish.own(b, x, c, o, i, s, st, nx, k, rs, ss, h) == Cr.Job{i, s, st, nx, k, Some{x}, rs, ss, h} : Cr.Job}:
  match b:
    case False{}:
      {==}
    case True{}:
      LALogic.cron.pc.absurd({Cr.finish.own(True{}, x, c, o, i, s, st, nx, k, rs, ss, h) == Cr.Job{i, s, st, nx, k, Some{x}, rs, ss, h} : Cr.Job}, no)

def CronJob.cron_finish_unowned(p, c, o, j, run, unowned):
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match cl:
        case None{}:
          %Equal.sym(Bool, Cr.has(p, rs), True{}, run) : {Cr.finish.run(_, p, c, o, i, s, st, nx, k, None{}, rs, ss, h) == Cr.Job{i, s, st, nx, k, None{}, Cr.drop(p, rs), ss, h} : Cr.Job}
          {==}
        case Some{x}:
          match x:
            case Cr.Claim{occ, w}:
              %Equal.sym(Bool, Cr.has(p, rs), True{}, run) : {Cr.finish.run(_, p, c, o, i, s, st, nx, k, Some{Cr.Claim{occ, w}}, rs, ss, h) == Cr.Job{i, s, st, nx, k, Some{Cr.Claim{occ, w}}, Cr.drop(p, rs), ss, h} : Cr.Job}
              cfu.own(Nat.is_eq(w, p), Cr.Claim{occ, w}, c, o, i, s, st, nx, k, Cr.drop(p, rs), ss, h, unowned)
