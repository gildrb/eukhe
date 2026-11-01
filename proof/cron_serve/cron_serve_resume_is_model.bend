# eukhe: the proof of LAW cron_serve_resume_is_model
# serve is the spec (cron_serve_exact); the spec answers the job at k with
# the resume when its id is n (LPM.pm.resume_at); applied, that is the
# model's resume at its clock (cron_resume_refines), else the job stays.

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_serve.bend as Sv
import ../../laws/cron.bend as Cron
import ../../laws/cron_store.bend as CronStore
import ../../laws/cron_serve/serve.bend as CronServe
import ../../laws/cron_serve/model.bend as CronServeModel
import ./base/model.bend as LPM
import ./base/safety.bend as LSf
import ./base/logic.bend as LG
import ./base/exact.bend as LSx

def pmu.v(+b: Bool, +j: Cr.Job, +p: Nat, +c: Nat) -> {CronServeModel.cm_applied(CronServe.sv_if(b, Sv.JAgain{CronStore.resume_spec(Cron.fact_of(j, 60000n), Nat.mul(c, 60000n))}), j, p, False{}) == Cron.view(Cr.job.pick(b, Cr.resume(c, j), j), 60000n) : Cron.View()}:
  match b:
    case True{}:
      Cron.cron_resume_refines(59999n, c, j)
    case False{}:
      {==}

def CronServeModel.cron_serve_resume_is_model(rs, cs, runs, p, n, c, dead, k, j, at):
  (CronServe.sv_if(Nat.is_eq(Cr.Job.id(j), n), Sv.JAgain{CronStore.resume_spec(Cron.fact_of(j, 60000n), Nat.mul(c, 60000n))}), (Equal.trans(Maybe<&2, Sv.JOut>, CronServeModel.cm_at(Sv.serve(runs, p, Sv.Parsed{CronServeModel.cm_pj(rs), cs}, Sv.OResume{n, Nat.mul(c, 60000n)}), k), CronServeModel.cm_at(CronServe.sv_serve(runs, p, Sv.Parsed{CronServeModel.cm_pj(rs), cs}, Sv.OResume{n, Nat.mul(c, 60000n)}), k), Some{CronServe.sv_if(Nat.is_eq(Cr.Job.id(j), n), Sv.JAgain{CronStore.resume_spec(Cron.fact_of(j, 60000n), Nat.mul(c, 60000n))})}, LPM.pm.exact(runs, p, CronServeModel.cm_pj(rs), cs, Sv.OResume{n, Nat.mul(c, 60000n)}, k), LPM.pm.resume_at(rs, k, j, n, Nat.mul(c, 60000n), at)), pmu.v(Nat.is_eq(Cr.Job.id(j), n), j, p, c)))
