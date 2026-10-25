# eukhe: the proof of LAW cron_resume_exact
# A case split on the status and the schedule.

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../laws/cron_store.bend as CronStore

def cx.resume_plan(p: CS.Plan, +now: Nat) -> {CS.resume.plan(p, now) == CronStore.resume_spec.plan(p, now) : CS.Again}:
  match p:
    case CS.POnce{}:
      {==}
    case CS.PEvery{ms}:
      {==}
    case CS.PRule{}:
      {==}

def cx.resume(f: CS.Fact, +now: Nat) -> {CS.resume(f, now) == CronStore.resume_spec(f, now) : CS.Again}:
  match f:
    case CS.Fact{st, p, nx, k}:
      match st:
        case Cr.Active{}:
          cx.resume_plan(p, now)
        case Cr.Paused{}:
          cx.resume_plan(p, now)
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def CronStore.cron_resume_exact(f, n):
  cx.resume(f, n)
