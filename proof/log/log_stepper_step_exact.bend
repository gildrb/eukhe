# eukhe: the proof of LAW log_stepper_step_exact
#
# The entry and the spec read the sidecar entries with the same wire
# primitive; a commit's plan is the spec's (log_commit_plan) and the entry
# spells it as the spec does (log_stepper_commit's pl.answer); every other
# path is the same error form and the same state on both sides.

import Base
import ../../bend/log.bend as Lr
import ../../bend/wire.bend as Wr
import ../../bend/ffi_log.bend as FLg
import ../../laws/log.bend as Log
import ./log_commit_plan.bend as PLogCommitPlan
import ./log_stepper_commit.bend as PLogStepperCommit

def lss.commit(x: Lr.Store, +ds: List<&2, Bool>) -> {FLg.reply(Lr.Store.commit(x, ds)) == Log.log_step_entry.commit(x, ds) : FLg.St & String}:
  match x:
    case Lr.Store{+fsync, +main}:
      %Log.log_commit_plan(fsync, main, ds) : {FLg.reply(Lr.Store.commit(Lr.Store{fsync, main}, ds)) == Log.log_answer(_) : FLg.St & String}
      PLogStepperCommit.pl.answer(Lr.Store.commit(Lr.Store{fsync, main}, ds))

def lss.end(b: Bool, x: Lr.Store, ds: List<&2, Bool>) -> {FLg.step.end(b, x, ds) == Log.log_step_entry.end(b, x, ds) : FLg.St & String}:
  match b:
    case True{}:
      lss.commit(x, ds)
    case False{}:
      {==}

def lss.go(x: Lr.Store, r: Wr.Dec<List<&2, Bool>>) -> {FLg.step.go(x, r) == Log.log_step_entry.go(x, r) : FLg.St & String}:
  match r:
    case Wr.Got{ds, rest}:
      lss.end(Wr.end(rest), x, ds)
    case Wr.Bad{}:
      {==}

def Log.log_stepper_step_exact(st, s):
  match st:
    case FLg.Running{x}:
      lss.go(x, Wr.get_list(~Bool, ~Wr.get_bool, s))
    case FLg.Shut{}:
      {==}
