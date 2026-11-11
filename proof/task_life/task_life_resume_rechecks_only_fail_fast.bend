# eukhe: the proof of LAW task_life_resume_rechecks_only_fail_fast
#
# PROOF: case on the state and a wait's policy: only a failFast wait
# resumes with the check (witness: its checkpoint); every other state
# resumes without it, contradicting the premise yes.

import Base
import ../../bend/task_life.bend as Tl
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife
import ./base.bend as LB

def trr.G(s: Tl.St) -> Type:
  Sigma<&1, &1, Nat, k => {s == Tl.Waiting{k, Tl.FailFast{}} : Tl.St}>

def TaskLife.task_life_resume_rechecks_only_fail_fast(s, yes):
  match s:
    case Tl.Pending{x}:
      LB.tlb.absurd_ft(trr.G(Tl.Pending{x}), yes)
    case Tl.Running{x}:
      LB.tlb.absurd_ft(trr.G(Tl.Running{x}), yes)
    case Tl.Waiting{+x, p}:
      match p:
        case Tl.FailFast{}:
          (x, {==})
        case Tl.AllSettled{}:
          LB.tlb.absurd_ft(trr.G(Tl.Waiting{x, Tl.AllSettled{}}), yes)
    case Tl.Completing{o}:
      LB.tlb.absurd_ft(trr.G(Tl.Completing{o}), yes)
    case Tl.Terminal{o}:
      LB.tlb.absurd_ft(trr.G(Tl.Terminal{o}), yes)

# Join
