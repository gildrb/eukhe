# eukhe: the proof of LAW task_life_resume_moves_only_running
#
# PROOF: case on the state: every state but a running one resumes to
# itself, and a running one to pending at its checkpoint (both compute); a
# running state contradicts the premise idle.

import Base
import ../../bend/task_life.bend as Tl
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife
import ./base.bend as LB

def TaskLife.task_life_resume_moves_only_running(s, c, idle):
  match s:
    case Tl.Pending{x}:
      ({==}, {==})
    case Tl.Running{x}:
      LB.tlb.absurd_tf({Sp.resumed(Tl.resume(Tl.Running{x})) == Tl.Running{x} : Tl.St} & {Sp.resumed(Tl.resume(Tl.Running{c})) == Tl.Pending{c} : Tl.St}, idle)
    case Tl.Waiting{x, p}:
      ({==}, {==})
    case Tl.Completing{o}:
      ({==}, {==})
    case Tl.Terminal{o}:
      ({==}, {==})
