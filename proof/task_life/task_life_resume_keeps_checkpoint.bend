# eukhe: the proof of LAW task_life_resume_keeps_checkpoint
#
# PROOF: case on the state: each resumed state computes, with the same
# checkpoint and outcome, and none is running.

import Base
import ../../bend/task_life.bend as Tl
import ../../bend/ffi_task_life.bend as FTl
import ../../bend/submission.bend as Sb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife

def TaskLife.task_life_resume_keeps_checkpoint(s):
  match s:
    case Tl.Pending{c}:
      ({==}, ({==}, {==}))
    case Tl.Running{c}:
      ({==}, ({==}, {==}))
    case Tl.Waiting{c, p}:
      ({==}, ({==}, {==}))
    case Tl.Completing{o}:
      ({==}, ({==}, {==}))
    case Tl.Terminal{o}:
      ({==}, ({==}, {==}))
