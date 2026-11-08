# eukhe: the proof of LAW task_life_example
#
# PROOF: closed: each anchor computes.

import Base
import ../../bend/task_life.bend as Tl
import ../../bend/ffi_task_life.bend as FTl
import ../../bend/submission.bend as Sb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife

def TaskLife.task_life_example():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))))
