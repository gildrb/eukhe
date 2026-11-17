# eukhe: the proof of LAW headless_task_stands_with_exit_code
#
# PROOF: headless_task_exit_stands gives the standing exit with the code
# Hx.code of the cause; headless_exit's exit for g is Hx.verdict of its
# cause, whose code is that same Hx.code, so both sides compute to
# Hx.code(Hx.cause(g)).

import Base
import ../../bend/headless_exit.bend as Hx
import ../../bend/headless_task.bend as Ht
import ../../spec/durable/headless_task.bend as SpT
import ../../laws/headless_task.bend as HeadlessTask
import ./headless_task_exit_stands.bend as PHeadlessTaskExitStands

def HeadlessTask.headless_task_stands_with_exit_code(g, a, r, h, u, k):
  Equal.cong(Ht.Verdict, Nat, v => SpT.code_of(v), Ht.decide(Ht.Facts{HeadlessTask.exit_cause(Hx.decide(g)), a, r}), Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{HeadlessTask.exit_cause(Hx.decide(g)), a, r})), Ht.Stands{}}, HeadlessTask.headless_task_exit_stands(Ht.Facts{HeadlessTask.exit_cause(Hx.decide(g)), a, r}, h, u, k))
