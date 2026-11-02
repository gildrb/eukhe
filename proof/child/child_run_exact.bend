# eukhe: the proof of LAW child_run_exact
# Event by event: each step of the task is the rule's (child_step_exact).

import Base
import ../../bend/child.bend as Ch
import ../../laws/child/run.bend as ChildRun
import ./child_step_exact.bend as PSE

def pcr.run(evs: List<&2, Ch.Ev>, +cfg: Ch.Cfg, +s: Ch.St) -> {Ch.run(evs, cfg, s) == ChildRun.chr_run(evs, cfg, s) : Ch.St}:
  match evs:
    case Nil{}:
      {==}
    case +e <> r:
      %PSE.pcs.step(cfg, s, e) : {Ch.run(r, cfg, Ch.step(cfg, s, e)) == ChildRun.chr_run(r, cfg, _) : Ch.St}
      pcr.run(r, cfg, Ch.step(cfg, s, e))

def ChildRun.child_run_exact(evs, cfg, s):
  pcr.run(evs, cfg, s)
