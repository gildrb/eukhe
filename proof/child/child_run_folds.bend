# eukhe: the proof of LAW child_run_folds
# The run of no event computes; a history and one more event: by induction
# on the history, from the state after its first event (pr.snoc).

import Base
import ../../bend/child.bend as Ch
import ../../laws/child/run.bend as ChildRun

def pr.snoc(evs: List<&2, Ch.Ev>, +cfg: Ch.Cfg, +s: Ch.St, +e: Ch.Ev) -> {Ch.run(List.append(&2, Ch.Ev, evs, [e]), cfg, s) == Ch.step(cfg, Ch.run(evs, cfg, s), e) : Ch.St}:
  match evs:
    case Nil{}:
      {==}
    case h <> t:
      pr.snoc(t, cfg, Ch.step(cfg, s, h), e)

def ChildRun.child_run_folds(cfg, s, evs, e):
  ({==}, pr.snoc(evs, cfg, s, e))
