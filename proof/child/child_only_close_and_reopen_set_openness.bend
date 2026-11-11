# eukhe: the proof of LAW child_only_close_and_reopen_set_openness
# Each event computes on a state.

import Base
import ../../bend/child.bend as Ch
import ../../laws/child/run.bend as ChildRun

def ChildRun.child_only_close_and_reopen_set_openness(cfg, s, m, del):
  match s:
    case Ch.St{ph, cut, open, inbox}:
      ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))))
