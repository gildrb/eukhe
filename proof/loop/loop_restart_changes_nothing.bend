# eukhe: the proof of LAW loop_restart_changes_nothing
#
# PROOF: the state is opened and its phase split: Lp.restart rebuilds the
# same state in each phase.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_restart_changes_nothing(s):
  match s:
    case Lp.St{p, i, l, d, c, b, f, x}:
      match p:
        case Lp.Off{}:
          {==}
        case Lp.Armed{}:
          {==}
        case Lp.Turn{}:
          {==}
        case Lp.Judging{}:
          {==}
        case Lp.Paused{}:
          {==}
        case Lp.Ended{w}:
          {==}
