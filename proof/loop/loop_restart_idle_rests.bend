# eukhe: the proof of LAW loop_restart_idle_rests
#
# PROOF: the state is opened and its phase split: off, armed, paused and
# ended restart to Rest by computation; in a turn or judging the premise is
# True == False.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_restart_idle_rests(s, h):
  match s:
    case Lp.St{p, i, l, d, c, b, f, x}:
      match p:
        case Lp.Off{}:
          {==}
        case Lp.Armed{}:
          {==}
        case Lp.Turn{}:
          LALoopBounds.lb.absurd_tf({S.does(Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}, Lp.Restart{}) == Lp.Rest{} : Lp.Act}, h)
        case Lp.Judging{}:
          LALoopBounds.lb.absurd_tf({S.does(Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, Lp.Restart{}) == Lp.Rest{} : Lp.Act}, h)
        case Lp.Paused{}:
          {==}
        case Lp.Ended{w}:
          {==}
