# eukhe: the proof of LAW loop_restart_resumes_adopted
#
# PROOF: the state is opened and its phase split: on, the prompt is adopted
# as turn 1 + i with text t and the restart of that state computes to the
# Resume; off or ended, the premise is False == True.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_restart_resumes_adopted(s, t, on):
  match s:
    case Lp.St{p, i, l, d, c, b, f, x}:
      match p:
        case Lp.Off{}:
          LALoopBounds.lb.absurd_ft({S.does(S.next(Lp.St{Lp.Off{}, i, l, d, c, b, f, x}, Lp.Prompt{t}), Lp.Restart{}) == Lp.Resume{1n+i, t} : Lp.Act}, on)
        case Lp.Armed{}:
          {==}
        case Lp.Turn{}:
          {==}
        case Lp.Judging{}:
          {==}
        case Lp.Paused{}:
          {==}
        case Lp.Ended{w}:
          LALoopBounds.lb.absurd_ft({S.does(S.next(Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}, Lp.Prompt{t}), Lp.Restart{}) == Lp.Resume{1n+i, t} : Lp.Act}, on)
