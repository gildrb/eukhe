# eukhe: the proof of LAW child_watch_takes_the_call
# The step's next phase on the watch's verdict is the phase of the call
# in inbox mode, verdict by verdict (pw.called).

import Base
import ../../bend/child.bend as Ch
import ../../laws/child/run.bend as ChildRun

def pw.called(x: Ch.Next) -> {Ch.watched(x) == ChildRun.chr_called(Ch.call.of(x, Ch.Inbox{})) : Ch.Ph}:
  match x:
    case Ch.Watch{w}:
      {==}
    case Ch.Owe{k}:
      {==}
    case Ch.Quiet{}:
      {==}

def ChildRun.child_watch_takes_the_call(cfg, w, open, inbox, dt, o):
  %pw.called(Ch.look(cfg, w, 1n+dt, o)) : {Ch.St{Ch.watched(Ch.look(cfg, w, 1n+dt, o)), None{}, open, inbox} == Ch.St{_, None{}, open, inbox} : Ch.St}
  {==}
