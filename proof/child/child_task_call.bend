# eukhe: the proof of LAW child_task_call

import Base
import ../../bend/child.bend as Ch
import ../../LAWS.bend as Laws

# The task's decisions: the call on a poll is the watch's verdict as the
# mode acts on it, for any verdict.

def pc.acted(x: Ch.Next, m: Ch.Mode) -> {Ch.call.of(x, m) == Laws.ChildActed(x, m) : Ch.Call}:
  match x:
    case Ch.Watch{w}:
      {==}
    case Ch.Owe{k}:
      match m:
        case Ch.Inbox{}:
          {==}
        case Ch.Silent{}:
          {==}
    case Ch.Quiet{}:
      {==}

def Laws.child_task_call(cfg, w, e, o, m):
  pc.acted(Ch.look(cfg, w, e, o), m)
