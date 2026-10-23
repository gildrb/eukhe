# eukhe: the proof of LAW child_silent_never_reports

import Base
import ../../bend/child.bend as Ch
import ../../laws/child.bend as Child

def pc.silent(x: Ch.Next) -> {Ch.Call.reports(Ch.call.of(x, Ch.Silent{})) == False{} : Bool}:
  match x:
    case Ch.Watch{w}:
      {==}
    case Ch.Owe{k}:
      {==}
    case Ch.Quiet{}:
      {==}

def Child.child_silent_never_reports(cfg, w, e, o):
  pc.silent(Ch.look(cfg, w, e, o))
