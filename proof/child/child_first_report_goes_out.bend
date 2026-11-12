# eukhe: the proof of LAW child_first_report_goes_out
# By the first poll's verdict (pfr.go): one that owes a report computes
# (the task owes it under 1, submits it, the parent places it); one that
# watches on or ends quietly is no report, against the premise.

import Base
import ../../bend/child.bend as Ch
import ../../laws/child/run.bend as ChildRun
import ../base/logic/logic.bend as LLogicLogic

def pfr.go(x: Ch.Next, +cfg: Ch.Cfg, +d2: Nat, +o2: Ch.Obs, rep: {Ch.Call.reports(Ch.call.of(x, Ch.Inbox{})) == True{} : Bool}) -> {Ch.St.reached(Ch.run([Ch.Poll{d2, o2}, Ch.Deliver{1n}], cfg, Ch.St{Ch.watched(x), None{}, True{}, Nil{}})) == 1n : Nat}:
  match x:
    case Ch.Watch{w}:
      LLogicLogic.child.pc.absurd({Ch.St.reached(Ch.run([Ch.Poll{d2, o2}, Ch.Deliver{1n}], cfg, Ch.St{Ch.watched(Ch.Watch{w}), None{}, True{}, Nil{}})) == 1n : Nat}, rep)
    case Ch.Owe{k}:
      {==}
    case Ch.Quiet{}:
      LLogicLogic.child.pc.absurd({Ch.St.reached(Ch.run([Ch.Poll{d2, o2}, Ch.Deliver{1n}], cfg, Ch.St{Ch.watched(Ch.Quiet{}), None{}, True{}, Nil{}})) == 1n : Nat}, rep)

def ChildRun.child_first_report_goes_out(cfg, d1, o1, d2, o2, reports):
  pfr.go(Ch.look(cfg, Ch.W.fresh(cfg, None{}), 1n+d1, o1), cfg, d2, o2, reports)
