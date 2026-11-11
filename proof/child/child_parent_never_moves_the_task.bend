# eukhe: the proof of LAW child_parent_never_moves_the_task
# Event by event: each event of the parent keeps the phase and the mark;
# a poll and a cancel or delete are no events of the parent, against the
# premise.

import Base
import ../../bend/child.bend as Ch
import ../../laws/child/run.bend as ChildRun
import ../base/logic/logic.bend as LLogicLogic

def pp.go(s: Ch.St, e: Ch.Ev, +cfg: Ch.Cfg, par: {ChildRun.chr_parents(e) == True{} : Bool}) -> {Ch.St.ph(Ch.step(cfg, s, e)) == Ch.St.ph(s) : Ch.Ph} & {ChildRun.chr_cut(Ch.step(cfg, s, e)) == ChildRun.chr_cut(s) : Maybe<&2, Bool>}:
  match s:
    case Ch.St{+ph, +cut, +open, +inbox}:
      match e:
        case Ch.Poll{+dt, +o}:
          LLogicLogic.child.pc.absurd({Ch.St.ph(Ch.step(cfg, Ch.St{ph, cut, open, inbox}, Ch.Poll{dt, o})) == ph : Ch.Ph} & {ChildRun.chr_cut(Ch.step(cfg, Ch.St{ph, cut, open, inbox}, Ch.Poll{dt, o})) == cut : Maybe<&2, Bool>}, par)
        case Ch.Deliver{m}:
          ({==}, {==})
        case Ch.Withdraw{m}:
          ({==}, {==})
        case Ch.Abort{}:
          ({==}, {==})
        case Ch.Shut{}:
          ({==}, {==})
        case Ch.Reopen{}:
          ({==}, {==})
        case Ch.Cut{+del}:
          LLogicLogic.child.pc.absurd({Ch.St.ph(Ch.step(cfg, Ch.St{ph, cut, open, inbox}, Ch.Cut{del})) == ph : Ch.Ph} & {ChildRun.chr_cut(Ch.step(cfg, Ch.St{ph, cut, open, inbox}, Ch.Cut{del})) == cut : Maybe<&2, Bool>}, par)
        case Ch.Collect{}:
          ({==}, {==})

def ChildRun.child_parent_never_moves_the_task(cfg, s, e, parents):
  pp.go(s, e, cfg, parents)
