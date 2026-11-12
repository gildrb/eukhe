# eukhe: the proof of LAW child_ended_stays_ended
# Event by event: no event moves the phase off Ended (a marked step runs
# the abort, which keeps an ended task ended), and the step keeps the
# inbox.

import Base
import ../../bend/child.bend as Ch
import ../../laws/child/run.bend as ChildRun

def pe.ph(e: Ch.Ev, +cfg: Ch.Cfg, cut: Maybe<&2, Bool>, +open: Bool, +inbox: List<&2, Ch.Sub>) -> {Ch.St.ph(Ch.step(cfg, Ch.St{Ch.Ended{}, cut, open, inbox}, e)) == Ch.Ended{} : Ch.Ph}:
  match e:
    case Ch.Poll{dt, o}:
      match cut:
        case None{}:
          {==}
        case Some{d}:
          {==}
    case Ch.Deliver{m}:
      {==}
    case Ch.Withdraw{m}:
      {==}
    case Ch.Abort{}:
      {==}
    case Ch.Shut{}:
      {==}
    case Ch.Reopen{}:
      {==}
    case Ch.Cut{del}:
      {==}
    case Ch.Collect{}:
      {==}

def pe.inbox(cut: Maybe<&2, Bool>, +cfg: Ch.Cfg, +open: Bool, +inbox: List<&2, Ch.Sub>, +dt: Nat, +o: Ch.Obs) -> {Ch.St.inbox(Ch.step(cfg, Ch.St{Ch.Ended{}, cut, open, inbox}, Ch.Poll{dt, o})) == inbox : List<&2, Ch.Sub>}:
  match cut:
    case None{}:
      {==}
    case Some{d}:
      {==}

def ChildRun.child_ended_stays_ended(cfg, cut, open, inbox, e, dt, o):
  (pe.ph(e, cfg, cut, open, inbox), pe.inbox(cut, cfg, open, inbox, dt, o))
