# eukhe: the proof of LAW cron_fires_once

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron.bend as Cron
import ./base/cron.bend as LACron
import ./base/logic.bend as LALogic

# What the invariant gives
# ------------------------

def pc.once_once(s: Cr.Sched, ss: List<&2, Nat>, +nx: Maybe<&2, Nat>, o: LALogic.pc.OnceG(s, ss, nx)) -> Cr.OnceOnce(s, ss):
  match s:
    case Cr.Once{d}:
      match ss:
        case Nil{}:
          Unit{}
        case x <> t:
          (a, b) = o
          a
    case Cr.Every{q}:
      Unit{}

def pc.g_fires(+c: Nat, +dead: List<&2, Nat>, j: Cr.Job, g: LALogic.pc.G(c, dead, j)) -> Cr.Fires(j):
  match j:
    case Cr.Job{i, +s, +st, +nx, k, +cl, +rs, +ss, h}:
      (h1, g2) = g
      (h2, g3) = g2
      (h3, g4) = g3
      (h4, g5) = g4
      (h5, g6) = g5
      (h1, (h3, pc.once_once(s, ss, nx, h5)))

def pc.all_fires(+c: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>, g: LALogic.pc.AllG(c, dead, rs)) -> Cr.FiresAll(rs):
  match rs:
    case Nil{}:
      Unit{}
    case r <> t:
      match r:
        case Cr.Known{+j}:
          (a, b) = g
          (pc.g_fires(c, dead, j, a), pc.all_fires(c, dead, t, b))
        case Cr.Raw{x}:
          pc.all_fires(c, dead, t, g)

def pc.fires_of(s: Cr.S, inv: LALogic.pc.Inv(s)) -> Cr.FiresAll(Cr.S.recs(s)):
  match s:
    case Cr.S{b, rs, rd, +dead, +c, n, a}:
      pc.all_fires(c, dead, rs, inv)

# The laws
# --------

def pc.cron_fires_once(+evs: List<&2, Cr.Ev>) -> Cr.FiresAll(Cr.S.recs(Cr.run(evs))):
  pc.fires_of(Cr.run(evs), LACron.pc.inv_run(evs))

# Cron

def Cron.cron_fires_once(evs):
  pc.cron_fires_once(evs)
