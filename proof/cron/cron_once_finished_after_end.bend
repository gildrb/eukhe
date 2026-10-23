# eukhe: the proof of LAW cron_once_finished_after_end

import Base
import ../../bend/cron.bend as Cr
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pc.g_ends(+c: Nat, +dead: List<&2, Nat>, j: Cr.Job, g: LA.pc.G(c, dead, j)) -> Cr.Ends(j):
  match j:
    case Cr.Job{i, +s, +st, +nx, k, cl, +rs, +ss, h}:
      (h1, g2) = g
      (h2, g3) = g2
      (h3, g4) = g3
      (h4, g5) = g4
      (h5, g6) = g5
      (h6, h7) = g6
      h7

def pc.all_ends(+c: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>, g: LA.pc.AllG(c, dead, rs)) -> Cr.EndsAll(rs):
  match rs:
    case Nil{}:
      Unit{}
    case r <> t:
      match r:
        case Cr.Known{+j}:
          (a, b) = g
          (pc.g_ends(c, dead, j, a), pc.all_ends(c, dead, t, b))
        case Cr.Raw{x}:
          pc.all_ends(c, dead, t, g)

def pc.ends_of(s: Cr.S, inv: LA.pc.Inv(s)) -> Cr.EndsAll(Cr.S.recs(s)):
  match s:
    case Cr.S{b, rs, rd, +dead, +c, n, a}:
      pc.all_ends(c, dead, rs, inv)

def pc.cron_once_finished_after_end(+evs: List<&2, Cr.Ev>) -> Cr.EndsAll(Cr.S.recs(Cr.run(evs))):
  pc.ends_of(Cr.run(evs), LA.pc.inv_run(evs))

def Laws.cron_once_finished_after_end(evs):
  pc.cron_once_finished_after_end(evs)
