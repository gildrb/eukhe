# eukhe: lemmas the proofs of area cron share: list

import Base
import ../../../bend/cron.bend as Cr
import ./nat.bend as LANat

# The invariant of a job
# ----------------------

# the processes that run the job are alive
def pc.Live(rs: List<&2, Nat>, +dead: List<&2, Nat>) -> Type:
  match rs:
    case Nil{}:
      Unit
    case +o <> t:
      ({Cr.has(o, dead) == False{} : Bool} & pc.Live(t, dead))

# the newest occurrence that started is at or before the clock and
# before the next run
def pc.Top(ss: List<&2, Nat>, +c: Nat, +nx: Maybe<&2, Nat>) -> Type:
  match ss:
    case Nil{}:
      Unit
    case +x <> t:
      ({Nat.is_le(x, c) == True{} : Bool} & LANat.pc.Below(x, nx))

# Shapes the invariant keeps
# --------------------------

def pc.top_none(+ss: List<&2, Nat>, +c: Nat, -nx: Maybe<&2, Nat>, t: pc.Top(ss, c, nx)) -> pc.Top(ss, c, None{}):
  match ss:
    case Nil{}:
      Unit{}
    case +x <> +u:
      (a, b) = t
      (a, Unit{})

def pc.dead_after(e: Cr.Ev, +dead: List<&2, Nat>) -> List<&2, Nat>:
  match e:
    case Cr.Die{p}:
      p <> dead
    case Cr.Take{p}:
      dead
    case Cr.Create{p, s}:
      dead
    case Cr.Recover{p}:
      dead
    case Cr.Finish{p, i, o}:
      dead
    case Cr.Abort{p}:
      dead
    case Cr.Cancel{p, i}:
      dead
    case Cr.Resume{p, i}:
      dead
    case Cr.Tick{d}:
      dead
    case Cr.RawJob{t}:
      dead
    case Cr.RawClaim{t}:
      dead
    case Cr.Corrupt{t}:
      dead

def pc.top_tick(+ss: List<&2, Nat>, +c: Nat, +d: Nat, -nx: Maybe<&2, Nat>, t: pc.Top(ss, c, nx)) -> pc.Top(ss, Nat.add(c, d), nx):
  match ss:
    case Nil{}:
      Unit{}
    case +x <> +u:
      (a, b) = t
      (LANat.cron.pc.le_add(x, c, d, a), b)
