# eukhe: the proof of LAW timeouts_ordered

import Base
import ../../bend/supervise.bend as Su
import ../../laws/supervise.bend as Supervise
import ../base/bool/and.bend as LBoolAnd
import ../base/nat/is_le.bend as LNatIsLe

# a is at most a + b
def ps.le_add(a: Nat, +b: Nat) -> {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      LNatIsLe.ps.le_zero(b)
    case 1n+p:
      ps.le_add(p, b)

# (D1) timeouts_ordered
# ---------------------

def ps.seen_lost(t: Su.Tm) -> {Nat.is_le(Su.Tm.seen(t), Su.Tm.lost(t)) == True{} : Bool}:
  match t:
    case Su.Tm{snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, +relaunch, +startup, +check, +slack, k, bmax, loop, qanswer}:
      ps.le_add(Nat.add(Nat.add(relaunch, startup), check), slack)

def ps.refresh_age(t: Su.Tm) -> {Nat.is_le(Su.Tm.refresh(t), Su.Tm.max_age(t)) == True{} : Bool}:
  match t:
    case Su.Tm{snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, +refresh, +boot, relaunch, startup, check, slack, k, bmax, loop, qanswer}:
      ps.le_add(refresh, boot)

def ps.timeouts_ordered(+t: Su.Tm) -> {Su.Tm.ordered(t) == True{} : Bool}:
  +window = Nat.is_le(Nat.mul(Su.Tm.k(t), Su.Tm.loop_step(t)), Su.Tm.window(t))
  +hold = Bool.and(Nat.is_le(Su.Tm.qanswer(t), Su.Tm.quiesce_hold(t)), window)
  +age = Bool.and(Nat.is_le(Su.Tm.refresh(t), Su.Tm.max_age(t)), hold)
  +lost = Bool.and(Nat.is_le(Su.Tm.seen(t), Su.Tm.lost(t)), age)
  +child = Bool.and(Nat.is_le(Nat.add(Su.Tm.stop_grace(t), Su.Tm.drain(t)), Su.Tm.child_kill(t)), lost)
  +drain = Bool.and(Nat.is_le(Su.Tm.drain(t), Su.Tm.launcher_wait(t)), child)
  LBoolAnd.supervisor.ps.and_t(Nat.is_le(Su.Tm.teardown(t), Su.Tm.stop_grace(t)), drain, ps.le_add(Su.Tm.teardown(t), Su.Tm.harness(t)),
    LBoolAnd.supervisor.ps.and_t(Nat.is_le(Su.Tm.drain(t), Su.Tm.launcher_wait(t)), child, ps.le_add(Su.Tm.drain(t), Su.Tm.margin(t)),
      LBoolAnd.supervisor.ps.and_t(Nat.is_le(Nat.add(Su.Tm.stop_grace(t), Su.Tm.drain(t)), Su.Tm.child_kill(t)), lost, ps.le_add(Nat.add(Su.Tm.stop_grace(t), Su.Tm.drain(t)), Su.Tm.margin(t)),
        LBoolAnd.supervisor.ps.and_t(Nat.is_le(Su.Tm.seen(t), Su.Tm.lost(t)), age, ps.seen_lost(t),
          LBoolAnd.supervisor.ps.and_t(Nat.is_le(Su.Tm.refresh(t), Su.Tm.max_age(t)), hold, ps.refresh_age(t),
            LBoolAnd.supervisor.ps.and_t(Nat.is_le(Su.Tm.qanswer(t), Su.Tm.quiesce_hold(t)), window, ps.le_add(Su.Tm.qanswer(t), Su.Tm.stop_grace(t)),
              LNatIsLe.supervisor.ps.le_add_l(Su.Tm.loop_step(t), Nat.mul(Su.Tm.k(t), Su.Tm.loop_step(t)))))))))

def Supervise.timeouts_ordered(t):
  ps.timeouts_ordered(t)
