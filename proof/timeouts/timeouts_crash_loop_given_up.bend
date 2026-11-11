# eukhe: the proof of LAW timeouts_crash_loop_given_up
#
# PROOF: k gaps of at most m = longest pause + loop period span at most
# k * m (tcl.sum_le), which is below the derived window (k + 1) * m = m +
# k * m when m is not 0 (tcl.lt_shift); so the run is inside the window and
# restart_gives_up gives the worker up.

import Base
import ../../bend/supervise.bend as Su
import ../../laws/supervise.bend as Supervise
import ../../laws/timeouts.bend as Timeouts
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ../supervise/restart_gives_up.bend as PRestartGivesUp
import ../supervise/restart_span_exact.bend as PRestartSpanExact

# a <= b: a + d <= b + d
def tcl.le_right(a: Nat, b: Nat, +d: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, d), Nat.add(b, d)) == True{} : Bool}:
  match a b:
    case 0n q:
      LNat.supervisor.ps.le_add_l(q, d)
    case 1n+p 0n:
      LLogicLogic.supervisor.ps.absurdF({Nat.is_le(Nat.add(1n+p, d), d) == True{} : Bool}, h)
    case 1n+p 1n+q:
      tcl.le_right(p, q, d, h)

# a <= b, c <= d: a + c <= b + d
def tcl.add_le(+a: Nat, +b: Nat, +c: Nat, +d: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, cd: {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  LNat.supervisor.ps.le_trans(Nat.add(a, c), Nat.add(a, d), Nat.add(b, d), LNat.ps.le_mono(a, c, d, cd), tcl.le_right(a, b, d, ab))

# gaps each at most m sum to at most |gs| * m
def tcl.sum_le(gs: List<&2, Nat>, +m: Nat, h: {Timeouts.tw_all_le(gs, m) == True{} : Bool}) -> {Nat.is_le(Supervise.restart_sum(gs), Nat.mul(List.length(&2, Nat, gs), m)) == True{} : Bool}:
  match gs:
    case Nil{}:
      {==}
    case +g <> +t:
      +hh = h
      +hg = LLogicBool.wr_and_l(Nat.is_le(g, m), Timeouts.tw_all_le(t, m), hh)
      +ht = LLogicBool.wr_and_r(Nat.is_le(g, m), Timeouts.tw_all_le(t, m), hh)
      tcl.add_le(g, m, Supervise.restart_sum(t), Nat.mul(List.length(&2, Nat, t), m), hg, tcl.sum_le(t, m, ht))

def tcl.le_k(+gs: List<&2, Nat>, +m: Nat, +k: Nat, many: {List.length(&2, Nat, gs) == k : Nat}, h: {Nat.is_le(Supervise.restart_sum(gs), Nat.mul(List.length(&2, Nat, gs), m)) == True{} : Bool}) -> {Nat.is_le(Supervise.restart_sum(gs), Nat.mul(k, m)) == True{} : Bool}:
  %many : {Nat.is_le(Supervise.restart_sum(gs), Nat.mul(_, m)) == True{} : Bool}
  h

# x <= z and 0 < m: x < m + z
def tcl.lt_shift(+x: Nat, +z: Nat, m: Nat, le: {Nat.is_le(x, z) == True{} : Bool}, pos: {Nat.is_lt(0n, m) == True{} : Bool}) -> {Nat.is_lt(x, Nat.add(m, z)) == True{} : Bool}:
  match m:
    case 0n:
      LLogicLogic.supervisor.ps.absurdF({Nat.is_lt(x, z) == True{} : Bool}, pos)
    case 1n++p:
      PRestartGivesUp.ps.lt_of_le_succ(x, 1n+Nat.add(p, z), LNat.supervisor.ps.le_trans(x, z, Nat.add(p, z), le, LNat.supervisor.ps.le_add_l(p, z)))

# a run whose gaps sum below w spans below w
def tcl.fast(+gs: List<&2, Nat>, +w: Nat, h: {Nat.is_lt(Supervise.restart_sum(gs), w) == True{} : Bool}) -> {Nat.is_lt(Su.span(gs), w) == True{} : Bool}:
  %Equal.sym(Nat, Su.span(gs), Supervise.restart_sum(gs), Supervise.restart_span_exact(gs)) : {Nat.is_lt(_, w) == True{} : Bool}
  h

def Timeouts.timeouts_crash_loop_given_up(k, bmax, loop, b, pre, g, gs, live, many, loops):
  +m = Nat.add(bmax, loop)
  +mm = many
  +sm = Supervise.restart_sum(gs)
  +lek = tcl.le_k(gs, m, k, mm, tcl.sum_le(gs, m, loops))
  +lt = tcl.lt_shift(sm, Nat.mul(k, m), m, lek, live)
  Supervise.restart_gives_up(Timeouts.tw_restart_cfg(k, bmax, loop, b), pre, g, gs, mm, tcl.fast(gs, Nat.mul(1n+k, m), lt))
