# eukhe: the proof of LAW failover_bounded
# A switch is made only within the budget: the attempts (1 + the switches
# made) are at most retry.failover.maxRetries (LW.fw.split), and the
# model's count is the laws' (LW.fw.count).

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ./base/walk.bend as LW

def bd.split(+len: Nat, +t: R.Tried, +rest: List<&2, R.Tried>, +last: Nat, +sw: Nat, +b: Nat, +m: Nat, +to: Nat, +w: Nat, sp: LW.fw.Split(len, t <> rest, last, R.Policy{sw, b, m}, to, w)) -> {Nat.is_lt(R.length(rest), sw) == True{} : Bool}:
  (B, S) = sp
  Equal.trans(Bool, Nat.is_lt(R.length(rest), sw), Nat.is_le(1n+R.length(rest), sw), True{}, Equal.sym(Bool, Nat.is_le(1n+R.length(rest), sw), Nat.is_lt(R.length(rest), sw), LW.fw.le_succ(R.length(rest), sw)), B)

def bounded(+len: Nat, +t: R.Tried, +rest: List<&2, R.Tried>, +sw: Nat, +b: Nat, +m: Nat, +to: Nat, +w: Nat, got: {R.next(len, t <> rest, R.Policy{sw, b, m}) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}) -> {Nat.is_lt(Retry.rs.count(rest), sw) == True{} : Bool}:
  %LW.fw.count(rest) : {Nat.is_lt(_, sw) == True{} : Bool}
  bd.split(len, t, rest, R.Tried.at(R.last.go(rest, t)), sw, b, m, to, w, LW.fw.split(len, t, rest, R.Policy{sw, b, m}, to, w, got))

def Retry.failover_bounded(len, t, rest, switches, base, max, to, w, got):
  bounded(len, t, rest, switches, base, max, to, w, got)
