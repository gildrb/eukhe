# eukhe: the proof of LAW failover_return_progress
# Within the budget, once every provider of the chain was tried
# (LW.fw.all_seen), the walk takes the return pick over the chain order
# after the provider that just failed; that order holds x (LW.fw.order_mem)
# and a return to x may go out by the model's test exactly when R3's
# (LW.fw.return_wait), so the pick is a switch (LW.fw.back_some).

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ./base/walk.bend as LW

def return_progress(+len: Nat, +t: R.Tried, +rest: List<&2, R.Tried>, +sw: Nat, +b: Nat, +m: Nat, +x: Nat, budget: {Nat.is_lt(Retry.rs.count(rest), sw) == True{} : Bool}, all: {Retry.rs.all_tried(Retry.rs.ints(len, 0n), t <> rest) == True{} : Bool}, chain: {Nat.is_lt(x, len) == True{} : Bool}, other: {Nat.is_eq(x, Retry.rs.newest(rest, t)) == False{} : Bool}, may: {Retry.rs.may_return(x, len, t <> rest, b, m) == True{} : Bool}) -> {Retry.rs.is_switch(R.next(len, t <> rest, R.Policy{sw, b, m})) == True{} : Bool}:
  +L = {t <> rest : List<&2, R.Tried>}
  +P = {R.Policy{sw, b, m} : R.Policy}
  +last = R.Tried.at(R.last.go(rest, t))
  +ord = R.order(last, len)
  +B = R.backoff(P, len, L)
  +hb = Equal.trans(Bool, Nat.is_le(1n+R.length(rest), sw), Nat.is_lt(R.length(rest), sw), True{}, LW.fw.le_succ(R.length(rest), sw), Equal.trans(Bool, Nat.is_lt(R.length(rest), sw), Nat.is_lt(Retry.rs.count(rest), sw), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(z, sw), R.length(rest), Retry.rs.count(rest), LW.fw.count(rest)), budget))
  +ea = Equal.trans(Bool, R.all_seen(len, L), Retry.rs.all_tried(Retry.rs.ints(len, 0n), L), True{}, LW.fw.all_seen(len, L), all)
  +ot = Equal.trans(Bool, Nat.is_eq(x, last), Nat.is_eq(x, Retry.rs.newest(rest, t)), False{}, Equal.cong(Nat, Bool, z => Nat.is_eq(x, z), last, Retry.rs.newest(rest, t), LW.fw.newest(rest, t)), other)
  +ok = Equal.trans(Bool, LW.fw.ok(x, L, B, m), Retry.rs.may_return(x, len, L, b, m), True{}, Equal.cong(Nat, Bool, z => Bool.and(Nat.is_gt(z, 0n), Nat.is_le(z, m)), Nat.max(B, R.server(x, L)), Retry.rs.return_wait(x, len, L, b, m), LW.fw.return_wait(x, sw, b, m, len, L)), may)
  %Equal.sym(Bool, Nat.is_le(1n+R.length(rest), sw), True{}, hb) : {Retry.rs.is_switch(R.next.budget(_, last, len, L, P)) == True{} : Bool}
  %Equal.sym(Bool, R.all_seen(len, L), True{}, ea) : {Retry.rs.is_switch(R.next.mode(_, last, len, L, P)) == True{} : Bool}
  LW.fw.back_some(ord, LW.fw.hd(ord, x), LW.fw.hb(ord, L, B, m), L, B, m, x, {==}, {==}, LW.fw.order_mem(last, len, x, chain, ot), ok)

def Retry.failover_return_progress(len, t, rest, switches, base, max, x, budget, all, chain, other, may):
  return_progress(len, t, rest, switches, base, max, x, budget, all, chain, other, may)
