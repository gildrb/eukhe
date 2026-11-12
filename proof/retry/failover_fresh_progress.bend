# eukhe: the proof of LAW failover_fresh_progress
# Within the budget the walk takes the fresh pick or the return pick; with
# a provider x of the chain not tried, not every provider was tried
# (LW.fw.all_has), so it takes the fresh pick over the chain order after
# the provider that just failed (LRetry.rp.fresh_order). That order holds
# x (x is not the provider that just failed, which was tried:
# LW.fw.last_seen, LW.fw.order_mem), so the pick is a switch
# (LW.fw.fresh_some), to a provider not tried, at once
# (LRetry.rp.fresh_inv).

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/bool.bend as LBool
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ../base/retry.bend as LRetry
import ./base/walk.bend as LW

# a fresh pick that is a switch is a switch to a provider not tried, at once
def fp.fs(m: Maybe<&2, R.Switch>, +last: Nat, +ts: List<&2, R.Tried>, +hf: {LLogicBool.rp.fresh_ok(m, last, ts) == True{} : Bool}, hs: {Retry.rs.is_switch(m) == True{} : Bool}) -> {Retry.rs.fresh_switch(m, ts) == True{} : Bool}:
  match m:
    case None{}:
      LLogicLogic.rp.absurdF({Retry.rs.fresh_switch(None{}, ts) == True{} : Bool}, hs)
    case Some{s}:
      match s:
        case R.Switch{+to, +d}:
          +d0 = LLogicBool.rp.and_l(Nat.is_eq(d, 0n), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts))), hf)
          +f2 = LLogicBool.rp.and_r(Nat.is_eq(d, 0n), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts))), hf)
          +ns = LLogicBool.rp.and_r(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts)), f2)
          %LW.fw.tried(to, ts) : {Bool.and(Bool.not(_), Nat.is_eq(d, 0n)) == True{} : Bool}
          LBool.rp.and_tt(Bool.not(R.seen(to, ts)), Nat.is_eq(d, 0n), ns, d0)

# not every provider of the chain was tried
def fp.not_all(c: Bool, +len: Nat, +x: Nat, +ts: List<&2, R.Tried>, ec: {R.all_seen(len, ts) == c : Bool}, chain: {Nat.is_lt(x, len) == True{} : Bool}, fx: {R.seen(x, ts) == False{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      LLogicLogic.rp.absurdT({True{} == False{} : Bool}, Equal.trans(Bool, True{}, R.seen(x, ts), False{}, Equal.sym(Bool, R.seen(x, ts), True{}, LW.fw.all_has(len, x, ts, ec, chain)), fx))
    case False{}:
      {==}

def fresh_progress(+len: Nat, +t: R.Tried, +rest: List<&2, R.Tried>, +sw: Nat, +b: Nat, +m: Nat, +x: Nat, budget: {Nat.is_lt(Retry.rs.count(rest), sw) == True{} : Bool}, +chain: {Nat.is_lt(x, len) == True{} : Bool}, fresh: {Retry.rs.tried(x, t <> rest) == False{} : Bool}) -> {Retry.rs.fresh_switch(R.next(len, t <> rest, R.Policy{sw, b, m}), t <> rest) == True{} : Bool}:
  +L = {t <> rest : List<&2, R.Tried>}
  +P = {R.Policy{sw, b, m} : R.Policy}
  +last = R.Tried.at(R.last.go(rest, t))
  +ord = R.order(last, len)
  +hb = Equal.trans(Bool, Nat.is_le(1n+R.length(rest), sw), Nat.is_lt(R.length(rest), sw), True{}, LW.fw.le_succ(R.length(rest), sw), Equal.trans(Bool, Nat.is_lt(R.length(rest), sw), Nat.is_lt(Retry.rs.count(rest), sw), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(z, sw), R.length(rest), Retry.rs.count(rest), LW.fw.count(rest)), budget))
  +fx = Equal.trans(Bool, R.seen(x, L), Retry.rs.tried(x, L), False{}, LW.fw.tried(x, L), fresh)
  +na = fp.not_all(R.all_seen(len, L), len, x, L, {==}, chain, fx)
  +ne = LNat.pt.ne_comm(last, x, LW.fw.seen_ne(last, x, L, LW.fw.last_seen(rest, t), fx))
  %Equal.sym(Bool, Nat.is_le(1n+R.length(rest), sw), True{}, hb) : {Retry.rs.fresh_switch(R.next.budget(_, last, len, L, P), L) == True{} : Bool}
  %Equal.sym(Bool, R.all_seen(len, L), False{}, na) : {Retry.rs.fresh_switch(R.next.mode(_, last, len, L, P), L) == True{} : Bool}
  %LRetry.rp.fresh_order(last, len, L) : {Retry.rs.fresh_switch(_, L) == True{} : Bool}
  fp.fs(R.pick.fresh(ord, L), last, L, LRetry.rp.fresh_inv(ord, last, L, LRetry.rp.order_notin(last, len)), LW.fw.fresh_some(ord, LW.fw.hd(ord, x), LW.fw.hs(ord, L), L, x, {==}, {==}, LW.fw.order_mem(last, len, x, chain, ne), fx))

def Retry.failover_fresh_progress(len, t, rest, switches, base, max, x, budget, chain, fresh):
  fresh_progress(len, t, rest, switches, base, max, x, budget, chain, fresh)
