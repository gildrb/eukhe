# eukhe: the proof of LAW failover_fresh_nearest
# With a provider x of the chain not tried, the switch is the fresh pick
# (a return needs every provider tried: LW.fw.all_has), over the chain
# order after the provider that just failed; that order ranks each of its
# providers at its rs.rank (LW.fw.order_ranked) and holds x (x is not the
# provider that just failed, which was tried: LW.fw.last_seen,
# LW.fw.order_mem); the fresh pick is no later than any provider of it not
# tried (LW.fw.fresh_nearest).

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base/walk.bend as LW

def fn.mode(all: Bool, +len: Nat, +ts: List<&2, R.Tried>, +last: Nat, +p: R.Policy, -to: Nat, -w: Nat, +x: Nat, M: LW.fw.Mode(all, len, ts, last, p, to, w), chain: {Nat.is_lt(x, len) == True{} : Bool}, +fx: {R.seen(x, ts) == False{} : Bool}, ls: {R.seen(last, ts) == True{} : Bool}) -> {Nat.is_le(Retry.rs.rank(last, to, len), Retry.rs.rank(last, x, len)) == True{} : Bool}:
  match all:
    case True{}:
      (ea, pb) = M
      LLogicLogic.rp.absurdT({Nat.is_le(Retry.rs.rank(last, to, len), Retry.rs.rank(last, x, len)) == True{} : Bool}, Equal.trans(Bool, True{}, R.seen(x, ts), False{}, Equal.sym(Bool, R.seen(x, ts), True{}, LW.fw.all_has(len, x, ts, ea, chain)), fx))
    case False{}:
      (ea, pf) = M
      +ord = R.order(last, len)
      +ne = LNat.pt.ne_comm(last, x, LW.fw.seen_ne(last, x, ts, ls, fx))
      LW.fw.fresh_nearest(ord, LW.fw.hd(ord, x), LW.fw.hs(ord, ts), 0n, last, len, ts, to, w, x, {==}, {==}, LW.fw.order_ranked(last, len), pf, LW.fw.order_mem(last, len, x, chain, ne), fx)

def fn.split(+len: Nat, +ts: List<&2, R.Tried>, +last: Nat, +p: R.Policy, -to: Nat, -w: Nat, +x: Nat, sp: LW.fw.Split(len, ts, last, p, to, w), chain: {Nat.is_lt(x, len) == True{} : Bool}, fx: {R.seen(x, ts) == False{} : Bool}, ls: {R.seen(last, ts) == True{} : Bool}) -> {Nat.is_le(Retry.rs.rank(last, to, len), Retry.rs.rank(last, x, len)) == True{} : Bool}:
  (B, S) = sp
  (all, M) = S
  fn.mode(all, len, ts, last, p, to, w, x, M, chain, fx, ls)

def fresh_nearest(+len: Nat, +t: R.Tried, +rest: List<&2, R.Tried>, +p: R.Policy, +to: Nat, +w: Nat, +x: Nat, got: {R.next(len, t <> rest, p) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}, chain: {Nat.is_lt(x, len) == True{} : Bool}, fresh: {Retry.rs.tried(x, t <> rest) == False{} : Bool}) -> {Nat.is_le(Retry.rs.rank(Retry.rs.newest(rest, t), to, len), Retry.rs.rank(Retry.rs.newest(rest, t), x, len)) == True{} : Bool}:
  %LW.fw.newest(rest, t) : {Nat.is_le(Retry.rs.rank(_, to, len), Retry.rs.rank(_, x, len)) == True{} : Bool}
  +fx = Equal.trans(Bool, R.seen(x, t <> rest), Retry.rs.tried(x, t <> rest), False{}, LW.fw.tried(x, t <> rest), fresh)
  fn.split(len, t <> rest, R.Tried.at(R.last.go(rest, t)), p, to, w, x, LW.fw.split(len, t, rest, p, to, w, got), chain, fx, LW.fw.last_seen(rest, t))

def Retry.failover_fresh_nearest(len, t, rest, p, to, w, x, got, chain, fresh):
  fresh_nearest(len, t, rest, p, to, w, x, got, chain, fresh)
