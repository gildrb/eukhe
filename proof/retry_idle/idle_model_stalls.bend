# eukhe: the proof of LAW idle_model_stalls
# By induction on pre: each gap of pre is at most d (not above it), so the
# model goes on, the time accumulating as the sum of pre (associativity);
# the late gap g then stalls it d after the last event of pre.
import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ../../laws/base.bend as LawsBase
import ./base.bend as LA
import ./idle_model_closes.bend as PMC

def ms.go(pre: List<&2, Nat>, +g: Nat, +rest: List<&2, Nat>, +d: Nat, +last: Nat, +within: {RetryIdle.gaps_within(pre, d) == True{} : Bool}, +late: {Nat.is_gt(g, d) == True{} : Bool}) -> {R.idle.go(List.append(&2, Nat, pre, g <> rest), d, last) == R.IdleStall{Nat.add(Nat.add(last, RetryIdle.gaps_sum(pre)), d)} : R.Idle}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_gt(g, d), True{}, late) : {R.idle.sel(_, R.IdleStall{Nat.add(last, d)}, R.idle.go(rest, d, Nat.add(last, g))) == R.IdleStall{Nat.add(Nat.add(last, 0n), d)} : R.Idle}
      %Equal.sym(Nat, Nat.add(last, 0n), last, LA.ri.add_zero(last)) : {R.IdleStall{Nat.add(last, d)} == R.IdleStall{Nat.add(_, d)} : R.Idle}
      {==}
    case +p <> +pre2:
      +hl = LA.ri.and_l(Nat.is_le(p, d), RetryIdle.gaps_within(pre2, d), within)
      +hr = LA.ri.and_r(Nat.is_le(p, d), RetryIdle.gaps_within(pre2, d), within)
      %Equal.sym(Bool, Nat.is_gt(p, d), False{}, PMC.mc.le_ngt(p, d, hl)) : {R.idle.sel(_, R.IdleStall{Nat.add(last, d)}, R.idle.go(List.append(&2, Nat, pre2, g <> rest), d, Nat.add(last, p))) == R.IdleStall{Nat.add(Nat.add(last, RetryIdle.gaps_sum(p <> pre2)), d)} : R.Idle}
      %LA.ri.add_assoc(last, p, RetryIdle.gaps_sum(pre2)) : {R.idle.go(List.append(&2, Nat, pre2, g <> rest), d, Nat.add(last, p)) == R.IdleStall{Nat.add(_, d)} : R.Idle}
      ms.go(pre2, g, rest, d, Nat.add(last, p), hr, late)

def ms.top(pre: List<&2, Nat>, +g: Nat, +rest: List<&2, Nat>, +d: Nat, +within: {RetryIdle.gaps_within(pre, d) == True{} : Bool}, +late: {Nat.is_gt(g, d) == True{} : Bool}) -> {R.idle(List.append(&2, Nat, pre, g <> rest), d) == R.IdleStall{Nat.add(RetryIdle.gaps_sum(pre), d)} : R.Idle}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_gt(g, d), True{}, late) : {R.idle.sel(_, R.IdleStall{d}, R.idle.go(rest, d, g)) == R.IdleStall{d} : R.Idle}
      {==}
    case +p <> +pre2:
      +hl = LA.ri.and_l(Nat.is_le(p, d), RetryIdle.gaps_within(pre2, d), within)
      +hr = LA.ri.and_r(Nat.is_le(p, d), RetryIdle.gaps_within(pre2, d), within)
      %Equal.sym(Bool, Nat.is_gt(p, d), False{}, PMC.mc.le_ngt(p, d, hl)) : {R.idle.sel(_, R.IdleStall{d}, R.idle.go(List.append(&2, Nat, pre2, g <> rest), d, p)) == R.IdleStall{Nat.add(Nat.add(p, RetryIdle.gaps_sum(pre2)), d)} : R.Idle}
      ms.go(pre2, g, rest, d, p, hr, late)

def RetryIdle.idle_model_stalls(pre, g, rest, d, within, late):
  (ms.top(pre, g, rest, d, within, late), {==})
