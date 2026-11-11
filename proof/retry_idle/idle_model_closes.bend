# eukhe: the proof of LAW idle_model_closes
# By induction on the gaps: a gap at most d is not above d, so the model
# goes on; the accumulated time is last plus the gaps so far (associativity).
import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ../../laws/base.bend as LawsBase
import ./base.bend as LA

# g at most d is not above d
def mc.le_ngt(g: Nat, d: Nat, e: {Nat.is_le(g, d) == True{} : Bool}) -> {Nat.is_gt(g, d) == False{} : Bool}:
  match g:
    case 0n:
      LA.ri.gt_zero(d)
    case 1n+p:
      match d:
        case 0n:
          LA.ri.absurd({Nat.is_gt(1n+p, 0n) == False{} : Bool}, e)
        case 1n+q:
          mc.le_ngt(p, q, e)

# gaps all within d, after an event at last: the model closes at last plus
# their sum
def mc.go(gs: List<&2, Nat>, +d: Nat, +last: Nat, +within: {RetryIdle.gaps_within(gs, d) == True{} : Bool}) -> {R.idle.go(gs, d, last) == R.IdleClose{Nat.add(last, RetryIdle.gaps_sum(gs))} : R.Idle}:
  match gs:
    case Nil{}:
      %Equal.sym(Nat, Nat.add(last, 0n), last, LA.ri.add_zero(last)) : {R.IdleClose{last} == R.IdleClose{_} : R.Idle}
      {==}
    case +g <> +rest:
      +hl = LA.ri.and_l(Nat.is_le(g, d), RetryIdle.gaps_within(rest, d), within)
      +hr = LA.ri.and_r(Nat.is_le(g, d), RetryIdle.gaps_within(rest, d), within)
      %Equal.sym(Bool, Nat.is_gt(g, d), False{}, mc.le_ngt(g, d, hl)) : {R.idle.sel(_, R.IdleStall{Nat.add(last, d)}, R.idle.go(rest, d, Nat.add(last, g))) == R.IdleClose{Nat.add(last, RetryIdle.gaps_sum(g <> rest))} : R.Idle}
      %LA.ri.add_assoc(last, g, RetryIdle.gaps_sum(rest)) : {R.idle.go(rest, d, Nat.add(last, g)) == R.IdleClose{_} : R.Idle}
      mc.go(rest, d, Nat.add(last, g), hr)

def mc.top(+g: Nat, +gs: List<&2, Nat>, +d: Nat, +within: {RetryIdle.gaps_within(g <> gs, d) == True{} : Bool}) -> {R.idle(g <> gs, d) == R.IdleClose{RetryIdle.gaps_sum(g <> gs)} : R.Idle}:
  +hl = LA.ri.and_l(Nat.is_le(g, d), RetryIdle.gaps_within(gs, d), within)
  +hr = LA.ri.and_r(Nat.is_le(g, d), RetryIdle.gaps_within(gs, d), within)
  %Equal.sym(Bool, Nat.is_gt(g, d), False{}, mc.le_ngt(g, d, hl)) : {R.idle.sel(_, R.IdleStall{d}, R.idle.go(gs, d, g)) == R.IdleClose{Nat.add(g, RetryIdle.gaps_sum(gs))} : R.Idle}
  mc.go(gs, d, g, hr)

def RetryIdle.idle_model_closes(g, gs, d, within):
  mc.top(g, gs, d, within)
