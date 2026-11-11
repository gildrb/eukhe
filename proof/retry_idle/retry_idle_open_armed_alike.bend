# eukhe: the proof of LAW retry_idle_open_armed_alike
# Each spelled open is read whole (LA.ri.open_spelled); a whole part above
# 0, or 0 with a fraction, computes to armed, like 1 ms: each opens the
# model's open of d.
import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ../../laws/base.bend as LawsBase
import ./base.bend as LA

# a spelled open that the facts arm opens as one of 1 ms
def aa.one(+whole: Nat, +frac: Bool, +d: Nat, +fd: {LawsBase.wire_fits(d) == True{} : Bool}, fits: {Bool.and(LawsBase.wire_fits(whole), LawsBase.wire_fits(d)) == True{} : Bool}, on: {R.idle.arm(False{}, False{}, whole, frac) == True{} : Bool}) -> {Fi.open(RetryIdle.spell_open(False{}, False{}, whole, frac, d)) == Fi.open(RetryIdle.spell_open(False{}, False{}, 1n, False{}, d)) : Fi.St & String}:
  %Equal.sym(Fi.St & String, Fi.open(RetryIdle.spell_open(False{}, False{}, whole, frac, d)), Fi.open.end(True{}, Fi.Open{False{}, False{}, whole, frac, d}), LA.ri.open_spelled(False{}, False{}, whole, frac, d, fits)) : {_ == Fi.open(RetryIdle.spell_open(False{}, False{}, 1n, False{}, d)) : Fi.St & String}
  %Equal.sym(Fi.St & String, Fi.open(RetryIdle.spell_open(False{}, False{}, 1n, False{}, d)), Fi.open.end(True{}, Fi.Open{False{}, False{}, 1n, False{}, d}), LA.ri.open_spelled(False{}, False{}, 1n, False{}, d, fd)) : {Fi.open.end(True{}, Fi.Open{False{}, False{}, whole, frac, d}) == _ : Fi.St & String}
  %Equal.sym(Bool, R.idle.arm(False{}, False{}, whole, frac), True{}, on) : {Fi.open.armed(_, d) == Fi.open.armed(True{}, d) : Fi.St & String}
  {==}

def RetryIdle.retry_idle_open_armed_alike(w, frac, d, fits):
  +f = fits
  +fd = LA.ri.and_r(LawsBase.wire_fits(1n+w), LawsBase.wire_fits(d), f)
  (aa.one(1n+w, frac, d, fd, f, {==}), aa.one(0n, True{}, d, fd, fd, {==}))
