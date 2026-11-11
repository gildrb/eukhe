# eukhe: the proof of LAW retry_idle_open_unarmed
# Each spelled open is read whole (LA.ri.open_spelled); NaN, a negative
# sign and a zero whole part with no fraction compute to unarmed, which
# opens the shut state with nothing to do.
import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ../../laws/base.bend as LawsBase
import ./base.bend as LA

# a spelled open that the facts leave unarmed
def ou.one(+nan: Bool, +neg: Bool, +whole: Nat, +frac: Bool, +d: Nat, fits: {Bool.and(LawsBase.wire_fits(whole), LawsBase.wire_fits(d)) == True{} : Bool}, off: {R.idle.arm(nan, neg, whole, frac) == False{} : Bool}) -> {Fi.open(RetryIdle.spell_open(nan, neg, whole, frac, d)) == (Fi.Shut{}, RetryIdle.spell_reply(None{})) : Fi.St & String}:
  %Equal.sym(Fi.St & String, Fi.open(RetryIdle.spell_open(nan, neg, whole, frac, d)), Fi.open.end(True{}, Fi.Open{nan, neg, whole, frac, d}), LA.ri.open_spelled(nan, neg, whole, frac, d, fits)) : {_ == (Fi.Shut{}, RetryIdle.spell_reply(None{})) : Fi.St & String}
  %Equal.sym(Bool, R.idle.arm(nan, neg, whole, frac), False{}, off) : {Fi.open.armed(_, d) == (Fi.Shut{}, RetryIdle.spell_reply(None{})) : Fi.St & String}
  {==}

def RetryIdle.retry_idle_open_unarmed(neg, whole, frac, d, fits):
  +f = fits
  +fd = LA.ri.and_r(LawsBase.wire_fits(whole), LawsBase.wire_fits(d), f)
  (ou.one(True{}, neg, whole, frac, d, f, {==}), ou.one(False{}, True{}, whole, frac, d, f, {==}), ou.one(False{}, False{}, 0n, False{}, d, fd, {==}))
