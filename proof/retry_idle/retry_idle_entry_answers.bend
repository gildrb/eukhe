# eukhe: the proof of LAW retry_idle_entry_answers
# A spelled open is read whole, one field at a time (LA.ri.open_spelled);
# an armed one is the model's open, its reply spelled (LA.ri.reply_pair).
import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ../../laws/base.bend as LawsBase
import ./base.bend as LA

def ao.armed(armed: Bool, +d: Nat) -> {Fi.open.armed(armed, d) == RetryIdle.open_spec(armed, d) : Fi.St & String}:
  match armed:
    case True{}:
      LA.ri.reply_pair(R.idle.open(d))
    case False{}:
      {==}

def RetryIdle.retry_idle_entry_answers(nan, neg, whole, frac, d, fits):
  Equal.trans(Fi.St & String, Fi.open(RetryIdle.spell_open(nan, neg, whole, frac, d)), Fi.open.end(True{}, Fi.Open{nan, neg, whole, frac, d}), RetryIdle.open_spec(R.idle.arm(nan, neg, whole, frac), d), LA.ri.open_spelled(nan, neg, whole, frac, d, fits), ao.armed(R.idle.arm(nan, neg, whole, frac), d))
