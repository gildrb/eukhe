# eukhe: the proof of LAW retry_idle_step_refused
# An event read whole runs the model's step, whose reply is no error form
# (LA.ri.reply_ok); every other input keeps the state and answers the
# malformed event.
import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ../../laws/base.bend as LawsBase
import ./base.bend as LA

def sf.got(+s: R.IdleSt, d: Wr.Dec<R.IdleEv>, err: {LawsBase.wire_opens_err(RetryIdle.ri_reply(Fi.step.ev(s, d))) == True{} : Bool}) -> {Fi.step.ev(s, d) == (Fi.Live{s}, Wr.err("retry_idle: malformed event")) : Fi.St & String}:
  match d:
    case Wr.Got{+e, r}:
      match r:
        case SNil{}:
          LA.ri.absurd({Fi.step.ev(s, Wr.Got{e, SNil{}}) == (Fi.Live{s}, Wr.err("retry_idle: malformed event")) : Fi.St & String}, Equal.trans(Bool, False{}, LawsBase.wire_opens_err(RetryIdle.ri_reply(Fi.reply(R.idle.step(s, e)))), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(RetryIdle.ri_reply(Fi.reply(R.idle.step(s, e)))), False{}, LA.ri.reply_ok(R.idle.step(s, e))), err))
        case SCon{h, t}:
          {==}
    case Wr.Bad{}:
      {==}

def RetryIdle.retry_idle_step_refused(s, i, err):
  sf.got(s, Fi.get_ev(i), err)
