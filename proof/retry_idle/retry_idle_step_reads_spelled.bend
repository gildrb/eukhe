# eukhe: the proof of LAW retry_idle_step_reads_spelled
# What the event decoder reads is spelled, and so is the input after it,
# its time fits the wire (LA.ri.pe); a reply that is no error form has
# nothing after the event, so the input is the spelled event.
import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ../../laws/base.bend as LawsBase
import ./base.bend as LA

# an event read with nothing after it is the spelled event
def rs.fin(-i: String, e: R.IdleEv, pe: LA.ri.PE(i, Wr.Got{e, SNil{}})) -> Sigma<&1, &1, R.IdleEv, e => {i == RetryIdle.spell_ev(e) : String} & {RetryIdle.ev_fits(e) == True{} : Bool}>:
  match e:
    case R.IdleLife{now}:
      (R.IdleLife{now}, pe)
    case R.IdleHold{}:
      (R.IdleHold{}, pe)
    case R.IdleFree{now}:
      (R.IdleFree{now}, pe)
    case R.IdleFire{now}:
      (R.IdleFire{now}, pe)

def rs.got(+s: R.IdleSt, -i: String, d: Wr.Dec<R.IdleEv>, pe: LA.ri.PE(i, d), ok: {LawsBase.wire_opens_err(RetryIdle.ri_reply(Fi.step.ev(s, d))) == False{} : Bool}) -> Sigma<&1, &1, R.IdleEv, e => {i == RetryIdle.spell_ev(e) : String} & {RetryIdle.ev_fits(e) == True{} : Bool}>:
  match d:
    case Wr.Got{e, r}:
      match r:
        case SNil{}:
          rs.fin(i, e, pe)
        case SCon{h, t}:
          LA.ri.absurd_t(Sigma<&1, &1, R.IdleEv, e => {i == RetryIdle.spell_ev(e) : String} & {RetryIdle.ev_fits(e) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LA.ri.absurd_t(Sigma<&1, &1, R.IdleEv, e => {i == RetryIdle.spell_ev(e) : String} & {RetryIdle.ev_fits(e) == True{} : Bool}>, ok)

def RetryIdle.retry_idle_step_reads_spelled(s, i, ok):
  rs.got(s, i, Fi.get_ev(i), LA.ri.pe(i), ok)
