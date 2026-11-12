# eukhe: the proof of LAW retry_idle_open_reads_spelled
# What the open decoder reads is spelled, and so is the input after it,
# its numbers fit the wire (LA.ri.po); a reply that is no error form has
# nothing after the open, so the input is the spelled open.
import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ../../laws/base.bend as LawsBase
import ./base.bend as LA

# an open read with nothing after it is the spelled open
def ors.fin(-i: String, o: Fi.Open, po: LA.ri.PO(i, Wr.Got{o, SNil{}})) -> Sigma<&1, &1, Fi.Open, o => {i == RetryIdle.spell_open_of(o) : String} & {RetryIdle.open_fits(o) == True{} : Bool}>:
  match o:
    case Fi.Open{nan, neg, whole, frac, dd}:
      (Fi.Open{nan, neg, whole, frac, dd}, po)

def ors.got(-i: String, d: Wr.Dec<Fi.Open>, po: LA.ri.PO(i, d), ok: {LawsBase.wire_opens_err(RetryIdle.ri_reply(Fi.open.go(d))) == False{} : Bool}) -> Sigma<&1, &1, Fi.Open, o => {i == RetryIdle.spell_open_of(o) : String} & {RetryIdle.open_fits(o) == True{} : Bool}>:
  match d:
    case Wr.Got{o, r}:
      match r:
        case SNil{}:
          ors.fin(i, o, po)
        case SCon{h, t}:
          LA.ri.absurd_t(Sigma<&1, &1, Fi.Open, o => {i == RetryIdle.spell_open_of(o) : String} & {RetryIdle.open_fits(o) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LA.ri.absurd_t(Sigma<&1, &1, Fi.Open, o => {i == RetryIdle.spell_open_of(o) : String} & {RetryIdle.open_fits(o) == True{} : Bool}>, ok)

def RetryIdle.retry_idle_open_reads_spelled(i, ok):
  ors.got(i, Fi.get_open(i), LA.ri.po(i), ok)
