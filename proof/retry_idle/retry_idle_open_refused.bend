# eukhe: the proof of LAW retry_idle_open_refused
# An open read whole answers nothing to do (shut) or the model's open, no
# error form either way (LA.ri.reply_ok); every other input shuts the
# stepper with the malformed open.
import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ../../laws/base.bend as LawsBase
import ./base.bend as LA

def orf.armed(b: Bool, +d: Nat) -> {LawsBase.wire_opens_err(RetryIdle.ri_reply(Fi.open.armed(b, d))) == False{} : Bool}:
  match b:
    case True{}:
      LA.ri.reply_ok(R.idle.open(d))
    case False{}:
      {==}

# an open read with nothing after it is answered with no error form
def orf.fin(o: Fi.Open, err: {LawsBase.wire_opens_err(RetryIdle.ri_reply(Fi.open.end(True{}, o))) == True{} : Bool}) -> {Fi.open.end(True{}, o) == (Fi.Shut{}, Wr.err("retry_idle: malformed open")) : Fi.St & String}:
  match o:
    case Fi.Open{+nan, +neg, +whole, +frac, +dd}:
      LA.ri.absurd({Fi.open.end(True{}, Fi.Open{nan, neg, whole, frac, dd}) == (Fi.Shut{}, Wr.err("retry_idle: malformed open")) : Fi.St & String}, Equal.trans(Bool, False{}, LawsBase.wire_opens_err(RetryIdle.ri_reply(Fi.open.armed(R.idle.arm(nan, neg, whole, frac), dd))), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(RetryIdle.ri_reply(Fi.open.armed(R.idle.arm(nan, neg, whole, frac), dd))), False{}, orf.armed(R.idle.arm(nan, neg, whole, frac), dd)), err))

def orf.got(d: Wr.Dec<Fi.Open>, err: {LawsBase.wire_opens_err(RetryIdle.ri_reply(Fi.open.go(d))) == True{} : Bool}) -> {Fi.open.go(d) == (Fi.Shut{}, Wr.err("retry_idle: malformed open")) : Fi.St & String}:
  match d:
    case Wr.Got{o, r}:
      match r:
        case SNil{}:
          orf.fin(o, err)
        case SCon{h, t}:
          {==}
    case Wr.Bad{}:
      {==}

def RetryIdle.retry_idle_open_refused(i, err):
  orf.got(Fi.get_open(i), err)
