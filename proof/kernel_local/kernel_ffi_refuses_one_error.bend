# eukhe: the proof of LAW kernel_ffi_refuses_one_error
#
# The entry answers a request with a Nat first (a count or an end's tag:
# never 'E', wire_nat_not_err), and anything else with the one error form;
# so an answer that opens with 'E' is that error form.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/kernel_local.bend as KL
import ../../bend/ffi_kernel_local.bend as FKL
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/kernel_local.bend as KernelLocal
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ./base.bend as LKL

def kfr.end(e: KL.End) -> {LawsBase.wire_opens_err(FKL.put_end(e, "")) == False{} : Bool}:
  match e:
    case KL.Got{}:
      {==}
    case KL.Busy{}:
      {==}
    case KL.Freed{}:
      {==}
    case KL.Crash{}:
      {==}

# no answer to a request opens with 'E'
def kfr.answer(a: KL.Ask) -> {LawsBase.wire_opens_err(FKL.answer(a)) == False{} : Bool}:
  match a:
    case KL.AskPlan{uv, python, env}:
      +xs = KL.plan(uv, python, env)
      Wire.wire_nat_not_err(List.length(&2, KL.Act, xs), FKL.put_acts.items(xs, ""))
    case KL.AskSweep{ls}:
      +bs = KL.keeps(ls)
      Wire.wire_nat_not_err(List.length(&2, Bool, bs), FKL.put_bools.items(bs, ""))
    case KL.AskLock{x}:
      kfr.end(KL.attempt(KL.lock.of(x)))

def kfr.run(r: Wr.Dec<KL.Ask>, bad: {LawsBase.wire_opens_err(FKL.run(r)) == True{} : Bool}) -> {FKL.run(r) == Wr.err("kernel_local: malformed request") : String}:
  match r:
    case Wr.Got{+a, rest}:
      match rest:
        case SNil{}:
          LKL.kl.absurd({FKL.answer(a) == Wr.err("kernel_local: malformed request") : String}, Equal.trans(Bool, False{}, LawsBase.wire_opens_err(FKL.answer(a)), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(FKL.answer(a)), False{}, kfr.answer(a)), bad))
        case SCon{c, t}:
          {==}
    case Wr.Bad{}:
      {==}

def KernelLocal.kernel_ffi_refuses_one_error(s, bad):
  kfr.run(FKL.get_ask(s), bad)
