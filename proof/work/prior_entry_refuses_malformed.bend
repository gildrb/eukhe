# eukhe: the proof of LAW prior_entry_refuses_malformed
#
# PROOF: the call answers either a prior, which opens with its tag (a Nat:
# never 'E', wire_nat_not_err), or its error form.

import Base
import ../../bend/ffi_work.bend as FW
import ../../bend/progress.bend as Pr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/work.bend as Work
import ../base/logic/logic.bend as LLogicLogic

# a prior opens with its tag
def per.prior(p: Maybe<&2, Pr.Prior>) -> {LawsBase.wire_opens_err(FW.put_prior(p)) == False{} : Bool}:
  match p:
    case None{}:
      Wire.wire_nat_not_err(0n, "")
    case Some{x}:
      match x:
        case Pr.Prior{s, w}:
          Wire.wire_nat_not_err(1n, Wr.put_nat(s, Wr.put_nat(w, "")))

def per.end(b: Bool, +m: Maybe<&2, Pr.Last>, err: {LawsBase.wire_opens_err(FW.run.end(b, m)) == True{} : Bool}) -> {FW.run.end(b, m) == Wr.err("work: malformed request") : String}:
  match b:
    case True{}:
      LLogicLogic.wn_absurd({FW.put_prior(Pr.compared(m)) == Wr.err("work: malformed request") : String},
        Equal.trans(Bool, False{}, LawsBase.wire_opens_err(FW.put_prior(Pr.compared(m))), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(FW.put_prior(Pr.compared(m))), False{}, per.prior(Pr.compared(m))), err))
    case False{}:
      {==}

def per.run(d: Wr.Dec<Maybe<&2, Pr.Last>>, err: {LawsBase.wire_opens_err(FW.run(d)) == True{} : Bool}) -> {FW.run(d) == Wr.err("work: malformed request") : String}:
  match d:
    case Wr.Got{m, r}:
      per.end(Wr.end(r), m, err)
    case Wr.Bad{}:
      {==}

def Work.prior_entry_refuses_malformed(s, err):
  per.run(FW.get_last(s), err)
