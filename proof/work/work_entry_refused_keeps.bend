# eukhe: the proof of LAW work_entry_refused_keeps
#
# PROOF: a step answers either the ledger's answer, which opens with its
# tag (a Nat: never 'E', wire_nat_not_err), or its error form with the
# ledger kept.

import Base
import ../../bend/ffi_work.bend as FW
import ../../bend/progress.bend as Pr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/work.bend as Work
import ../base/logic/logic.bend as LLogicLogic

# an answer of the ledger opens with its tag
def wrk.out(o: Pr.Out) -> {LawsBase.wire_opens_err(FW.put_out(o)) == False{} : Bool}:
  match o:
    case Pr.Read{w, r, z}:
      Wire.wire_nat_not_err(0n, Wr.put_nat(w, Wr.put_nat(r, FW.put_at(z, ""))))
    case Pr.Again{}:
      Wire.wire_nat_not_err(1n, "")

# a step that answers the ledger's answer opens with its tag
def wrk.step(-l: Pr.Led, p: Pr.Led & Pr.Out, err: {LawsBase.wire_opens_err(Work.wk_reply(FW.step.out(p))) == True{} : Bool}) -> {FW.step.out(p) == (FW.Live{l}, Wr.err("work: malformed event")) : FW.St & String}:
  match p:
    case (l2, +o):
      LLogicLogic.wn_absurd({FW.step.out((l2, o)) == (FW.Live{l}, Wr.err("work: malformed event")) : FW.St & String},
        Equal.trans(Bool, False{}, LawsBase.wire_opens_err(FW.put_out(o)), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(FW.put_out(o)), False{}, wrk.out(o)), err))

def wrk.end(b: Bool, +l: Pr.Led, +e: Pr.Ev, err: {LawsBase.wire_opens_err(Work.wk_reply(FW.step.end(b, l, e))) == True{} : Bool}) -> {FW.step.end(b, l, e) == (FW.Live{l}, Wr.err("work: malformed event")) : FW.St & String}:
  match b:
    case True{}:
      wrk.step(l, Pr.next(l, e), err)
    case False{}:
      {==}

def wrk.ev(+l: Pr.Led, d: Wr.Dec<Pr.Ev>, err: {LawsBase.wire_opens_err(Work.wk_reply(FW.step.ev(l, d))) == True{} : Bool}) -> {FW.step.ev(l, d) == (FW.Live{l}, Wr.err("work: malformed event")) : FW.St & String}:
  match d:
    case Wr.Got{e, rest}:
      wrk.end(Wr.end(rest), l, e, err)
    case Wr.Bad{}:
      {==}

def Work.work_entry_refused_keeps(l, s, err):
  wrk.ev(l, FW.get_ev(s), err)
