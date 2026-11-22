# eukhe: the proof of LAW prior_entry_answers
# The run's flag computes once split; the stalls and the work read back
# by the wire's round trip.

import Base
import ../../laws/work.bend as Work
import ../../bend/ffi_work.bend as FW
import ../../bend/progress.bend as Pr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire

def pea.fin(r: Bool, +s: Nat, +w: Nat) -> {FW.run.end(True{}, Some{Pr.Last{r, s, w}}) == Work.pe_answer(Some{Pr.Last{r, s, w}}) : String}:
  match r:
    case True{}:
      {==}
    case False{}:
      {==}

def pea.nums(r: Bool, +s: Nat, +w: Nat, hs: {LawsBase.wire_fits(s) == True{} : Bool}, hw: {LawsBase.wire_fits(w) == True{} : Bool}) -> {FW.run(FW.get_last.stalls(r, Wr.get_nat(Wr.put_nat(s, Wr.put_nat(w, ""))))) == Work.pe_answer(Some{Pr.Last{r, s, w}}) : String}:
  %LWire.pw6.nat(s, Wr.put_nat(w, ""), hs) : {FW.run(FW.get_last.stalls(r, _)) == Work.pe_answer(Some{Pr.Last{r, s, w}}) : String}
  %LWire.pw6.nat(w, "", hw) : {FW.run(FW.get_last.work(r, s, _)) == Work.pe_answer(Some{Pr.Last{r, s, w}}) : String}
  pea.fin(r, s, w)

def pea.flags(r: Bool, +s: Nat, +w: Nat, hs: {LawsBase.wire_fits(s) == True{} : Bool}, hw: {LawsBase.wire_fits(w) == True{} : Bool}) -> {FW.ffi(Work.pe_spell_req(Some{Pr.Last{r, s, w}})) == Work.pe_answer(Some{Pr.Last{r, s, w}}) : String}:
  match r:
    case True{}:
      pea.nums(True{}, s, w, hs, hw)
    case False{}:
      pea.nums(False{}, s, w, hs, hw)

def Work.prior_entry_answers(m, h):
  match m:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case Pr.Last{r, +s, +w}:
          +hh = h
          pea.flags(r, s, w, LLogicBool.wr_and_l(LawsBase.wire_fits(s), LawsBase.wire_fits(w), hh), LLogicBool.wr_and_r(LawsBase.wire_fits(s), LawsBase.wire_fits(w), hh))
