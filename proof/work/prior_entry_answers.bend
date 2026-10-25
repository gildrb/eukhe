# eukhe: the proof of LAW prior_entry_answers
# The flags compute once split; the stalls and the work read back by
# the wire's round trip.

import Base
import ../../laws/work.bend as Work
import ../../bend/ffi_work.bend as FW
import ../../bend/progress.bend as Pr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire

def pea.fin(r: Bool, g: Bool, +s: Nat, +w: Nat) -> {FW.run.end(True{}, Some{Pr.Last{r, g, s, w}}) == Work.pe_answer(Some{Pr.Last{r, g, s, w}}) : String}:
  match r:
    case True{}:
      match g:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match g:
        case True{}:
          {==}
        case False{}:
          {==}

def pea.nums(r: Bool, g: Bool, +s: Nat, +w: Nat, hs: {LawsBase.wire_fits(s) == True{} : Bool}, hw: {LawsBase.wire_fits(w) == True{} : Bool}) -> {FW.run(FW.get_last.stalls(r, g, Wr.get_nat(Wr.put_nat(s, Wr.put_nat(w, ""))))) == Work.pe_answer(Some{Pr.Last{r, g, s, w}}) : String}:
  %LWire.pw6.nat(s, Wr.put_nat(w, ""), hs) : {FW.run(FW.get_last.stalls(r, g, _)) == Work.pe_answer(Some{Pr.Last{r, g, s, w}}) : String}
  %LWire.pw6.nat(w, "", hw) : {FW.run(FW.get_last.work(r, g, s, _)) == Work.pe_answer(Some{Pr.Last{r, g, s, w}}) : String}
  pea.fin(r, g, s, w)

def pea.flags(r: Bool, g: Bool, +s: Nat, +w: Nat, hs: {LawsBase.wire_fits(s) == True{} : Bool}, hw: {LawsBase.wire_fits(w) == True{} : Bool}) -> {FW.ffi(Work.pe_spell_req(Some{Pr.Last{r, g, s, w}})) == Work.pe_answer(Some{Pr.Last{r, g, s, w}}) : String}:
  match r:
    case True{}:
      match g:
        case True{}:
          pea.nums(True{}, True{}, s, w, hs, hw)
        case False{}:
          pea.nums(True{}, False{}, s, w, hs, hw)
    case False{}:
      match g:
        case True{}:
          pea.nums(False{}, True{}, s, w, hs, hw)
        case False{}:
          pea.nums(False{}, False{}, s, w, hs, hw)

def Work.prior_entry_answers(m, h):
  match m:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case Pr.Last{r, g, +s, +w}:
          +hh = h
          pea.flags(r, g, s, w, LLogicBool.wr_and_l(LawsBase.wire_fits(s), LawsBase.wire_fits(w), hh), LLogicBool.wr_and_r(LawsBase.wire_fits(s), LawsBase.wire_fits(w), hh))
