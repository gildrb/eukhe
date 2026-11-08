# eukhe: the proof of LAW wait_any_entry_refuses
#
# PROOF: the entry answers either a decision, which opens with a Nat
# (never 'E': wire_nat_not_err), or the one error form; so an answer
# that opens with 'E' is that error form.

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ../../bend/ffi_wait_any.bend as FWa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg

def waf.pick_ok(p: Wa.Pick) -> {LawsBase.wire_opens_err(FWa.put_pick(p)) == False{} : Bool}:
  match p:
    case Wa.Waits{}:
      Wire.wire_nat_not_err(0n, "")
    case Wa.Takes{i}:
      Wire.wire_nat_not_err(1n, Wr.put_nat(i, ""))
    case Wa.NoWork{}:
      Wire.wire_nat_not_err(2n, "")
    case Wa.Capped{}:
      Wire.wire_nat_not_err(3n, "")
    case Wa.Stopped{}:
      Wire.wire_nat_not_err(4n, "")

def waf.out_ok(o: Wa.Out) -> {LawsBase.wire_opens_err(FWa.put_step(o)) == False{} : Bool}:
  match o:
    case Wa.Out{d, k}:
      match d:
        case Wa.D{w, p}:
          Wire.wire_nat_not_err(w, Wr.put_nat(FWa.phase_code(p), Wr.put_nat(k, "")))

def waf.answer_ok(q: FWa.Req) -> {LawsBase.wire_opens_err(FWa.answer(q)) == False{} : Bool}:
  match q:
    case FWa.QPoll{n, c, l, ts}:
      waf.pick_ok(Wa.poll(n, c, l, ts))
    case FWa.QStep{k, d, e}:
      waf.out_ok(Wa.step(k, d, e))
    case FWa.QTimeout{a}:
      Wire.wire_nat_not_err(Wa.timeout(a), "")

def waf.refuse(d: Wr.Dec<FWa.Req>, bad: {LawsBase.wire_opens_err(FWa.ffi.got(d)) == True{} : Bool}) -> {FWa.ffi.got(d) == Wr.err("wait_any: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FWa.answer(q) == Wr.err("wait_any: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FWa.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FWa.answer(q)), True{}, bad), waf.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def WaitAny.wait_any_entry_refuses(s, bad):
  waf.refuse(FWa.get_req(s), bad)
