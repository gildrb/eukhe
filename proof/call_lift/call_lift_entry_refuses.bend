# eukhe: the proof of LAW call_lift_entry_refuses
#
# PROOF: the entry answers either the lifts of a request read whole, which
# open with their count (never 'E': wire_nat_not_err), or the one error
# form; so an answer that opens with 'E' is that error form.

import Base
import ../../bend/call_lift.bend as Cl
import ../../bend/ffi_call_lift.bend as FCl
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/call_lift.bend as CallLift
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg

def clr.done(b: Bool, +cs: List<&2, Cl.Call>, bad: {LawsBase.wire_opens_err(FCl.ffi.done(cs, b)) == True{} : Bool}) -> {FCl.ffi.done(cs, b) == Wr.err("call_lift: malformed request") : String}:
  match b:
    case True{}:
      LStg.stg.absurd({FCl.answer(cs) == Wr.err("call_lift: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FCl.answer(cs)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FCl.answer(cs)), True{}, bad), Wire.wire_nat_not_err(List.length(&2, Cl.Call, cs), FCl.put_lifts(Cl.table(), cs, ""))))
    case False{}:
      {==}

def clr.got(d: Wr.Dec<List<&2, Cl.Call>>, bad: {LawsBase.wire_opens_err(FCl.ffi.got(d)) == True{} : Bool}) -> {FCl.ffi.got(d) == Wr.err("call_lift: malformed request") : String}:
  match d:
    case Wr.Got{+cs, +s}:
      clr.done(Wr.end(s), cs, bad)
    case Wr.Bad{}:
      {==}

def CallLift.call_lift_entry_refuses(s, bad):
  clr.got(FCl.get_req(s), bad)
