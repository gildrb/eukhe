# eukhe: the proof of LAW call_lift_entry_malformed_exact
#
# PROOF: the entry reads every input as the laws' reader does (cle.req); where that reader finds no whole request (it fails, or input is left over), the entry answers its error form, and a request read whole contradicts the premise.

import Base
import ../../bend/call_lift.bend as Cl
import ../../bend/ffi_call_lift.bend as FCl
import ../../bend/wire.bend as Wr
import ../../spec/harness/lift_wire.bend as SpW
import ../../laws/call_lift.bend as CallLift
import ./base/read.bend as LCallLiftRead

def cle.MI(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def cle.some_none(-A: Data, -x: A, -G: Type, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  %e : cle.MI(A, _, G)
  Unit{}

def cle.end(b: Bool, -cs: List<&2, Cl.Call>, no: {SpW.r_whole.end(b, cs) == None{} : Maybe<&2, List<&2, Cl.Call>>}) -> {FCl.ffi.done(cs, b) == Wr.err("call_lift: malformed request") : String}:
  match b:
    case True{}:
      cle.some_none(List<&2, Cl.Call>, cs, {FCl.answer(cs) == Wr.err("call_lift: malformed request") : String}, no)
    case False{}:
      {==}

def cle.whole(r: Wr.Dec<List<&2, Cl.Call>>, no: {SpW.r_whole(r) == None{} : Maybe<&2, List<&2, Cl.Call>>}) -> {FCl.ffi.got(r) == Wr.err("call_lift: malformed request") : String}:
  match r:
    case Wr.Got{cs, +s}:
      cle.end(Wr.end(s), cs, no)
    case Wr.Bad{}:
      {==}

def CallLift.call_lift_entry_malformed_exact(s, no):
  %Equal.sym(Wr.Dec<List<&2, Cl.Call>>, FCl.get_req(s), Wr.get_list(~Cl.Call, ~SpW.r_call, s), LCallLiftRead.cle.req(s)) : {FCl.ffi.got(_) == Wr.err("call_lift: malformed request") : String}
  cle.whole(Wr.get_list(~Cl.Call, ~SpW.r_call, s), no)
