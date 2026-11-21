# eukhe: the proof of LAW work_left_entry_refuses
#
# PROOF: the entry answers either a step, which opens with its tag (never
# 'E': Wire.wire_nat_not_err), or the one error form; so an answer that
# opens with 'E' is that error form.

import Base
import ../../bend/progress.bend as Pg
import ../../bend/work_left.bend as Wl
import ../../bend/ffi_work_left.bend as FWl
import ../../bend/wire.bend as Wr
import ../../spec/agents/work_left.bend as SpL
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/work_left.bend as WorkLeft
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg

def wr.step_ok(st: Wl.Step) -> {LawsBase.wire_opens_err(FWl.put_step(st, "")) == False{} : Bool}:
  match st:
    case Wl.Continue{m}:
      Wire.wire_nat_not_err(0n, Wr.put_nat(m, ""))
    case Wl.Yield{}:
      Wire.wire_nat_not_err(1n, "")
    case Wl.Ask{}:
      Wire.wire_nat_not_err(2n, "")

def wr.refuse(d: Wr.Dec<Wl.Facts>, bad: {LawsBase.wire_opens_err(FWl.ffi.got(d)) == True{} : Bool}) -> {FWl.ffi.got(d) == Wr.err("work_left: malformed request") : String}:
  match d:
    case Wr.Got{+f, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FWl.put_step(Wl.decide(f), "") == Wr.err("work_left: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FWl.put_step(Wl.decide(f), "")), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FWl.put_step(Wl.decide(f), "")), True{}, bad), wr.step_ok(Wl.decide(f))))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def WorkLeft.work_left_entry_refuses(s, bad):
  wr.refuse(FWl.get_facts(s), bad)
