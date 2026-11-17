# eukhe: the proof of LAW headless_task_entry_refuses
#
# PROOF: the entry answers either a task's exit, which opens with its
# code (a Nat, never 'E': wire_nat_not_err), or the one error form; so
# an answer that opens with 'E' is that error form.

import Base
import ../../bend/headless_task.bend as Ht
import ../../bend/ffi_headless_task.bend as FHt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/headless_task.bend as HeadlessTask
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg

def htr.put_ok(v: Ht.Verdict) -> {LawsBase.wire_opens_err(FHt.put_verdict(v, "")) == False{} : Bool}:
  match v:
    case Ht.Verdict{n, t}:
      Wire.wire_nat_not_err(n, FHt.put_task(t, ""))

def htr.refuse(d: Wr.Dec<Ht.Facts>, bad: {LawsBase.wire_opens_err(FHt.ffi.got(d)) == True{} : Bool}) -> {FHt.ffi.got(d) == Wr.err("headless_task: malformed request") : String}:
  match d:
    case Wr.Got{+f, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FHt.put_verdict(Ht.decide(f), "") == Wr.err("headless_task: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FHt.put_verdict(Ht.decide(f), "")), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FHt.put_verdict(Ht.decide(f), "")), True{}, bad), htr.put_ok(Ht.decide(f))))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def HeadlessTask.headless_task_entry_refuses(s, bad):
  htr.refuse(FHt.get_facts(s), bad)
