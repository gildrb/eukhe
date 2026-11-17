# eukhe: the proof of LAW headless_exit_entry_refuses
#
# PROOF: the entry answers either an exit, which opens with its code (a
# Nat, never 'E': wire_nat_not_err), or the one error form; so an answer
# that opens with 'E' is that error form.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../bend/ffi_headless_exit.bend as FHx
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/headless_exit.bend as HeadlessExit
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg

def hxr.put_ok(v: Hx.Verdict) -> {LawsBase.wire_opens_err(FHx.put_verdict(v, "")) == False{} : Bool}:
  match v:
    case Hx.Verdict{n, c}:
      Wire.wire_nat_not_err(n, FHx.put_cause(c, ""))

def hxr.refuse(d: Wr.Dec<Hx.Facts>, bad: {LawsBase.wire_opens_err(FHx.ffi.got(d)) == True{} : Bool}) -> {FHx.ffi.got(d) == Wr.err("headless_exit: malformed request") : String}:
  match d:
    case Wr.Got{+f, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FHx.put_verdict(Hx.decide(f), "") == Wr.err("headless_exit: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FHx.put_verdict(Hx.decide(f), "")), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FHx.put_verdict(Hx.decide(f), "")), True{}, bad), hxr.put_ok(Hx.decide(f))))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def HeadlessExit.headless_exit_entry_refuses(s, bad):
  hxr.refuse(FHx.get_facts(s), bad)
