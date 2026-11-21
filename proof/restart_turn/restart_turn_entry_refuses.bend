# eukhe: the proof of LAW restart_turn_entry_refuses
#
# PROOF: the entry answers either what follows, which opens with its tag
# (never 'E': wire_nat_not_err), or the one error form; so an answer that
# opens with 'E' is that error form.

import Base
import ../../bend/restart_turn.bend as Rt
import ../../bend/ffi_restart_turn.bend as FRt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/restart_turn.bend as RestartTurn
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg

def rtf.answer_ok(x: Rt.Next) -> {LawsBase.wire_opens_err(FRt.put_next(x)) == False{} : Bool}:
  match x:
    case Rt.Continue{n}:
      Wire.wire_nat_not_err(0n, Wr.put_nat(n, ""))
    case Rt.End{n}:
      Wire.wire_nat_not_err(1n, Wr.put_nat(n, ""))
    case Rt.Relaunch{}:
      Wire.wire_nat_not_err(2n, "")
    case Rt.Retire{}:
      Wire.wire_nat_not_err(3n, "")

def rtf.refuse(d: Wr.Dec<Rt.Fact>, bad: {LawsBase.wire_opens_err(FRt.ffi.got(d)) == True{} : Bool}) -> {FRt.ffi.got(d) == Wr.err("restart_turn: malformed request") : String}:
  match d:
    case Wr.Got{+f, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FRt.put_next(Rt.next(f)) == Wr.err("restart_turn: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FRt.put_next(Rt.next(f))), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FRt.put_next(Rt.next(f))), True{}, bad), rtf.answer_ok(Rt.next(f))))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def RestartTurn.restart_turn_entry_refuses(s, bad):
  rtf.refuse(FRt.get_req(s), bad)
