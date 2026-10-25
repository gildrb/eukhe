# eukhe: the proof of LAW gateway_commands_entry_refuses
#
# PROOF: the entry answers either a meaning, opening with a Nat tag (never
# 'E': wire_nat_not_err), or the one error form; so an answer that opens
# with 'E' is that error form.

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/ffi_gateway_commands.bend as FGc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/gateway_commands.bend as GatewayCommands
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg

def gcf.out_ok(o: Gc.Out) -> {LawsBase.wire_opens_err(FGc.put_out(o)) == False{} : Bool}:
  match o:
    case Gc.OCommand{c}:
      Wire.wire_nat_not_err(0n, FGc.put_cmd(c))
    case Gc.OAnswer{t}:
      Wire.wire_nat_not_err(1n, Wr.put_str(t, ""))
    case Gc.OPrompt{}:
      {==}

def gcf.answer_ok(q: FGc.Req) -> {LawsBase.wire_opens_err(FGc.answer(q)) == False{} : Bool}:
  match q:
    case FGc.QParse{t, ns}:
      gcf.out_ok(Gc.parse(t, ns))

def gcf.refuse(d: Wr.Dec<FGc.Req>, bad: {LawsBase.wire_opens_err(FGc.ffi.got(d)) == True{} : Bool}) -> {FGc.ffi.got(d) == Wr.err("gateway_commands: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FGc.answer(q) == Wr.err("gateway_commands: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FGc.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FGc.answer(q)), True{}, bad), gcf.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def GatewayCommands.gateway_commands_entry_refuses(s, bad):
  gcf.refuse(FGc.get_req(s), bad)
