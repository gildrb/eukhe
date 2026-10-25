# eukhe: the proof of LAW gateway_commands_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left
# (gateway_commands_entry_reads), so the entry answers the code's parse,
# which is the spec's (gateway_commands_spec), spelled by the spec's tags
# (gca.out, case by case).

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/ffi_gateway_commands.bend as FGc
import ../../bend/wire.bend as Wr
import ../../laws/gateway_commands.bend as GatewayCommands
import ./gateway_commands_spec.bend as PGatewayCommandsSpec
import ./gateway_commands_entry_reads.bend as PGatewayCommandsEntryReads

def gca.cmd(c: Gc.Cmd) -> {FGc.put_cmd(c) == GatewayCommands.gc_w_cmd(c) : String}:
  match c:
    case Gc.CHelp{}:
      {==}
    case Gc.CSessions{}:
      {==}
    case Gc.CUse{a}:
      {==}
    case Gc.CLatest{}:
      {==}
    case Gc.CNew{}:
      {==}
    case Gc.CStop{}:
      {==}
    case Gc.CStatus{}:
      {==}
    case Gc.CMemory{}:
      {==}

def gca.out(o: Gc.Out) -> {FGc.put_out(o) == GatewayCommands.gc_w_out(o) : String}:
  match o:
    case Gc.OCommand{+c}:
      %gca.cmd(c) : {Wr.put_nat(0n, FGc.put_cmd(c)) == Wr.put_nat(0n, _) : String}
      {==}
    case Gc.OAnswer{t}:
      {==}
    case Gc.OPrompt{}:
      {==}

def gca.reply(q: FGc.Req) -> {FGc.answer(q) == GatewayCommands.gc_w_reply(q) : String}:
  match q:
    case FGc.QParse{+t, +ns}:
      %Equal.sym(Gc.Out, Gc.parse(t, ns), GatewayCommands.gc_parse(t, ns), GatewayCommands.gateway_commands_spec(t, ns)) : {FGc.put_out(_) == GatewayCommands.gc_w_out(GatewayCommands.gc_parse(t, ns)) : String}
      gca.out(GatewayCommands.gc_parse(t, ns))

def GatewayCommands.gateway_commands_entry_answers(q, h):
  %Equal.sym(Wr.Dec<FGc.Req>, FGc.get_req(GatewayCommands.gc_w_req(q, "")), Wr.Got{q, ""}, GatewayCommands.gateway_commands_entry_reads(q, "", h)) : {FGc.ffi.got(_) == GatewayCommands.gc_w_reply(q) : String}
  gca.reply(q)
