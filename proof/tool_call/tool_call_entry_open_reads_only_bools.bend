# eukhe: the proof of LAW tool_call_entry_open_reads_only_bools
# What the open's decoder reads is a Bool's spelling, then its rest
# (wire_bool_exact); the reply is the error form unless nothing is left.

import Base
import ../../bend/ffi_tool_call.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/tool_call.bend as ToolCall
import ../../laws/wire.bend as Wire
import ../wire/base/spell.bend as LAWireSpell
import ../wire/wire_bool_exact.bend as PWireBoolExact

def tco.G(i: String) -> Type:
  Sigma<&1, &1, Bool, b => {i == ToolCall.tc_spell_open(b) : String}>

def tco.fin(+i: String, b: Bool, r: String, pre: {i == Wr.put_bool(b, r) : String}, ok: {String.eq(ToolCall.tc_reply(FTc.open.end(Wr.end(r), b)), ToolCall.tc_bad_open()) == False{} : Bool}) -> tco.G(i):
  match r:
    case SNil{}:
      (b, pre)
    case SCon{x, y}:
      LAWireSpell.ws_absurd(tco.G(i), ok)

def tco.main(+i: String, d: Wr.Dec<Bool>, er: {Wr.get_bool(i) == d : Wr.Dec<Bool>}, ok: {String.eq(ToolCall.tc_reply(FTc.open.first(d)), ToolCall.tc_bad_open()) == False{} : Bool}) -> tco.G(i):
  match d:
    case Wr.Got{+b, +r}:
      tco.fin(i, b, r, Wire.wire_bool_exact(i, b, r, er), ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(tco.G(i), ok)

def ToolCall.tool_call_entry_open_reads_only_bools(i, other):
  tco.main(i, Wr.get_bool(i), {==}, other)
