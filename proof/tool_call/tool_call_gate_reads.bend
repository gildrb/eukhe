# eukhe: the proof of LAW tool_call_gate_reads
# The entry reads every input as the laws' reader does (LA.ep.read); a
# whole question runs as the same question spelled (LA.ep.spelled).

import Base
import ../../bend/tool_call.bend as Tc
import ../../bend/ffi_tool_call.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/tool_call.bend as ToolCall
import ../../spec/harness/effect.bend as Sp
import ./base.bend as LA

def gr.got(d: Wr.Dec<Tc.Gate>, +q: Tc.Gate, got: {ToolCall.tc_rg.whole(d) == Some{q} : Maybe<&2, Tc.Gate>}) -> {FTc.ffi.gate(d) == FTc.ffi(ToolCall.tc_spell_gate(q)) : String}:
  match d:
    case Wr.Got{+x, rest}:
      match rest:
        case SNil{}:
          %LA.tp.some_inj(Tc.Gate, x, q, got) : {FTc.ffi.end(True{}, x) == FTc.ffi(ToolCall.tc_spell_gate(_)) : String}
          LA.ep.spelled(x)
        case SCon{h, t}:
          LA.tp.none_some(Tc.Gate, {FTc.ffi.end(False{}, x) == FTc.ffi(ToolCall.tc_spell_gate(q)) : String}, q, got)
    case Wr.Bad{}:
      LA.tp.none_some(Tc.Gate, {Wr.err("tool_call: malformed gate") == FTc.ffi(ToolCall.tc_spell_gate(q)) : String}, q, got)

def ToolCall.tool_call_gate_reads(i, q, got):
  %LA.ep.read(Wr.get_nat(i)) : {FTc.ffi.gate(_) == FTc.ffi(ToolCall.tc_spell_gate(q)) : String}
  gr.got(ToolCall.tc_rg.go(Wr.get_nat(i)), q, got)
