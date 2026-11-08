# eukhe: the proof of LAW tool_call_gate_malformed_exact
# The entry reads every input as the laws' reader does (LA.ep.read);
# where that reader finds no whole question, the entry answers its error
# form.

import Base
import ../../bend/tool_call.bend as Tc
import ../../bend/ffi_tool_call.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/tool_call.bend as ToolCall
import ../../spec/harness/effect.bend as Sp
import ./base.bend as LA

def gm.no(d: Wr.Dec<Tc.Gate>, no: {ToolCall.tc_rg.whole(d) == None{} : Maybe<&2, Tc.Gate>}) -> {FTc.ffi.gate(d) == SCon{'E', SCon{' ', "tool_call: malformed gate"}} : String}:
  match d:
    case Wr.Got{x, rest}:
      match rest:
        case SNil{}:
          LA.tp.none_some(Tc.Gate, {FTc.ffi.end(True{}, x) == SCon{'E', SCon{' ', "tool_call: malformed gate"}} : String}, x, Equal.sym(Maybe<&2, Tc.Gate>, Some{x}, None{}, no))
        case SCon{h, t}:
          {==}
    case Wr.Bad{}:
      {==}

def ToolCall.tool_call_gate_malformed_exact(i, no):
  %LA.ep.read(Wr.get_nat(i)) : {FTc.ffi.gate(_) == SCon{'E', SCon{' ', "tool_call: malformed gate"}} : String}
  gm.no(ToolCall.tc_rg.go(Wr.get_nat(i)), no)
