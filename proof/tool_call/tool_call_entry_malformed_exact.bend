# eukhe: the proof of LAW tool_call_entry_malformed_exact
# The entry reads every input as the laws' reader does (LA.tp.read);
# where that reader finds no whole event, the entry keeps the call and
# answers its error form.

import Base
import ../../bend/tool_call.bend as Tc
import ../../bend/ffi_tool_call.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/tool_call.bend as ToolCall
import ./base.bend as LA

def tm.no(+c: Tc.C, d: Wr.Dec<Tc.Ev>, no: {ToolCall.tc_read.whole(d) == None{} : Maybe<&2, Tc.Ev>}) -> {FTc.step.ev(c, d) == (FTc.Call{c}, SCon{'E', SCon{' ', "tool_call: malformed event"}}) : FTc.St & String}:
  match d:
    case Wr.Got{x, rest}:
      match rest:
        case SNil{}:
          LA.tp.none_some(Tc.Ev, {FTc.step.end(True{}, c, x) == (FTc.Call{c}, SCon{'E', SCon{' ', "tool_call: malformed event"}}) : FTc.St & String}, x, Equal.sym(Maybe<&2, Tc.Ev>, Some{x}, None{}, no))
        case SCon{h, t}:
          {==}
    case Wr.Bad{}:
      {==}

def ToolCall.tool_call_entry_malformed_exact(c, i, no):
  %LA.tp.read(Wr.get_nat(i)) : {FTc.step.ev(c, _) == (FTc.Call{c}, SCon{'E', SCon{' ', "tool_call: malformed event"}}) : FTc.St & String}
  tm.no(c, ToolCall.tc_read.go(Wr.get_nat(i)), no)
