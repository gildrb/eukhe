# eukhe: the proof of LAW tool_call_entry_open_malformed_exact
# Where the laws' reader finds no whole Bool, neither does the entry: it
# opens the refused state with its error form.

import Base
import ../../bend/ffi_tool_call.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/tool_call.bend as ToolCall
import ./base.bend as LA

def tom.no(d: Wr.Dec<Bool>, no: {ToolCall.tc_read_open.whole(d) == None{} : Maybe<&2, Bool>}) -> {FTc.open.first(d) == (FTc.Refused{}, SCon{'E', SCon{' ', "tool_call: malformed open"}}) : FTc.St & String}:
  match d:
    case Wr.Got{f, rest}:
      match rest:
        case SNil{}:
          LA.tp.none_some(Bool, {FTc.open.end(True{}, f) == (FTc.Refused{}, SCon{'E', SCon{' ', "tool_call: malformed open"}}) : FTc.St & String}, f, Equal.sym(Maybe<&2, Bool>, Some{f}, None{}, no))
        case SCon{h, t}:
          {==}
    case Wr.Bad{}:
      {==}

def ToolCall.tool_call_entry_open_malformed_exact(i, no):
  tom.no(Wr.get_bool(i), no)
