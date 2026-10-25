# eukhe: the proof of LAW tool_call_entry_open_reads
# The entry and the laws' reader read the open's Bool with the same wire
# decoder; a whole one opens as the same Bool spelled (LA.tp.open_spelled).

import Base
import ../../bend/ffi_tool_call.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/tool_call.bend as ToolCall
import ./base.bend as LA

def to.got(d: Wr.Dec<Bool>, +b: Bool, got: {ToolCall.tc_read_open.whole(d) == Some{b} : Maybe<&2, Bool>}) -> {FTc.open.first(d) == FTc.open(ToolCall.tc_spell_open(b)) : FTc.St & String}:
  match d:
    case Wr.Got{+f, rest}:
      match rest:
        case SNil{}:
          %LA.tp.some_inj(Bool, f, b, got) : {FTc.open.end(True{}, f) == FTc.open(ToolCall.tc_spell_open(_)) : FTc.St & String}
          LA.tp.open_spelled(f)
        case SCon{h, t}:
          LA.tp.none_some(Bool, {FTc.open.end(False{}, f) == FTc.open(ToolCall.tc_spell_open(b)) : FTc.St & String}, b, got)
    case Wr.Bad{}:
      LA.tp.none_some(Bool, {(FTc.Refused{}, Wr.err("tool_call: malformed open")) == FTc.open(ToolCall.tc_spell_open(b)) : FTc.St & String}, b, got)

def ToolCall.tool_call_entry_open_reads(i, b, got):
  to.got(Wr.get_bool(i), b, got)
