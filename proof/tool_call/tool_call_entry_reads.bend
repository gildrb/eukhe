# eukhe: the proof of LAW tool_call_entry_reads
# The entry reads every input as the laws' reader does (LA.tp.read); a
# whole event runs as the same event spelled (LA.tp.spelled).

import Base
import ../../bend/tool_call.bend as Tc
import ../../bend/ffi_tool_call.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/tool_call.bend as ToolCall
import ./base.bend as LA

def tr.got(+c: Tc.C, d: Wr.Dec<Tc.Ev>, +e: Tc.Ev, got: {ToolCall.tc_read.whole(d) == Some{e} : Maybe<&2, Tc.Ev>}) -> {FTc.step.ev(c, d) == FTc.step(FTc.Call{c}, ToolCall.tc_spell(e)) : FTc.St & String}:
  match d:
    case Wr.Got{+x, rest}:
      match rest:
        case SNil{}:
          %LA.tp.some_inj(Tc.Ev, x, e, got) : {FTc.step.end(True{}, c, x) == FTc.step(FTc.Call{c}, ToolCall.tc_spell(_)) : FTc.St & String}
          LA.tp.spelled(c, x)
        case SCon{h, t}:
          LA.tp.none_some(Tc.Ev, {FTc.step.end(False{}, c, x) == FTc.step(FTc.Call{c}, ToolCall.tc_spell(e)) : FTc.St & String}, e, got)
    case Wr.Bad{}:
      LA.tp.none_some(Tc.Ev, {(FTc.Call{c}, FTc.fail()) == FTc.step(FTc.Call{c}, ToolCall.tc_spell(e)) : FTc.St & String}, e, got)

def ToolCall.tool_call_entry_reads(c, i, e, got):
  %LA.tp.read(Wr.get_nat(i)) : {FTc.step.ev(c, _) == FTc.step(FTc.Call{c}, ToolCall.tc_spell(e)) : FTc.St & String}
  tr.got(c, ToolCall.tc_read.go(Wr.get_nat(i)), e, got)
