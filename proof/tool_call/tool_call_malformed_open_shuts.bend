# eukhe: the proof of LAW tool_call_malformed_open_shuts
# An open answered with the error form opened the refused state (a whole
# Bool answers its record, no error form); the refused state answers
# every input with the refusal and stays refused (by induction).

import Base
import ../../bend/tool_call.bend as Tc
import ../../bend/ffi_tool_call.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/tool_call.bend as ToolCall
import ./base.bend as LA

def tms.fin(r: String, b: Bool, bad: {String.eq(ToolCall.tc_reply(FTc.open.end(Wr.end(r), b)), ToolCall.tc_bad_open()) == True{} : Bool}) -> {ToolCall.tc_state(FTc.open.end(Wr.end(r), b)) == FTc.Refused{} : FTc.St}:
  match r:
    case SNil{}:
      match b:
        case True{}:
          LA.tp.no({ToolCall.tc_state(FTc.open.end(True{}, True{})) == FTc.Refused{} : FTc.St}, bad)
        case False{}:
          LA.tp.no({ToolCall.tc_state(FTc.open.end(True{}, False{})) == FTc.Refused{} : FTc.St}, bad)
    case SCon{x, y}:
      {==}

def tms.main(d: Wr.Dec<Bool>, bad: {String.eq(ToolCall.tc_reply(FTc.open.first(d)), ToolCall.tc_bad_open()) == True{} : Bool}) -> {ToolCall.tc_state(FTc.open.first(d)) == FTc.Refused{} : FTc.St}:
  match d:
    case Wr.Got{b, r}:
      tms.fin(r, b, bad)
    case Wr.Bad{}:
      {==}

# the refused state refuses every input
def tms.shut(xs: List<&2, String>) -> {ToolCall.tc_raw_replies(xs, FTc.Refused{}) == ToolCall.tc_refusals(xs) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.cong(List<&2, String>, List<&2, String>, z => ToolCall.tc_refused() <> z, ToolCall.tc_raw_replies(rest, FTc.Refused{}), ToolCall.tc_refusals(rest), tms.shut(rest))

def ToolCall.tool_call_malformed_open_shuts(i, xs, bad):
  %Equal.sym(FTc.St, ToolCall.tc_state(FTc.open(i)), FTc.Refused{}, tms.main(Wr.get_bool(i), bad)) : {ToolCall.tc_raw_replies(xs, _) == ToolCall.tc_refusals(xs) : List<&2, String>}
  tms.shut(xs)
