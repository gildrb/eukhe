# eukhe: the proof of LAW tool_call_entry_malformed_keeps
# Every path of the entry's step that answers the error form keeps the
# call; a whole event that ends a running call answers a settle, which is
# no error form.

import Base
import ../../bend/tool_call.bend as Tc
import ../../bend/ffi_tool_call.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/tool_call.bend as ToolCall
import ./base.bend as LA

# a whole event: only an end of a running call moves it, and its reply is
# a settle
def tmk.whole(c: Tc.C, e: Tc.Ev, bad: {String.eq(ToolCall.tc_reply(FTc.step.reply(Tc.step(c, e))), ToolCall.tc_bad_event()) == True{} : Bool}) -> {ToolCall.tc_state(FTc.step.reply(Tc.step(c, e))) == FTc.Call{c} : FTc.St}:
  match c:
    case Tc.Taking{}:
      match e:
        case Tc.Report{}:
          {==}
        case Tc.End{t, a}:
          match t a:
            case True{} True{}:
              LA.tp.no({ToolCall.tc_state(FTc.step.reply(Tc.step(Tc.Taking{}, Tc.End{True{}, True{}}))) == FTc.Call{Tc.Taking{}} : FTc.St}, bad)
            case True{} False{}:
              LA.tp.no({ToolCall.tc_state(FTc.step.reply(Tc.step(Tc.Taking{}, Tc.End{True{}, False{}}))) == FTc.Call{Tc.Taking{}} : FTc.St}, bad)
            case False{} True{}:
              LA.tp.no({ToolCall.tc_state(FTc.step.reply(Tc.step(Tc.Taking{}, Tc.End{False{}, True{}}))) == FTc.Call{Tc.Taking{}} : FTc.St}, bad)
            case False{} False{}:
              LA.tp.no({ToolCall.tc_state(FTc.step.reply(Tc.step(Tc.Taking{}, Tc.End{False{}, False{}}))) == FTc.Call{Tc.Taking{}} : FTc.St}, bad)
    case Tc.Ended{}:
      match e:
        case Tc.Report{}:
          {==}
        case Tc.End{t, a}:
          {==}

def tmk.fin(+c: Tc.C, e: Tc.Ev, r: String, bad: {String.eq(ToolCall.tc_reply(FTc.step.end(Wr.end(r), c, e)), ToolCall.tc_bad_event()) == True{} : Bool}) -> {ToolCall.tc_state(FTc.step.end(Wr.end(r), c, e)) == FTc.Call{c} : FTc.St}:
  match r:
    case SNil{}:
      tmk.whole(c, e, bad)
    case SCon{x, y}:
      {==}

def tmk.main(+c: Tc.C, d: Wr.Dec<Tc.Ev>, bad: {String.eq(ToolCall.tc_reply(FTc.step.ev(c, d)), ToolCall.tc_bad_event()) == True{} : Bool}) -> {ToolCall.tc_state(FTc.step.ev(c, d)) == FTc.Call{c} : FTc.St}:
  match d:
    case Wr.Got{e, r}:
      tmk.fin(c, e, r, bad)
    case Wr.Bad{}:
      {==}

def ToolCall.tool_call_entry_malformed_keeps(c, i, bad):
  tmk.main(c, FTc.get_ev(i), bad)
