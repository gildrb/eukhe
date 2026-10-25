# eukhe: the proof of LAW slash_args_entry_left_over
#
# PROOF: the text reads back with the rest untouched (wire_str_round_trip); the rest is not empty, so the entry answers the error form.

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/ffi_slash_args.bend as FSa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/slash_args/model.bend as SlashArgs
import ../../laws/slash_args/entry.bend as SlashArgsEntry
import ../base/wire.bend as LWire

def SlashArgsEntry.slash_args_entry_left_over(q, c, t, fit):
  match q:
    case FSa.QGoal{+a}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, SCon{c, t})), Wr.Got{a, SCon{c, t}}, Wire.wire_str_round_trip(a, SCon{c, t}, fit)) : {FSa.ffi.got(FSa.get_goal(_)) == Wr.err("slash_args: malformed request") : String}
      {==}
    case FSa.QAuto{+a}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, SCon{c, t})), Wr.Got{a, SCon{c, t}}, Wire.wire_str_round_trip(a, SCon{c, t}, fit)) : {FSa.ffi.got(FSa.get_auto(_)) == Wr.err("slash_args: malformed request") : String}
      {==}
    case FSa.QWords{+a}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, SCon{c, t})), Wr.Got{a, SCon{c, t}}, Wire.wire_str_round_trip(a, SCon{c, t}, fit)) : {FSa.ffi.got(FSa.get_words(_)) == Wr.err("slash_args: malformed request") : String}
      {==}
    case FSa.QObjective{+a}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, SCon{c, t})), Wr.Got{a, SCon{c, t}}, Wire.wire_str_round_trip(a, SCon{c, t}, fit)) : {FSa.ffi.got(FSa.get_objective(_)) == Wr.err("slash_args: malformed request") : String}
      {==}
