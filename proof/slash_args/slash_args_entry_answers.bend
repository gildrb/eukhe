# eukhe: the proof of LAW slash_args_entry_answers
#
# PROOF: each request's text reads back whole with nothing left
# (wire_str_round_trip), so the entry answers the model's answer, spelled
# by encoders that are the spec spellers (sae.auto; words:
# wire_strs_spells).

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/ffi_slash_args.bend as FSa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/slash_args/entry.bend as SlashArgsEntry
import ../base/wire.bend as LWire
import ../wire/wire_strs_spells.bend as PWireStrsSpells
import ./base/entry.bend as LE

def SlashArgsEntry.slash_args_entry_answers(q, fit):
  match q:
    case FSa.QGoal{+a}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, "")), Wr.Got{a, ""}, Wire.wire_str_round_trip(a, "", fit)) : {FSa.ffi.got(FSa.get_goal(_)) == SlashArgsEntry.sae_reply(FSa.QGoal{a}) : String}
      %Equal.sym(String, FSa.put_auto(Sa.goal(a)), SlashArgsEntry.sae_auto(Sa.goal(a)), LE.sae.auto(Sa.goal(a))) : {Wr.put_nat(1n, _) == Wr.put_nat(1n, SlashArgsEntry.sae_auto(Sa.goal(a))) : String}
      {==}
    case FSa.QAuto{+a}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, "")), Wr.Got{a, ""}, Wire.wire_str_round_trip(a, "", fit)) : {FSa.ffi.got(FSa.get_auto(_)) == SlashArgsEntry.sae_reply(FSa.QAuto{a}) : String}
      %Equal.sym(String, FSa.put_auto(Sa.auto(a)), SlashArgsEntry.sae_auto(Sa.auto(a)), LE.sae.auto(Sa.auto(a))) : {Wr.put_nat(0n, _) == Wr.put_nat(0n, SlashArgsEntry.sae_auto(Sa.auto(a))) : String}
      {==}
    case FSa.QWords{+a}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, "")), Wr.Got{a, ""}, Wire.wire_str_round_trip(a, "", fit)) : {FSa.ffi.got(FSa.get_words(_)) == SlashArgsEntry.sae_reply(FSa.QWords{a}) : String}
      Wire.wire_strs_spells(Sa.words(a), "")
    case FSa.QObjective{+a}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, "")), Wr.Got{a, ""}, Wire.wire_str_round_trip(a, "", fit)) : {FSa.ffi.got(FSa.get_objective(_)) == SlashArgsEntry.sae_reply(FSa.QObjective{a}) : String}
      LE.sae.auto(Sa.goal.objective(a, None{}))
    case FSa.QAutonomous{+a}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, "")), Wr.Got{a, ""}, Wire.wire_str_round_trip(a, "", fit)) : {FSa.ffi.got(FSa.get_autonomous(_)) == SlashArgsEntry.sae_reply(FSa.QAutonomous{a}) : String}
      %Equal.sym(String, FSa.put_auto(Sa.auto(a)), SlashArgsEntry.sae_auto(Sa.auto(a)), LE.sae.auto(Sa.auto(a))) : {Wr.put_nat(0n, _) == Wr.put_nat(0n, SlashArgsEntry.sae_auto(Sa.auto(a))) : String}
      {==}
