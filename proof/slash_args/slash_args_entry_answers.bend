# eukhe: the proof of LAW slash_args_entry_answers
#
# PROOF: each request's text reads back whole with nothing left (wire_str_round_trip), so the entry answers the model's answer, the spec's (the model laws), spelled by encoders that are the spec spellers (sae.goal, sae.auto; words: wire_strs_spells).

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/ffi_slash_args.bend as FSa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/slash_args/model.bend as SlashArgs
import ../../laws/slash_args/entry.bend as SlashArgsEntry
import ../base/wire.bend as LWire
import ../wire/wire_strs_spells.bend as PWireStrsSpells
import ./base/entry.bend as LE
import ./slash_args_goal_spec.bend as PSlashArgsGoalSpec
import ./slash_args_auto_spec.bend as PSlashArgsAutoSpec
import ./slash_args_words_spec.bend as PSlashArgsWordsSpec
import ./slash_args_objective_spec.bend as PSlashArgsObjectiveSpec

def SlashArgsEntry.slash_args_entry_answers(q, fit):
  match q:
    case FSa.QGoal{+a}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, "")), Wr.Got{a, ""}, Wire.wire_str_round_trip(a, "", fit)) : {FSa.ffi.got(FSa.get_goal(_)) == SlashArgsEntry.sae_reply(FSa.QGoal{a}) : String}
      %SlashArgs.slash_args_goal_spec(a) : {FSa.put_goal(Sa.goal(a)) == SlashArgsEntry.sae_goal(_) : String}
      LE.sae.goal(Sa.goal(a))
    case FSa.QAuto{+a}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, "")), Wr.Got{a, ""}, Wire.wire_str_round_trip(a, "", fit)) : {FSa.ffi.got(FSa.get_auto(_)) == SlashArgsEntry.sae_reply(FSa.QAuto{a}) : String}
      %SlashArgs.slash_args_auto_spec(a) : {FSa.put_auto(Sa.auto(a)) == SlashArgsEntry.sae_auto(_) : String}
      LE.sae.auto(Sa.auto(a))
    case FSa.QWords{+a}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, "")), Wr.Got{a, ""}, Wire.wire_str_round_trip(a, "", fit)) : {FSa.ffi.got(FSa.get_words(_)) == SlashArgsEntry.sae_reply(FSa.QWords{a}) : String}
      %SlashArgs.slash_args_words_spec(a) : {Wr.put_list(~String, ~Wr.put_str, Sa.words(a), "") == LawsBase.wire_spell_strs(_, "") : String}
      Wire.wire_strs_spells(Sa.words(a), "")
    case FSa.QObjective{+a}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, "")), Wr.Got{a, ""}, Wire.wire_str_round_trip(a, "", fit)) : {FSa.ffi.got(FSa.get_objective(_)) == SlashArgsEntry.sae_reply(FSa.QObjective{a}) : String}
      %SlashArgs.slash_args_objective_spec(a, None{}) : {FSa.put_goal(Sa.goal.objective(a, None{})) == SlashArgsEntry.sae_goal(_) : String}
      LE.sae.goal(Sa.goal.objective(a, None{}))
