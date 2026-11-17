# eukhe: the proof of LAW slash_args_entry_alias
#
# PROOF: both requests are answered with their spelled reply
# (slash_args_entry_answers), and the two spelled replies are the same.

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/ffi_slash_args.bend as FSa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/slash_args/entry.bend as SlashArgsEntry
import ./slash_args_entry_answers.bend as PSlashArgsEntryAnswers

def SlashArgsEntry.slash_args_entry_alias(a, fit):
  Equal.trans(String, FSa.ffi(SlashArgsEntry.sae_req(FSa.QAutonomous{a}, "")), SlashArgsEntry.sae_reply(FSa.QAuto{a}), FSa.ffi(SlashArgsEntry.sae_req(FSa.QAuto{a}, "")), SlashArgsEntry.slash_args_entry_answers(FSa.QAutonomous{a}, fit), Equal.sym(String, FSa.ffi(SlashArgsEntry.sae_req(FSa.QAuto{a}, "")), SlashArgsEntry.sae_reply(FSa.QAuto{a}), SlashArgsEntry.slash_args_entry_answers(FSa.QAuto{a}, fit)))
