# eukhe: the proof of LAW slash_args_entry_goal_pointer
#
# PROOF: the `/goal` request is answered with its spelled reply
# (slash_args_entry_answers), which is the pointer.

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/ffi_slash_args.bend as FSa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/slash_args/entry.bend as SlashArgsEntry
import ./slash_args_entry_answers.bend as PSlashArgsEntryAnswers

def SlashArgsEntry.slash_args_entry_goal_pointer(a, fit):
  SlashArgsEntry.slash_args_entry_answers(FSa.QGoal{a}, fit)
