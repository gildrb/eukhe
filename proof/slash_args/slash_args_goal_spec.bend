# eukhe: the proof of LAW slash_args_goal_spec
#
# PROOF: the trimmed text is the spec's (sab.trim), then each stage of the answer is (sab.kw: keywords, sab.start: the first piece, sab.flag, sab.spaced, sab.budget, sab.objective).

import Base
import ../../bend/slash_args.bend as Sa
import ../../laws/slash_args/model.bend as SlashArgs
import ./base/text.bend as LT

def SlashArgs.slash_args_goal_spec(s):
  LT.sab.goal(s)
