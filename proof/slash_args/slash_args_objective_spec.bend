# eukhe: the proof of LAW slash_args_objective_spec
#
# PROOF: the trimmed objective is the spec's (sab.trim), then the verdict is (sab.objective.at).

import Base
import ../../bend/slash_args.bend as Sa
import ../../laws/slash_args/model.bend as SlashArgs
import ./base/text.bend as LT

def SlashArgs.slash_args_objective_spec(s, b):
  LT.sab.objective(s, b)
