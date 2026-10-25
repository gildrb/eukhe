# eukhe: the proof of LAW codemode_models_tool_exact

import Base
import ../../bend/codemode_models.bend as Mod
import ../../laws/codemode_models/checks.bend as CodemodeModels
import ./base/calls.bend as LACmCalls

# PROOF of LAW codemode_models_tool_exact: both name tests, case by case (cm.tool_of).

def CodemodeModels.codemode_models_tool_exact(g):
  LACmCalls.cm.tool_of(String.eq(g, "models.classify"), String.eq(g, "models.generateImages"))
