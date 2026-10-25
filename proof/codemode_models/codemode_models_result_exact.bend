# eukhe: the proof of LAW codemode_models_result_exact

import Base
import ../../bend/codemode_models.bend as Mod
import ../../laws/codemode_models/checks.bend as CodemodeModels
import ./base/calls.bend as LACmCalls

# PROOF of LAW codemode_models_result_exact: the stop test, the call and the error message, case by case (cm.result).

def CodemodeModels.codemode_models_result_exact(c, p, i, stop, e):
  LACmCalls.cm.result(String.eq(stop, "stop"), c, p, i, stop, e)
