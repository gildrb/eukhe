# eukhe: the proof of LAW codemode_models_describe_exact

import Base
import ../../bend/codemode_models.bend as Mod
import ../../laws/codemode_models/checks.bend as CodemodeModels
import ./base.bend as LACm

# PROOF of LAW codemode_models_describe_exact: each kind computes; an object's keys are the spec's first six joined, then `...` (cm.desc).

def CodemodeModels.codemode_models_describe_exact(d):
  LACm.cm.desc(d)
