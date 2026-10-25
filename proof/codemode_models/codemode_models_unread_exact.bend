# eukhe: the proof of LAW codemode_models_unread_exact

import Base
import ../../bend/codemode_models.bend as Mod
import ../../laws/codemode_models/checks.bend as CodemodeModels
import ./base.bend as LACm

# PROOF of LAW codemode_models_unread_exact: each call computes.

def CodemodeModels.codemode_models_unread_exact(c, e):
  match c:
    case Mod.CClassify{}:
      {==}
    case Mod.CImages{}:
      {==}
