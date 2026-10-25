# eukhe: the proof of LAW codemode_models_catalog_exact

import Base
import ../../bend/codemode_models.bend as Mod
import ../../laws/codemode_models/checks.bend as CodemodeModels
import ./base/calls.bend as LACmCalls

# PROOF of LAW codemode_models_catalog_exact: by the global's name: the listing calls (cm.list) and getModelOfType (cm.get) are the spec's (cm.catalog_go).

def CodemodeModels.codemode_models_catalog_exact(x):
  match x:
    case Mod.Cat{+name, args, kind, json}:
      LACmCalls.cm.catalog_go(String.eq(name, "models.getModelsOfType"), String.eq(name, "models.getAvailableOfType"), args, json, kind)
