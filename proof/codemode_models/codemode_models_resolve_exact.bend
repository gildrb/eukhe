# eukhe: the proof of LAW codemode_models_resolve_exact

import Base
import ../../bend/codemode_models.bend as Mod
import ../../laws/codemode_models/checks.bend as CodemodeModels
import ./base/calls.bend as LACmCalls

# PROOF of LAW codemode_models_resolve_exact: by the call: the default test (cm.resolve), the named model (cm.named), the type found (cm.found) and the other types in order (cm.other).

def CodemodeModels.codemode_models_resolve_exact(x):
  match x:
    case Mod.Res{c, d, model, provider, id, chat, image, classifier}:
      LACmCalls.cm.resolve(c, d, model, provider, id, chat, image, classifier)
