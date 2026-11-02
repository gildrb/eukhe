# eukhe: the proof of LAW runners_registry_spec
# Both registries compute, for each value of chat.

import Base
import ../../bend/runners.bend as Ru
import ../../laws/runners.bend as Runners

def Runners.runners_registry_spec(chat):
  match chat:
    case True{}:
      {==}
    case False{}:
      {==}
