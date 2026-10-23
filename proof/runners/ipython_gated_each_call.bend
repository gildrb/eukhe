# eukhe: the proof of LAW ipython_gated_each_call

import Base
import ../../bend/runners.bend as Ru
import ../../LAWS.bend as Laws

def pr.ipython(chat: Bool) -> {Ru.find(Ru.registry(chat), "ipython") == Some{Ru.Tool{"ipython", [Ru.exec()], Ru.EachCall{}}} : Maybe<&2, Ru.Tool>}:
  match chat:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.ipython_gated_each_call(chat):
  pr.ipython(chat)
