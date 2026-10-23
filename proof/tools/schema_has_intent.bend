# eukhe: the proof of LAW schema_has_intent

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA

def pl.schema_has_intent(s: Tl.Schema) -> {Tl.elem(Tl.Schema.params(Tl.build(s)), Tl.intent()) == True{} : Bool}:
  match s:
    case Tl.Schema{+ps, v}:
      LA.pl.add_has(Tl.elem(ps, Tl.intent()), ps, {==})

def Tools.schema_has_intent(s):
  pl.schema_has_intent(s)
