# eukhe: the proof of LAW undo_refusal_keeps_state
#
# PROOF: by cases on the live turns: none, the model computes both sides;
# some, the model answers a restore, so the premise (a refusal) is absurd.

import Base
import ../../bend/undo.bend as U
import ../../laws/undo.bend as Undo

# G when the answer is a refusal, Unit for every other answer
def urk.IfRefused(a: U.Act, G: Type) -> Type:
  match a:
    case U.Took{}:
      Unit
    case U.Restore{t}:
      Unit
    case U.Refused{}:
      G
    case U.Compare{t}:
      Unit
    case U.NoSnapshot{}:
      Unit

def Undo.undo_refusal_keeps_state(st, r):
  match st:
    case U.St{live, b}:
      match live:
        case Nil{}:
          {==}
        case Con{t, rest}:
          %r : urk.IfRefused(_, {Undo.sp_state(U.step(U.St{t <> rest, b}, U.Undo{})) == U.St{t <> rest, b} : U.St})
          Unit{}
