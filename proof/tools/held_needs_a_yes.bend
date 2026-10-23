# eukhe: the proof of LAW held_needs_a_yes

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools

# a denied step runs nothing and names itself
def ps.gate_den(s: Tl.Step, r: Tl.Ran) -> {Tl.gate(False{}, s, r) == Tl.Ran{Nil{}, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}:
  match s:
    case Tl.Step{i, e}:
      {==}

def ps.held_needs_a_yes(+s: Tl.Step, +post: List<&2, Tl.Step>, +auto: List<&2, Nat>, w: {Tl.within(Tl.Step.effs(s), auto) == False{} : Bool}) -> {Tl.exec(s <> post, auto, Nil{}) == Tl.Ran{Nil{}, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}:
  %Equal.sym(Bool, Tl.within(Tl.Step.effs(s), auto), False{}, w) : {Tl.exec.go(s <> post, auto, _, Nil{}) == Tl.Ran{Nil{}, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}
  ps.gate_den(s, Tl.Ran{Nil{}, Tl.Finished{}})

def Tools.held_needs_a_yes(s, post, auto, w):
  ps.held_needs_a_yes(s, post, auto, w)
