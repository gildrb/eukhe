# eukhe: the proof of LAW once_life_step_is_spec
#
# PROOF: the spec's life of j is the model's (once_life_is_spec), and so
# is the spec's life of j with r after it; the model's life of j with r
# after it is one step from the model's life of j (LA.ob.go_snoc).

import Base
import ../../bend/once.bend as O
import ../../spec/once/life.bend as S
import ../../laws/once.bend as Once
import ./base.bend as LA

def Once.once_life_step_is_spec(j, r):
  %Once.once_life_is_spec(j) : {O.life.step(_, r) == S.life_spec(List.append(&2, O.Rec, j, [r])) : O.Life}
  %Once.once_life_is_spec(List.append(&2, O.Rec, j, [r])) : {O.life.step(O.life(j), r) == _ : O.Life}
  Equal.sym(O.Life, O.life(List.append(&2, O.Rec, j, [r])), O.life.step(O.life(j), r), LA.ob.go_snoc(j, r))
