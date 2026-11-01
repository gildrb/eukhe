# eukhe: the proof of LAW stop_promise_continues
#
# PROOF: the walk is the spec's (LA.stb.walk); the spec's reply that announces a step and asks nothing goes on with UnexpectedStop.

import Base
import ../../bend/stop.bend as S
import ../../spec/harness/stop.bend as StSpec
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def Stop.stop_promise_continues(s, said, asked):
  %Equal.sym(S.Pick, S.walk(S.Facts{False{}, True{}, False{}, False{}, s}), StSpec.pick(S.Facts{False{}, True{}, False{}, False{}, s}), LA.stb.walk(S.Facts{False{}, True{}, False{}, False{}, s})) : {_ == S.Goes{S.UnexpectedStop{}} : S.Pick}
  %Equal.sym(Bool, StSpec.asks(s), False{}, asked) : {StSpec.announced(_, StSpec.promises(s)) == S.Goes{S.UnexpectedStop{}} : S.Pick}
  %Equal.sym(Bool, StSpec.promises(s), True{}, said) : {StSpec.announced(False{}, _) == S.Goes{S.UnexpectedStop{}} : S.Pick}
  {==}
