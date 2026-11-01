# eukhe: the proof of LAW stop_asked_stands
#
# PROOF: the walk is the spec's (LA.stb.walk); with work pending it stands, else the spec's asked reply stands.

import Base
import ../../bend/stop.bend as S
import ../../spec/harness/stop.bend as StSpec
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def Stop.stop_asked_stands(p, s, asked):
  match p:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(S.Pick, S.walk(S.Facts{False{}, True{}, False{}, False{}, s}), StSpec.pick(S.Facts{False{}, True{}, False{}, False{}, s}), LA.stb.walk(S.Facts{False{}, True{}, False{}, False{}, s})) : {_ == S.Stands{} : S.Pick}
      %Equal.sym(Bool, StSpec.asks(s), True{}, asked) : {StSpec.announced(_, StSpec.promises(s)) == S.Stands{} : S.Pick}
      {==}
