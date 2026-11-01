# eukhe: the proof of LAW stop_plain_stands
#
# PROOF: the walk is the spec's (LA.stb.walk); a reply that announces nothing stands, asked or not.

import Base
import ../../bend/stop.bend as S
import ../../spec/harness/stop.bend as StSpec
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def plain.ann(a: Bool) -> {StSpec.announced(a, False{}) == S.Stands{} : S.Pick}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def Stop.stop_plain_stands(p, s, plain):
  match p:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(S.Pick, S.walk(S.Facts{False{}, True{}, False{}, False{}, s}), StSpec.pick(S.Facts{False{}, True{}, False{}, False{}, s}), LA.stb.walk(S.Facts{False{}, True{}, False{}, False{}, s})) : {_ == S.Stands{} : S.Pick}
      %Equal.sym(Bool, StSpec.promises(s), False{}, plain) : {StSpec.announced(StSpec.asks(s), _) == S.Stands{} : S.Pick}
      plain.ann(StSpec.asks(s))
