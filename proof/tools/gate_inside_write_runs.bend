# eukhe: the proof of LAW gate_inside_write_runs

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools

def pp.gate_inside_write_runs(+auto: List<&2, Nat>, +ans: Pp.Ans, w: {Tl.elem(auto, 1n) == True{} : Bool}) -> {Pp.runs(Pp.Inside{}, Pp.Wr{}, auto, ans) == True{} : Bool}:
  %Equal.sym(Bool, Tl.elem(auto, 1n), True{}, w) : {Bool.or(_, Pp.Ans.yes(ans)) == True{} : Bool}
  {==}

def Tools.gate_inside_write_runs(auto, ans, w):
  pp.gate_inside_write_runs(auto, ans, w)
