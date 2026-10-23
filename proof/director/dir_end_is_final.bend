# eukhe: the proof of LAW dir_end_is_final

import Base
import ../../bend/director.bend as Dr
import ../../laws/director.bend as Director
import ../base/bool/misc.bend as LBoolMisc

def pd.dir_end_is_final(+cap: Nat, +l: Dr.Loop, done: {Dr.ended(l) == True{} : Bool}, vs: List<&2, Dr.Verdict>) -> {Dr.tick(cap, l, vs) == l : Dr.Loop}:
  match l:
    case Dr.Loop{n, s, e}:
      match e:
        case None{}:
          LBoolMisc.tree.pt.absurdF({Dr.tick(cap, Dr.Loop{n, s, None{}}, vs) == Dr.Loop{n, s, None{}} : Dr.Loop}, done)
        case Some{x}:
          {==}

def Director.dir_end_is_final(cap, l, done, vs):
  pd.dir_end_is_final(cap, l, done, vs)
