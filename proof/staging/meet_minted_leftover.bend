# eukhe: the proof of LAW meet_minted_leftover

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA

def Staging.meet_minted_leftover(t, l, id, m, full, u):
  +e = {Sg.Seen{Sg.Utf{Staging.sp_mint(t, l, id)}, Sg.KDir{m}} : Sg.Seen}
  %Equal.sym(Sg.Met, Sg.met(e, [e]), LA.rr.m(e, [e]), LA.rr.met(e, [e])) : {[_] == [Sg.MLeftover{}] : List<&2, Sg.Met>}
  %Equal.sym(Bool, LA.sp_swept(Staging.sp_mint(t, l, id)), True{}, LA.rr.minted(t, l, id, full, u)) : {[LA.rr.m.dir(_, m)] == [Sg.MLeftover{}] : List<&2, Sg.Met>}
  {==}
