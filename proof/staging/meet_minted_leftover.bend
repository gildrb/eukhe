# eukhe: the proof of LAW meet_minted_leftover

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA
import ./meet_exact.bend as PMeetExact

def Staging.meet_minted_leftover(t, l, id, m, full, u):
  +e = {Sg.Seen{Sg.Utf{Staging.sp_mint(t, l, id)}, Sg.KDir{m}} : Sg.Seen}
  %Equal.sym(List<&2, Sg.Met>, Sg.meet([e]), Staging.sp_meet([e]), Staging.meet_exact([e])) : {_ == [Sg.MLeftover{}] : List<&2, Sg.Met>}
  %Equal.sym(Bool, Staging.sp_swept(Staging.sp_mint(t, l, id)), True{}, LA.rr.minted(t, l, id, full, u)) : {[Staging.sp_met.dir(_, m)] == [Sg.MLeftover{}] : List<&2, Sg.Met>}
  {==}
