# eukhe: the proof of LAW once_done_ran
#
# PROOF: the invariant LW.od.inv holds of the first world and after every
# event, for every policy (LW.od.run); a world it holds of has a finished
# effect only when it took hold (LW.od.outw).

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once
import ../../spec/once/life.bend as S
import ./base.bend as LA
import ./base/world_done.bend as LW

def Once.once_done_ran(p, es):
  LA.ob.mp(LW.od.inv(Once.wd_run(es, S.w0(), p)), Bool.or(Bool.not(S.is_ran(S.life(Once.wd_run(es, S.w0(), p)))), Nat.is_le(1n, S.lands(Once.wd_run(es, S.w0(), p)))), LW.od.run(es, S.w0(), p, {==}), LW.od.outw(Once.wd_run(es, S.w0(), p)))
