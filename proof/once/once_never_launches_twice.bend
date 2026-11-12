# eukhe: the proof of LAW once_never_launches_twice
#
# PROOF: the invariant LW.ol.inv holds of the first world and after every
# event of a history in which the world is never asked (LW.ol.run); a
# world it holds of made at most one launch (LW.ol.outw).

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once
import ../../spec/once/life.bend as S
import ./base.bend as LA
import ./base/world_launch.bend as LW

def Once.once_never_launches_twice(es):
  LA.ob.mp(LW.ol.inv(Once.wd_run(S.dim(es), S.w0(), O.Never{})), Nat.is_le(S.launches(Once.wd_run(S.dim(es), S.w0(), O.Never{})), 1n), LW.ol.run(es, S.w0(), {==}), LW.ol.outw(Once.wd_run(S.dim(es), S.w0(), O.Never{})))
