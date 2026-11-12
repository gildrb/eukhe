# eukhe: the proof of LAW once_never_takes_hold_twice
#
# PROOF: the invariant LW.oa.inv holds of the first world and after every
# event (LW.oa.run); a world it holds of took hold at most once
# (LW.oa.outw).

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once
import ../../spec/once/life.bend as S
import ./base.bend as LA
import ./base/world_hold.bend as LW

def Once.once_never_takes_hold_twice(es):
  LA.ob.mp(LW.oa.inv(Once.wd_run(es, S.w0(), O.Never{})), Nat.is_le(S.lands(Once.wd_run(es, S.w0(), O.Never{})), 1n), LW.oa.run(es, S.w0(), {==}), LW.oa.outw(Once.wd_run(es, S.w0(), O.Never{})))
