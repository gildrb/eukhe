# eukhe: the proof of LAW once_ends_once
#
# PROOF: the invariant LW.on.inv holds of the first world and after every
# event, for every policy (LW.on.run); a world it holds of journaled at
# most one end (LW.on.outw).

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once
import ../../spec/once/life.bend as S
import ./base.bend as LA
import ./base/world_ends.bend as LW

def Once.once_ends_once(p, es):
  LA.ob.mp(LW.on.inv(Once.wd_run(es, S.w0(), p)), Nat.is_le(S.ends(Once.wd_run(es, S.w0(), p)), 1n), LW.on.run(es, S.w0(), p, {==}), LW.on.outw(Once.wd_run(es, S.w0(), p)))
