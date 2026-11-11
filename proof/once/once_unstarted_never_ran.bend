# eukhe: the proof of LAW once_unstarted_never_ran
#
# PROOF: the invariant LW.ov.inv holds of the first world and after every
# event, for every policy (LW.ov.run); a world it holds of has an effect
# reported not started only when it never took hold (LW.ov.outw).

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once
import ../../spec/once/life.bend as S
import ./base.bend as LA
import ./base/world_void.bend as LW

def Once.once_unstarted_never_ran(p, es):
  LA.ob.mp(LW.ov.inv(Once.wd_run(es, S.w0(), p)), Bool.or(Bool.not(S.is_void(S.life(Once.wd_run(es, S.w0(), p)))), Nat.is_eq(S.lands(Once.wd_run(es, S.w0(), p)), 0n)), LW.ov.run(es, S.w0(), p, {==}), LW.ov.outw(Once.wd_run(es, S.w0(), p)))
