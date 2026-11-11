# eukhe: the proof of LAW once_ended_never_launches
#
# PROOF: the invariant LW.ot.inv holds of the first world and after every
# event, for every policy (LW.ot.run); a world it holds of made no launch
# of an ended effect (LW.ot.outw), and a number is_eq says is 0 is 0
# (LA.ob.eq_zero).

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once
import ../../spec/once/life.bend as S
import ./base.bend as LA
import ./base/world_late.bend as LW

def Once.once_ended_never_launches(p, es):
  LA.ob.eq_zero(S.late(Once.wd_run(es, S.w0(), p)), LA.ob.mp(LW.ot.inv(Once.wd_run(es, S.w0(), p)), Nat.is_eq(S.late(Once.wd_run(es, S.w0(), p)), 0n), LW.ot.run(es, S.w0(), p, {==}), LW.ot.outw(Once.wd_run(es, S.w0(), p))))
