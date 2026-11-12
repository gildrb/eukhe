# eukhe: the proof of LAW once_keyed_sends_capped
#
# PROOF: the invariant LW.oc.inv holds of the first world and after every
# event of a history in which the world is never asked (LW.oc.run); a
# world it holds of made at most 1 + cap launches (LW.oc.outw).

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once
import ../../spec/once/life.bend as S
import ./base.bend as LA
import ./base/world_sends.bend as LW

def Once.once_keyed_sends_capped(cap, es):
  LA.ob.mp(LW.oc.inv(cap, Once.wd_run(S.dim(es), S.w0(), O.Keyed{cap})), Nat.is_le(S.launches(Once.wd_run(S.dim(es), S.w0(), O.Keyed{cap})), 1n+cap), LW.oc.run(es, S.w0(), cap, {==}), LW.oc.outw(cap, Once.wd_run(S.dim(es), S.w0(), O.Keyed{cap})))
