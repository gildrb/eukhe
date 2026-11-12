# eukhe: the proof of LAW fallback_notice_once
#
# PROOF: by induction on the passes, a session's notices hold no key twice
# and none of the keys shown before it (afh.inv): a pass notices only a
# key not shown, which joins the shown keys for the passes after it.

import Base
import ../../bend/aux_fallback.bend as Af
import ../../laws/aux_fallback/model.bend as AuxFallback
import ../base/logic/bool.bend as LLogicBool
import ./base/session.bend as LS

def AuxFallback.fallback_notice_once(ps):
  LLogicBool.ppr.and_l(AuxFallback.afh_nodup(Af.notes(Af.run(ps))), LS.afh.disj(Af.notes(Af.run(ps)), Nil{}), LS.afh.inv(ps, Nil{}))
