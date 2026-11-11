# eukhe: the proof of LAW fallback_session_history
#
# PROOF: a session of ps then x is the events of ps, then x's events with
# the keys shown after ps (afh.go_app); a key is shown after ps exactly
# when a pass of ps fell back with it (afh.aft_listed), so x's events are
# the spec's (afh.last).

import Base
import ../../bend/aux_fallback.bend as Af
import ../../laws/aux_fallback/model.bend as AuxFallback
import ./base/session.bend as LS

def AuxFallback.fallback_session_history(ps, x):
  ({==}, Equal.trans(List<&2, Af.Ev>, Af.go(List.append(&2, Af.Pass, ps, [x]), Nil{}), List.append(&2, Af.Ev, Af.go(ps, Nil{}), Af.go([x], LS.afh.aft(ps, Nil{}))), List.append(&2, Af.Ev, Af.run(ps), AuxFallback.afh_events(Af.decide(x), AuxFallback.afh_fallen(ps))), LS.afh.go_app(ps, [x], Nil{}), Equal.cong(List<&2, Af.Ev>, List<&2, Af.Ev>, z => List.append(&2, Af.Ev, Af.run(ps), z), Af.go([x], LS.afh.aft(ps, Nil{})), AuxFallback.afh_events(Af.decide(x), AuxFallback.afh_fallen(ps)), LS.afh.last(Af.decide(x), ps))))
