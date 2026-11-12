# eukhe: the proof of LAW fallback_event_keys
#
# PROOF: subs and notes of joined lists by induction on the first
# (afh.subs_app, afh.notes_app); the one-event lists compute.

import Base
import ../../bend/aux_fallback.bend as Af
import ../../laws/aux_fallback/model.bend as AuxFallback
import ./base/session.bend as LS

def AuxFallback.fallback_event_keys(es, fs, k):
  (LS.afh.subs_app(es, fs), (LS.afh.notes_app(es, fs), {==}))
