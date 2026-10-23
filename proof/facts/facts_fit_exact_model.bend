# eukhe: the proof of LAW facts_fit_exact_model

import Base
import ../../laws/facts.bend as Facts
import ./base.bend as LA

def Facts.facts_fit_exact_model(mm, b, a):
  LA.w2.fit_at(Nat.is_le(mm, b), mm, b, a)
