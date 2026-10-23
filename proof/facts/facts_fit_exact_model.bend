# eukhe: the proof of LAW facts_fit_exact_model

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.facts_fit_exact_model(mm, b, a):
  LA.w2.fit_at(Nat.is_le(mm, b), mm, b, a)
