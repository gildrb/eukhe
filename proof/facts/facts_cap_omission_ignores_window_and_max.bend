# eukhe: the proof of LAW facts_cap_omission_ignores_window_and_max

import Base
import ../../laws/facts/model.bend as Facts

def Facts.facts_cap_omission_ignores_window_and_max(caller, needs, mm1, win1, mm2, win2):
  match caller needs:
    case Some{x} True{}:
      {==}
    case Some{x} False{}:
      {==}
    case None{} True{}:
      {==}
    case None{} False{}:
      {==}
