# eukhe: the proof of LAW facts_cap_omits_only_the_default

import Base
import ../../laws/facts/model.bend as Facts

def Facts.facts_cap_omits_only_the_default(caller, mm, win):
  match caller:
    case Some{x}:
      {==}
    case None{}:
      {==}
