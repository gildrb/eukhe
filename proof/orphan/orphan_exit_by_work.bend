# eukhe: the proof of LAW orphan_exit_by_work

import Base
import ../../bend/orphan.bend as Or
import ../../LAWS.bend as Laws

def Laws.orphan_exit_by_work(work):
  match work:
    case Or.Idle{}:
      {==}
    case Or.Ongoing{}:
      {==}
