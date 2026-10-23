# eukhe: the proof of LAW orphan_wire_reply

import Base
import ../../bend/orphan.bend as Or
import ../../LAWS.bend as Laws

def Laws.orphan_wire_reply(d, e, rest):
  match d e:
    case True{} Or.Shut{}:
      {==}
    case True{} Or.Handover{}:
      {==}
    case False{} Or.Shut{}:
      {==}
    case False{} Or.Handover{}:
      {==}
