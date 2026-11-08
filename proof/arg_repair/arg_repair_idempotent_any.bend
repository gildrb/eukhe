# eukhe: the proof of LAW arg_repair_idempotent_any
#
# PROOF: arg_repair_idempotent's induction (id.all) needs no well-formed
# dialect: every name a step reads is read as itself when sent again
# (sv.fix), since an alias's canonical name is admitted only as itself.

import Base
import ../../bend/arg_repair.bend as Ar
import ../../laws/arg_repair.bend as ArgRepair
import ./arg_repair_idempotent.bend as PIdempotent

def ArgRepair.arg_repair_idempotent_any(sc, d, args, os, rs, ok):
  PIdempotent.id.all(sc, d, args, os, rs, ok)
