# eukhe: the proof of LAW child_entry_bad_request
#
# PROOF: the request tag does not read, so the entry's first stage
# answers the bad request error.

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child/entry.bend as Child
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ./base.bend as LA

def Child.child_entry_bad_request(rest, bad):
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(rest), Wr.Bad{}, bad) : {FCh.run(_) == Wr.err("child: bad request") : String}
  {==}
