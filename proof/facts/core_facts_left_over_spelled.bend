# eukhe: the proof of LAW core_facts_left_over_spelled
#
# PROOF: the spelled request reads back whole (LA.fs.run), whose end check
# sees the char left and answers the left-over error form.

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_facts.bend as FFx
import ../../bend/wire.bend as Wr
import ../../laws/facts.bend as Facts
import ../../laws/base.bend as LawsBase
import ./base.bend as LA

def flo.main(+q: FFx.Req, fits: {Facts.core_facts_req_fits(q) == True{} : Bool}, +c: Char, +t: String) -> {FFx.ffi(Facts.facts_spell_req(q, SCon{c, t})) == Wr.err("budget request: input left over") : String}:
  LA.fs.run(q, SCon{c, t}, fits)

def Facts.core_facts_left_over_spelled(q, fits, c, t):
  flo.main(q, fits, c, t)
