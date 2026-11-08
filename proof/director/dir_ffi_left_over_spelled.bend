# eukhe: the proof of LAW dir_ffi_left_over_spelled
#
# PROOF: the spelled request is the entry's own encoding of it (pds.req),
# which reads back whole with the rest after it (pdf.req_rt); a rest that
# is not empty is input left over.

import Base
import ../../bend/ffi_director.bend as FDr
import ../../bend/wire.bend as Wr
import ../../laws/director.bend as Director
import ./base.bend as LA
import ./dir_ffi_answers_spelled/spell.bend as LS

def Director.dir_ffi_left_over_spelled(q, fits, c, t):
  %LS.pds.req(q, SCon{c, t}) : {FDr.ffi(_) == Wr.err("director: input left over") : String}
  %Equal.sym(Wr.Dec<FDr.Req>, FDr.get_req(FDr.put_req(q, SCon{c, t})), Wr.Got{q, SCon{c, t}}, LA.pdf.req_rt(q, SCon{c, t}, fits)) : {FDr.ffi.go(_) == Wr.err("director: input left over") : String}
  {==}
