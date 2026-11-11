# eukhe: the proof of LAW error_body_blank
#
# PROOF: the code's start trim of white space only is empty
# (LA.ebr.start_ws), and an empty trimmed text is no body.

import Base
import ../../bend/error_body.bend as Eb
import ../../laws/error_body.bend as ErrorBody
import ../base/staging.bend as LStg
import ./base.bend as LA

def ErrorBody.error_body_blank(x, hx):
  %Equal.sym(String, Eb.trim_start(x), SNil{}, LA.ebr.start_ws(x, hx)) : {Eb.body.of(Eb.trim_end(_)) == None{} : Maybe<&2, String>}
  {==}
