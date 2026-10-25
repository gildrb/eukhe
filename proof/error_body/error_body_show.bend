# eukhe: the proof of LAW error_body_show
#
# PROOF: every flag, status, body and prefix: both sides compute
# (LA.ebs.show).

import Base
import ../../bend/error_body.bend as Eb
import ../../bend/ffi_error_body.bend as FEb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/error_body.bend as ErrorBody
import ./base.bend as LA

def ErrorBody.error_body_show(c, st, b, p, m):
  LA.ebs.show(c, st, b, p, m)
