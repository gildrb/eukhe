# eukhe: the proof of LAW error_body_body
#
# PROOF: the code picks the place the spec picks (LA.ebb.pick), trims as
# the spec trims (LA.ebt.trim: per char the white space is the spec's,
# LA.ebc.ws; the end is cut where only white space is left, LA.ebt.shape),
# and cuts as the spec cuts (LA.ebt.truncate).

import Base
import ../../bend/error_body.bend as Eb
import ../../bend/ffi_error_body.bend as FEb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/error_body.bend as ErrorBody
import ./base.bend as LA

def ErrorBody.error_body_body(b, e, r):
  LA.ebb.body(b, e, r)
