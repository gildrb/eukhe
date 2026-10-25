# eukhe: the proof of LAW error_body_truncate
#
# PROOF: the code counts the spec's UTF-16 units (LA.ebc.u: 65536 <= x is
# 65535 < x on 32-bit words, LA.ebw.astral) and keeps the spec's prefix
# (LA.ebt.prefix), so its cut is the spec's (LA.ebt.truncate).

import Base
import ../../bend/error_body.bend as Eb
import ../../bend/ffi_error_body.bend as FEb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/error_body.bend as ErrorBody
import ./base.bend as LA

def ErrorBody.error_body_truncate(text, cap):
  LA.ebt.truncate(text, cap)
