# eukhe: the proof of LAW verify_entry_unknown_tag_refused
#
# PROOF: the tag reads back from its spelling (LE.ve.nat); a tag of 8 or
# more is no request, so the entry answers its error form.

import Base
import ../../bend/ffi_verify.bend as FV
import ../../bend/wire.bend as Wr
import ../../laws/verify.bend as Verify
import ./base/entry.bend as LE

def Verify.verify_entry_unknown_tag_refused(n, s, fit):
  %LE.ve.nat(8n+n, s, fit) : {FV.ffi.got(FV.get_req(_)) == Wr.err("verify: malformed request") : String}
  {==}
