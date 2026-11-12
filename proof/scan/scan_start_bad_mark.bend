# eukhe: the proof of LAW scan_start_bad_mark
#
# PROOF: a bad order field refuses whatever is asked: computes.

import Base
import ../../bend/scan.bend as Sc
import ../../bend/ffi_scan.bend as FSc
import ../../bend/wire.bend as Wr
import ../../laws/scan.bend as Scan
import ../base/staging.bend as LStg

def Scan.scan_start_bad_mark(asked, fallback):
  {==}
