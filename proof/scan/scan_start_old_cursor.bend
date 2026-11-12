# eukhe: the proof of LAW scan_start_old_cursor
#
# PROOF: case on the default: each start computes.

import Base
import ../../bend/scan.bend as Sc
import ../../bend/ffi_scan.bend as FSc
import ../../bend/wire.bend as Wr
import ../../laws/scan.bend as Scan
import ../base/staging.bend as LStg

def Scan.scan_start_old_cursor(fallback):
  match fallback:
    case Sc.Asc{}:
      ({==}, {==})
    case Sc.Desc{}:
      ({==}, {==})
