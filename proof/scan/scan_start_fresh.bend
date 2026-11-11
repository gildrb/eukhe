# eukhe: the proof of LAW scan_start_fresh
#
# PROOF: case on the order asked and the default: each start computes.

import Base
import ../../bend/scan.bend as Sc
import ../../bend/ffi_scan.bend as FSc
import ../../bend/wire.bend as Wr
import ../../laws/scan.bend as Scan
import ../base/staging.bend as LStg

def Scan.scan_start_fresh(a, fallback):
  match a fallback:
    case Sc.Asc{} Sc.Asc{}:
      ({==}, {==})
    case Sc.Asc{} Sc.Desc{}:
      ({==}, {==})
    case Sc.Desc{} Sc.Asc{}:
      ({==}, {==})
    case Sc.Desc{} Sc.Desc{}:
      ({==}, {==})
