# eukhe: the proof of LAW scan_start_bad_after
#
# PROOF: case on the `after` field: absent and not safe refuse before the order field is read; a safe one contradicts bad.

import Base
import ../../bend/scan.bend as Sc
import ../../bend/ffi_scan.bend as FSc
import ../../bend/wire.bend as Wr
import ../../laws/scan.bend as Scan
import ../base/staging.bend as LStg

def Scan.scan_start_bad_after(asked, m, fallback, a, bad):
  match a:
    case Sc.NoAfter{}:
      {==}
    case Sc.BadAfter{}:
      {==}
    case Sc.SafeAfter{}:
      LStg.stg.absurd({Sc.start(asked, Some{Sc.Cursor{Sc.SafeAfter{}, m}}, fallback) == Sc.Refuse{"Invalid storage cursor"} : Sc.Start}, bad)
