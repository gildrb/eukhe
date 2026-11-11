# eukhe: the proof of LAW scan_start_mismatch
#
# PROOF: case on the two orders: equal ones contradict other; for different ones both starts compute to the refusal.

import Base
import ../../bend/scan.bend as Sc
import ../../bend/ffi_scan.bend as FSc
import ../../bend/wire.bend as Wr
import ../../laws/scan.bend as Scan
import ../base/staging.bend as LStg

def Scan.scan_start_mismatch(o, a, fallback, other):
  match o a:
    case Sc.Asc{} Sc.Asc{}:
      LStg.stg.absurd({Sc.start(Some{Sc.Asc{}}, Some{Sc.Cursor{Sc.SafeAfter{}, Scan.mark_of(Sc.Asc{})}}, fallback) == Sc.Refuse{Scan.mismatch_spec(Sc.Asc{}, Sc.Asc{})} : Sc.Start} & {Sc.start(Some{Sc.Asc{}}, Some{Sc.Cursor{Sc.SafeAfter{}, Sc.NoMark{}}}, Sc.Asc{}) == Sc.Refuse{Scan.mismatch_spec(Sc.Asc{}, Sc.Asc{})} : Sc.Start}, other)
    case Sc.Asc{} Sc.Desc{}:
      ({==}, {==})
    case Sc.Desc{} Sc.Asc{}:
      ({==}, {==})
    case Sc.Desc{} Sc.Desc{}:
      LStg.stg.absurd({Sc.start(Some{Sc.Desc{}}, Some{Sc.Cursor{Sc.SafeAfter{}, Scan.mark_of(Sc.Desc{})}}, fallback) == Sc.Refuse{Scan.mismatch_spec(Sc.Desc{}, Sc.Desc{})} : Sc.Start} & {Sc.start(Some{Sc.Desc{}}, Some{Sc.Cursor{Sc.SafeAfter{}, Sc.NoMark{}}}, Sc.Desc{}) == Sc.Refuse{Scan.mismatch_spec(Sc.Desc{}, Sc.Desc{})} : Sc.Start}, other)
