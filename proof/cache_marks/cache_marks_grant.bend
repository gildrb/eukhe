# eukhe: the proof of LAW cache_marks_grant
#
# PROOF: the code walk with f slots left is the spec's walk after 0 wanted
# marks with 0 + f slots (LA.cmb.go), and 0 + f is f.

import Base
import ../../bend/cache_marks.bend as Cm
import ../../bend/ffi_cache_marks.bend as FCm
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/cache_marks.bend as CacheMarks
import ./base.bend as LA

def CacheMarks.cache_marks_grant(placed, ws):
  +f = Nat.sub(4n, placed)
  Equal.trans(List<&2, Bool>, Cm.grant.go(ws, f), CacheMarks.sp_grant.go(ws, 0n, Nat.add(f, 0n)), CacheMarks.sp_grant.go(ws, 0n, f), LA.cmb.go(ws, f, 0n), Equal.cong(Nat, List<&2, Bool>, z => CacheMarks.sp_grant.go(ws, 0n, z), Nat.add(f, 0n), f, LA.cmb.add_zero(f)))
