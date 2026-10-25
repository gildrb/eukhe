# eukhe: the proof of LAW cache_marks_excess
#
# PROOF: by cases on the count: 0 to 3 compute to no error; from 4 on
# both sides compute to the text with the count.

import Base
import ../../bend/cache_marks.bend as Cm
import ../../bend/ffi_cache_marks.bend as FCm
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/cache_marks.bend as CacheMarks

def CacheMarks.cache_marks_excess(n):
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n+m:
      {==}
