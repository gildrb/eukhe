# eukhe: the proof of LAW codemode_source_exact

import Base
import ../../bend/codemode_source.bend as Src
import ../../bend/ffi_codemode_source.bend as FSrc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/codemode_source.bend as CodemodeSource
import ./base.bend as LACs

# PROOF of LAW codemode_source_exact: each step of Src.parse is the spec's step: the blank and misplaced checks compute, the rest is csr.dir (the options, the first unsupported key, the values).

def CodemodeSource.codemode_source_exact(f):
  match f:
    case Src.Facts{blank, ms, rb, m}:
      match blank:
        case True{}:
          {==}
        case False{}:
          match ms:
            case k <> t:
              {==}
            case Nil{}:
              LACs.csr.dir(m, rb)
