# eukhe: the proof of LAW rows_gate_goes_as_omp
#
# PROOF: every raw, utf8, utf16 and nul: both sides compute equal.

import Base
import ../../laws/doc_rows.bend as DocRows

def DocRows.rows_gate_goes_as_omp(raw, utf8, utf16, nul):
  match raw:
    case True{}:
      {==}
    case False{}:
      match utf8:
        case True{}:
          match nul:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match utf16:
            case True{}:
              {==}
            case False{}:
              match nul:
                case True{}:
                  {==}
                case False{}:
                  {==}
