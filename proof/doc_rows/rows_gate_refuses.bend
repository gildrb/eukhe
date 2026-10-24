# eukhe: the proof of LAW rows_gate_refuses

import Base
import ../../laws/doc_rows.bend as DocRows

# every raw, utf8, utf16 and nul: both sides compute equal
def DocRows.rows_gate_refuses(raw, utf8, utf16, nul):
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
              match nul:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match nul:
                case True{}:
                  {==}
                case False{}:
                  {==}
