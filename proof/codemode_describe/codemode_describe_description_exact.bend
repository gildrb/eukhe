# eukhe: the proof of LAW codemode_describe_description_exact

import Base
import ../../bend/codemode_describe.bend as Dsc
import ../../laws/codemode_describe.bend as CodemodeDescribe

# PROOF of LAW codemode_describe_description_exact: each of the four choices computes.

def CodemodeDescribe.codemode_describe_description_exact(on, classify):
  match on:
    case True{}:
      match classify:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match classify:
        case True{}:
          {==}
        case False{}:
          {==}
