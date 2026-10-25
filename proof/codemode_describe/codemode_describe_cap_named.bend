# eukhe: the proof of LAW codemode_describe_cap_named

import Base
import ../../bend/codemode_describe.bend as Dsc
import ../../bend/codemode_models.bend as Cm
import ../../laws/codemode_describe.bend as CodemodeDescribe

# PROOF of LAW codemode_describe_cap_named: both choices compute from the limit.

def CodemodeDescribe.codemode_describe_cap_named(classify):
  match classify:
    case True{}:
      {==}
    case False{}:
      {==}
