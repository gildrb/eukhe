# eukhe: the proof of LAW infer_force_flag_exact
# By cases on the attempt and the provider's support.

import Base
import ../../laws/infer_force.bend as InferForce

def InferForce.infer_force_flag_exact(i, sup, free):
  match i:
    case 0n:
      match sup:
        case True{}:
          {==}
        case False{}:
          {==}
    case 1n+j:
      {==}
