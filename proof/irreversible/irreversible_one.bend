# eukhe: the proof of LAW irreversible_one
#
# PROOF: by cases on the code: 0, 1 and 2 are below 3, any code from 3 up
# is not; both sides compute.

import Base
import ../../laws/irreversible.bend as Irreversible

def Irreversible.irreversible_one(c):
  match c:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+d:
              match d:
                case 0n:
                  {==}
                case 1n+e:
                  {==}
