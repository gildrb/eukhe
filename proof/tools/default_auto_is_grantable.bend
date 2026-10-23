# eukhe: the proof of LAW default_auto_is_grantable

import Base
import ../../bend/approvals.bend as Am
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools

# The auto set
# ------------

def pa.default_auto(+c: Nat) -> {Tl.elem(Am.default_auto(), c) == Tl.grantable(c) : Bool}:
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

# (G5) The default auto set; the never-auto effects

def Tools.default_auto_is_grantable(c):
  pa.default_auto(c)
