# eukhe: the proof of LAW verify_only_checked

import Base
import ../../bend/screen.bend as Sc
import ../../LAWS.bend as Laws

# 3. Off-screen verification
# --------------------------

def ps.verify_only_checked(f: Nat, g: Nat, +ok1: Bool, +ok2: Bool) -> {Sc.checked(Sc.present(f, g, ok1, ok2), ok1, ok2) == True{} : Bool}:
  match ok1:
    case True{}:
      {==}
    case False{}:
      match ok2:
        case True{}:
          {==}
        case False{}:
          {==}

def Laws.verify_only_checked(f, g, ok1, ok2):
  ps.verify_only_checked(f, g, ok1, ok2)
