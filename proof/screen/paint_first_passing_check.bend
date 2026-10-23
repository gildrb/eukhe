# eukhe: the proof of LAW paint_first_passing_check

import Base
import ../../bend/screen.bend as Sc
import ../../laws/screen.bend as Screen

def ps.paint_first_passing_check(+f: Nat, +g: Nat, +h: Nat, +ok1: Bool, +ok2: Bool, +ok3: Bool) -> {Sc.resync(Sc.present(f, g, ok1, ok2), h, ok3) == Screen.screen_paint_spec(f, g, h, ok1, ok2, ok3) : Sc.Paint}:
  match ok1:
    case True{}:
      {==}
    case False{}:
      match ok2:
        case True{}:
          {==}
        case False{}:
          match ok3:
            case True{}:
              {==}
            case False{}:
              {==}

def Screen.paint_first_passing_check(f, g, h, ok1, ok2, ok3):
  ps.paint_first_passing_check(f, g, h, ok1, ok2, ok3)
