import Base
import ../../bend/color.bend as Co
import ../../laws/color.bend as Color

# eukhe: the proof of LAW color_ansi256_spec: one case per range test

def ca2.go(lo: Bool, cube: Bool, +i: U32) -> {Co.ansi256.pick(lo, cube, i) == Color.th.ansi_any.if(lo, cube, i) : Co.Rgb}:
  match lo:
    case True{}:
      {==}
    case False{}:
      match cube:
        case True{}:
          {==}
        case False{}:
          {==}

def Color.color_ansi256_spec(i):
  ca2.go(U32.is_lt(i, 16), U32.is_lt(i, 232), i)
