# eukhe: the proof of LAW color_hexd_spec: the same three range tests in
# the same order, one case per test result

import Base
import ../../bend/color.bend as Co
import ../../laws/color.bend as Color

def hx.up(b: Bool, +x: U32) -> {Co.hexd.up(b, x) == Color.th.hexv.up(b, x) : Maybe<&2, U32>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def hx.low(b: Bool, +x: U32) -> {Co.hexd.low(b, x) == Color.th.hexv.low(b, x) : Maybe<&2, U32>}:
  match b:
    case True{}:
      {==}
    case False{}:
      hx.up(Co.in(x, 65, 70), x)

def hx.dec(b: Bool, +x: U32) -> {Co.hexd.dec(b, x) == Color.th.hexv.dec(b, x) : Maybe<&2, U32>}:
  match b:
    case True{}:
      {==}
    case False{}:
      hx.low(Co.in(x, 97, 102), x)

def Color.color_hexd_spec(c):
  match c:
    case Chr{+x}:
      hx.dec(Co.in(x, 48, 57), x)
