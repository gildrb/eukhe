# eukhe: the proof of LAW glob_utf8
#
# PROOF: split on the three length tests in the order the code asks them;
# in each case both sides compute the same bytes.

import Base
import ../../laws/glob.bend as Glob
import ../../bend/glob/items.bend as GItems

def gu8.d(+x: U32, +rest: List<&2, U32>, b: Bool) -> {GItems.utf8.d(x, rest, b) == Glob.sp_utf8.at(Glob.sp_utf8.more(False{}, False{}, b), x, rest) : List<&2, U32>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def gu8.c(+x: U32, +rest: List<&2, U32>, b: Bool) -> {GItems.utf8.c(x, rest, b) == Glob.sp_utf8.at(Glob.sp_utf8.more(False{}, b, U32.is_lt(x, 65536)), x, rest) : List<&2, U32>}:
  match b:
    case True{}:
      {==}
    case False{}:
      gu8.d(x, rest, U32.is_lt(x, 65536))

def gu8.b(+x: U32, +rest: List<&2, U32>, b: Bool) -> {GItems.utf8.b(x, rest, b) == Glob.sp_utf8.at(Glob.sp_utf8.more(b, U32.is_lt(x, 2048), U32.is_lt(x, 65536)), x, rest) : List<&2, U32>}:
  match b:
    case True{}:
      {==}
    case False{}:
      gu8.c(x, rest, U32.is_lt(x, 2048))

def Glob.glob_utf8(x, rest):
  gu8.b(x, rest, U32.is_lt(x, 128))
