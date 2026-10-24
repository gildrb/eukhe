# eukhe: the whitespace lemma of LAW dash_stored_spec
#
# The code and the spec both test a char's code point against the same
# list of code points, one `U32.is_eq` an item: the scans agree item by
# item (sw.in), and the lists are the same.

import Base
import ../../../bend/dash.bend as Da
import ../../../laws/dash.bend as Dash

# the code's scan of a list is the spec's
def sw.in(+x: U32, xs: List<&2, U32>) -> {Da.space.in(x, xs) == Dash.sp_in(x, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> rest:
      Equal.cong(Bool, Bool, z => Bool.or(U32.is_eq(x, y), z), Da.space.in(x, rest), Dash.sp_in(x, rest), sw.in(x, rest))

# the code's whitespace is the spec's
def sw.space(c: Char) -> {Da.space(c) == Dash.sp_space(c) : Bool}:
  sw.in(Char.to_u32(c), Da.spaces())
