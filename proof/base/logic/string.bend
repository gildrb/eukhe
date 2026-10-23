# eukhe: lemmas the proofs of two or more areas share: logic/string

import Base
import ../../../bend/wire.bend as Wr

# ---- the digits of a Nat, lowest first ----

# the chars of ds (lowest digit first) before acc: the highest digit leads
def wn_emit(ds: List<&2, Nat>, acc: String) -> String:
  match ds:
    case Nil{}:
      acc
    case Con{d, t}:
      wn_emit(t, SCon{Wr.dchar(d), acc})

# String
# ------

# a then rest
def wr_app(a: String, rest: String) -> String:
  match a:
    case SNil{}:
      rest
    case SCon{c, t}:
      SCon{c, wr_app(t, rest)}

# Lists
# -----

# the items of xs, then rest
def wr_items(xs: List<&2, Nat>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      Wr.put_nat(x, wr_items(t, rest))
