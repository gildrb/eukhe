# eukhe: lemmas shared by the proofs of area dash_policy: the code's
# char-by-char comparison and name test are the spec's

import Base
import ../../bend/dash_policy.bend as Dp
import ../../laws/base.bend as LawsBase
import ../../laws/dash_policy.bend as DashPolicy

# the code's comparison is the spec's text_same
def dpb.same(a: String, b: String) -> {Dp.same(a, b) == LawsBase.text_same(a, b) : Bool}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, v}:
      {==}
    case SCon{x, u} SNil{}:
      {==}
    case SCon{x, u} SCon{y, v}:
      %dpb.same(u, v) : {Bool.and(Char.is_eq(x, y), Dp.same(u, v)) == Bool.and(Char.is_eq(x, y), _) : Bool}
      {==}

# the code's name test is the spec's, on every list
def dpb.listed(+n: String, xs: List<&2, String>) -> {Dp.listed(n, xs) == DashPolicy.dp_in(n, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      %dpb.same(x, n) : {Bool.or(Dp.same(x, n), Dp.listed(n, t)) == Bool.or(_, DashPolicy.dp_in(n, t)) : Bool}
      %dpb.listed(n, t) : {Bool.or(Dp.same(x, n), Dp.listed(n, t)) == Bool.or(Dp.same(x, n), _) : Bool}
      {==}
