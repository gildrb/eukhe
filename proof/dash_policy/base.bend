# eukhe: lemmas shared by the proofs of area dash_policy: the code's
# char-by-char comparison is the spec's text_same, places compare, and an
# answer that is Some{k} is k

import Base
import ../../bend/dash_policy.bend as Dp
import ../../laws/base.bend as LawsBase
import ../../laws/dash_policy.bend as DashPolicy
import ../base/staging.bend as LStg

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

# the code's comparison is equality
def dpb.same_eq(+a: String, +b: String, e: {Dp.same(a, b) == True{} : Bool}) -> {a == b : String}:
  LStg.stg.same_eq(a, b, Equal.trans(Bool, LawsBase.text_same(a, b), Dp.same(a, b), True{}, Equal.sym(Bool, Dp.same(a, b), LawsBase.text_same(a, b), dpb.same(a, b)), e))

# two places are the same place
def dpb.ceq(a: DashPolicy.DpClass, b: DashPolicy.DpClass) -> Bool:
  match a:
    case DashPolicy.DpCatalog{}:
      match b:
        case DashPolicy.DpCatalog{}:
          True{}
        case DashPolicy.DpSession{}:
          False{}
        case DashPolicy.DpOwned{}:
          False{}
    case DashPolicy.DpSession{}:
      match b:
        case DashPolicy.DpCatalog{}:
          False{}
        case DashPolicy.DpSession{}:
          True{}
        case DashPolicy.DpOwned{}:
          False{}
    case DashPolicy.DpOwned{}:
      match b:
        case DashPolicy.DpCatalog{}:
          False{}
        case DashPolicy.DpSession{}:
          False{}
        case DashPolicy.DpOwned{}:
          True{}

def dpb.ceq_eq(a: DashPolicy.DpClass, b: DashPolicy.DpClass, e: {dpb.ceq(a, b) == True{} : Bool}) -> {a == b : DashPolicy.DpClass}:
  match a:
    case DashPolicy.DpCatalog{}:
      match b:
        case DashPolicy.DpCatalog{}:
          {==}
        case DashPolicy.DpSession{}:
          LStg.stg.absurdF({DashPolicy.DpCatalog{} == DashPolicy.DpSession{} : DashPolicy.DpClass}, e)
        case DashPolicy.DpOwned{}:
          LStg.stg.absurdF({DashPolicy.DpCatalog{} == DashPolicy.DpOwned{} : DashPolicy.DpClass}, e)
    case DashPolicy.DpSession{}:
      match b:
        case DashPolicy.DpCatalog{}:
          LStg.stg.absurdF({DashPolicy.DpSession{} == DashPolicy.DpCatalog{} : DashPolicy.DpClass}, e)
        case DashPolicy.DpSession{}:
          {==}
        case DashPolicy.DpOwned{}:
          LStg.stg.absurdF({DashPolicy.DpSession{} == DashPolicy.DpOwned{} : DashPolicy.DpClass}, e)
    case DashPolicy.DpOwned{}:
      match b:
        case DashPolicy.DpCatalog{}:
          LStg.stg.absurdF({DashPolicy.DpOwned{} == DashPolicy.DpCatalog{} : DashPolicy.DpClass}, e)
        case DashPolicy.DpSession{}:
          LStg.stg.absurdF({DashPolicy.DpOwned{} == DashPolicy.DpSession{} : DashPolicy.DpClass}, e)
        case DashPolicy.DpOwned{}:
          {==}

# the value inside an answer, d if none
def dpb.get(m: Maybe<&2, DashPolicy.DpClass>, d: DashPolicy.DpClass) -> DashPolicy.DpClass:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def dpb.some_inj(+a: DashPolicy.DpClass, -b: DashPolicy.DpClass, e: {Some{a} == Some{b} : Maybe<&2, DashPolicy.DpClass>}) -> {a == b : DashPolicy.DpClass}:
  Equal.cong(Maybe<&2, DashPolicy.DpClass>, DashPolicy.DpClass, m => dpb.get(m, a), Some{a}, Some{b}, e)

def dpb.M.If(m: Maybe<&2, DashPolicy.DpClass>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# no answer is not an answer
def dpb.none_some(-G: Type, -b: DashPolicy.DpClass, e: {None{} == Some{b} : Maybe<&2, DashPolicy.DpClass>}) -> G:
  %e : dpb.M.If(_, G)
  Unit{}

# an answer that is k, as a test
def dpb.is(m: Maybe<&2, DashPolicy.DpClass>, k: DashPolicy.DpClass) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      dpb.ceq(x, k)

def dpb.is_eq(m: Maybe<&2, DashPolicy.DpClass>, +k: DashPolicy.DpClass, e: {dpb.is(m, k) == True{} : Bool}) -> {m == Some{k} : Maybe<&2, DashPolicy.DpClass>}:
  match m:
    case None{}:
      LStg.stg.absurdF({None{} == Some{k} : Maybe<&2, DashPolicy.DpClass>}, e)
    case Some{+x}:
      Equal.cong(DashPolicy.DpClass, Maybe<&2, DashPolicy.DpClass>, z => Some{z}, x, k, dpb.ceq_eq(x, k, e))
