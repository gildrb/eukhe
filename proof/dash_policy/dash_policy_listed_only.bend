# eukhe: the proof of LAW dash_policy_listed_only
#
# PROOF: a catalog verdict means the code's catalog table lists n, a
# session verdict that its session table does (dlo.cat, dlo.ses: the
# other cases answer another verdict). A listed name is one of the
# table's names (the code's comparison is equality: dpb.same_eq), and
# Rust's table places each of them where the verdict says (dlo.all: a
# finite check, computed), so n is placed there (dlo.mem, by induction on
# the table).

import Base
import ../../bend/dash_policy.bend as Dp
import ../../laws/base.bend as LawsBase
import ../../laws/dash_policy.bend as DashPolicy
import ../base/staging.bend as LStg
import ./base.bend as LA

def dlo.V.If(v: Dp.Verdict, G: Type) -> Type:
  match v:
    case Dp.ForSession{}:
      Unit
    case Dp.ForCatalog{}:
      G
    case Dp.NotRun{}:
      Unit

# a session or refused verdict is no catalog verdict
def dlo.not_cat(-G: Type, -v: Dp.Verdict, e: {v == Dp.ForCatalog{} : Dp.Verdict}, nc: dlo.V.If(v, G)) -> G:
  %e : dlo.V.If(_, G)
  nc

def dlo.S.If(v: Dp.Verdict, G: Type) -> Type:
  match v:
    case Dp.ForSession{}:
      G
    case Dp.ForCatalog{}:
      Unit
    case Dp.NotRun{}:
      Unit

def dlo.not_ses(-G: Type, -v: Dp.Verdict, e: {v == Dp.ForSession{} : Dp.Verdict}, nc: dlo.S.If(v, G)) -> G:
  %e : dlo.S.If(_, G)
  nc

# a catalog verdict: the catalog table lists the name
def dlo.cat(a: Bool, b: Bool, e: {Dp.verdict.of(a, b) == Dp.ForCatalog{} : Dp.Verdict}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      match b:
        case True{}:
          dlo.not_cat({False{} == True{} : Bool}, Dp.ForSession{}, e, Unit{})
        case False{}:
          dlo.not_cat({False{} == True{} : Bool}, Dp.NotRun{}, e, Unit{})

# a session verdict: the session table lists the name
def dlo.ses(a: Bool, b: Bool, e: {Dp.verdict.of(a, b) == Dp.ForSession{} : Dp.Verdict}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      dlo.not_ses({b == True{} : Bool}, Dp.ForCatalog{}, e, Unit{})
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          dlo.not_ses({False{} == True{} : Bool}, Dp.NotRun{}, e, Unit{})

# Rust's table places every name of xs at k
def dlo.all(xs: List<&2, String>, +k: DashPolicy.DpClass) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(LA.dpb.is(DashPolicy.dp_class(x, DashPolicy.dp_wire()), k), dlo.all(t, k))

# the first name of xs is n, as the code compares
def dlo.head(+n: String, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Dp.same(x, n)

# a name a table lists, every name of which Rust's table places at k, is
# placed at k (c: whether it is the table's first name)
def dlo.mem(+n: String, xs: List<&2, String>, +k: DashPolicy.DpClass, c: Bool, +ec: {dlo.head(n, xs) == c : Bool}, +all: {dlo.all(xs, k) == True{} : Bool}, inn: {Dp.listed(n, xs) == True{} : Bool}) -> {DashPolicy.dp_class(n, DashPolicy.dp_wire()) == Some{k} : Maybe<&2, DashPolicy.DpClass>}:
  match xs:
    case Nil{}:
      LStg.stg.absurdF({DashPolicy.dp_class(n, DashPolicy.dp_wire()) == Some{k} : Maybe<&2, DashPolicy.DpClass>}, inn)
    case +x <> +t:
      match c:
        case True{}:
          +exn = LA.dpb.same_eq(x, n, ec)
          +ex = LA.dpb.is_eq(DashPolicy.dp_class(x, DashPolicy.dp_wire()), k, LStg.stg.and_l(LA.dpb.is(DashPolicy.dp_class(x, DashPolicy.dp_wire()), k), dlo.all(t, k), all))
          %exn : {DashPolicy.dp_class(_, DashPolicy.dp_wire()) == Some{k} : Maybe<&2, DashPolicy.DpClass>}
          ex
        case False{}:
          +inn2 = Equal.trans(Bool, Dp.listed(n, t), Bool.or(Dp.same(x, n), Dp.listed(n, t)), True{}, Equal.cong(Bool, Bool, z => Bool.or(z, Dp.listed(n, t)), False{}, Dp.same(x, n), Equal.sym(Bool, Dp.same(x, n), False{}, ec)), inn)
          dlo.mem(n, t, k, dlo.head(n, t), {==}, LStg.stg.and_r(LA.dpb.is(DashPolicy.dp_class(x, DashPolicy.dp_wire()), k), dlo.all(t, k), all), inn2)

def DashPolicy.dash_policy_listed_only(n, k, ran, runs):
  match k:
    case DashPolicy.DpCatalog{}:
      dlo.mem(n, Dp.catalog(), DashPolicy.DpCatalog{}, dlo.head(n, Dp.catalog()), {==}, {==}, dlo.cat(Dp.listed(n, Dp.catalog()), Dp.listed(n, Dp.session()), ran))
    case DashPolicy.DpSession{}:
      dlo.mem(n, Dp.session(), DashPolicy.DpSession{}, dlo.head(n, Dp.session()), {==}, {==}, dlo.ses(Dp.listed(n, Dp.catalog()), Dp.listed(n, Dp.session()), ran))
    case DashPolicy.DpOwned{}:
      LStg.stg.absurdF({DashPolicy.dp_class(n, DashPolicy.dp_wire()) == Some{DashPolicy.DpOwned{}} : Maybe<&2, DashPolicy.DpClass>}, runs)
