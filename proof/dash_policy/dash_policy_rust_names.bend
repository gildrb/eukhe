# eukhe: the proof of LAW dash_policy_rust_names
#
# PROOF: every entry of Rust's table gets the verdict its place asks for
# (drn.all: a finite check over dp_wire, computed). The place answered for
# n is the one of the first entry named n (text_same is equality:
# stg.same_eq), so n is that entry's name and its verdict is the one its
# place asks for (drn.go, by induction on the table).

import Base
import ../../bend/dash_policy.bend as Dp
import ../../laws/base.bend as LawsBase
import ../../laws/dash_policy.bend as DashPolicy
import ../base/staging.bend as LStg
import ./base.bend as LA

# a verdict is the one place k asks for
def drn.is(v: Dp.Verdict, k: DashPolicy.DpClass) -> Bool:
  match v:
    case Dp.ForSession{}:
      LA.dpb.ceq(k, DashPolicy.DpSession{})
    case Dp.ForCatalog{}:
      LA.dpb.ceq(k, DashPolicy.DpCatalog{})
    case Dp.NotRun{}:
      LA.dpb.ceq(k, DashPolicy.DpOwned{})

def drn.is_eq(v: Dp.Verdict, +k: DashPolicy.DpClass, e: {drn.is(v, k) == True{} : Bool}) -> {v == DashPolicy.dp_of(k) : Dp.Verdict}:
  match v:
    case Dp.ForSession{}:
      %Equal.sym(DashPolicy.DpClass, k, DashPolicy.DpSession{}, LA.dpb.ceq_eq(k, DashPolicy.DpSession{}, e)) : {Dp.ForSession{} == DashPolicy.dp_of(_) : Dp.Verdict}
      {==}
    case Dp.ForCatalog{}:
      %Equal.sym(DashPolicy.DpClass, k, DashPolicy.DpCatalog{}, LA.dpb.ceq_eq(k, DashPolicy.DpCatalog{}, e)) : {Dp.ForCatalog{} == DashPolicy.dp_of(_) : Dp.Verdict}
      {==}
    case Dp.NotRun{}:
      %Equal.sym(DashPolicy.DpClass, k, DashPolicy.DpOwned{}, LA.dpb.ceq_eq(k, DashPolicy.DpOwned{}, e)) : {Dp.NotRun{} == DashPolicy.dp_of(_) : Dp.Verdict}
      {==}

# every entry of es gets the verdict its place asks for
def drn.all(es: List<&2, DashPolicy.DpEntry>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> t:
      match e:
        case DashPolicy.DpEntry{x, k}:
          Bool.and(drn.is(Dp.verdict(x), k), drn.all(t))

# the first entry of es is named n
def drn.head(+n: String, es: List<&2, DashPolicy.DpEntry>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> t:
      match e:
        case DashPolicy.DpEntry{x, k}:
          LawsBase.text_same(x, n)

# the place of a name in a table that drn.all checks gives its verdict (b:
# whether the first entry is named n)
def drn.go(+n: String, es: List<&2, DashPolicy.DpEntry>, +k: DashPolicy.DpClass, b: Bool, +eb: {drn.head(n, es) == b : Bool}, +all: {drn.all(es) == True{} : Bool}, named: {DashPolicy.dp_class(n, es) == Some{k} : Maybe<&2, DashPolicy.DpClass>}) -> {Dp.verdict(n) == DashPolicy.dp_of(k) : Dp.Verdict}:
  match es:
    case Nil{}:
      LA.dpb.none_some({Dp.verdict(n) == DashPolicy.dp_of(k) : Dp.Verdict}, k, named)
    case e <> +t:
      match e:
        case DashPolicy.DpEntry{+x, +c}:
          match b:
            case True{}:
              +ecn = Equal.trans(Maybe<&2, DashPolicy.DpClass>, Some{c}, DashPolicy.dp_class.at(LawsBase.text_same(x, n), c, DashPolicy.dp_class(n, t)), Some{k}, Equal.cong(Bool, Maybe<&2, DashPolicy.DpClass>, z => DashPolicy.dp_class.at(z, c, DashPolicy.dp_class(n, t)), True{}, LawsBase.text_same(x, n), Equal.sym(Bool, LawsBase.text_same(x, n), True{}, eb)), named)
              +eck = LA.dpb.some_inj(c, k, ecn)
              +exn = LStg.stg.same_eq(x, n, eb)
              +evx = drn.is_eq(Dp.verdict(x), c, LStg.stg.and_l(drn.is(Dp.verdict(x), c), drn.all(t), all))
              %exn : {Dp.verdict(_) == DashPolicy.dp_of(k) : Dp.Verdict}
              %eck : {Dp.verdict(x) == DashPolicy.dp_of(_) : Dp.Verdict}
              evx
            case False{}:
              +named2 = Equal.trans(Maybe<&2, DashPolicy.DpClass>, DashPolicy.dp_class(n, t), DashPolicy.dp_class.at(LawsBase.text_same(x, n), c, DashPolicy.dp_class(n, t)), Some{k}, Equal.cong(Bool, Maybe<&2, DashPolicy.DpClass>, z => DashPolicy.dp_class.at(z, c, DashPolicy.dp_class(n, t)), False{}, LawsBase.text_same(x, n), Equal.sym(Bool, LawsBase.text_same(x, n), False{}, eb)), named)
              drn.go(n, t, k, drn.head(n, t), {==}, LStg.stg.and_r(drn.is(Dp.verdict(x), c), drn.all(t), all), named2)

def DashPolicy.dash_policy_rust_names(n, k, named):
  drn.go(n, DashPolicy.dp_wire(), k, drn.head(n, DashPolicy.dp_wire()), {==}, {==}, named)
