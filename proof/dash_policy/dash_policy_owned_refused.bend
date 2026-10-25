# eukhe: the proof of LAW dash_policy_owned_refused
#
# PROOF: the spec refuses each owned name (dpo.all: a finite check over
# the owned table, computed); a name in a table is one of its names
# (text_same is equality: stg.same_eq), so its verdict is refused
# (dpo.mem, by induction on the table); the code's verdict is the spec's
# (dash_policy_spec).

import Base
import ../../bend/dash_policy.bend as Dp
import ../../laws/base.bend as LawsBase
import ../../laws/dash_policy.bend as DashPolicy
import ../base/staging.bend as LStg
import ./dash_policy_spec.bend as PDashPolicySpec

# the verdict is refused
def dpo.isnot(v: Dp.Verdict) -> Bool:
  match v:
    case Dp.ForSession{}:
      False{}
    case Dp.ForCatalog{}:
      False{}
    case Dp.NotRun{}:
      True{}

# the spec refuses every name of xs
def dpo.all(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(dpo.isnot(DashPolicy.dp_verdict(x)), dpo.all(t))

def dpo.isnot_eq(v: Dp.Verdict, e: {dpo.isnot(v) == True{} : Bool}) -> {v == Dp.NotRun{} : Dp.Verdict}:
  match v:
    case Dp.ForSession{}:
      LStg.stg.absurdF({Dp.ForSession{} == Dp.NotRun{} : Dp.Verdict}, e)
    case Dp.ForCatalog{}:
      LStg.stg.absurdF({Dp.ForCatalog{} == Dp.NotRun{} : Dp.Verdict}, e)
    case Dp.NotRun{}:
      {==}

# the first name of xs is n
def dpo.head(+n: String, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      LawsBase.text_same(x, n)

# a name of a table the spec refuses wholly is refused (c: whether it is
# the table's first name)
def dpo.mem(+n: String, xs: List<&2, String>, c: Bool, ec: {dpo.head(n, xs) == c : Bool}, all: {dpo.all(xs) == True{} : Bool}, inn: {DashPolicy.dp_in(n, xs) == True{} : Bool}) -> {DashPolicy.dp_verdict(n) == Dp.NotRun{} : Dp.Verdict}:
  match xs:
    case Nil{}:
      LStg.stg.absurdF({DashPolicy.dp_verdict(n) == Dp.NotRun{} : Dp.Verdict}, inn)
    case +x <> +t:
      match c:
        case True{}:
          +exn = LStg.stg.same_eq(x, n, ec)
          +ex = dpo.isnot_eq(DashPolicy.dp_verdict(x), LStg.stg.and_l(dpo.isnot(DashPolicy.dp_verdict(x)), dpo.all(t), all))
          Equal.trans(Dp.Verdict, DashPolicy.dp_verdict(n), DashPolicy.dp_verdict(x), Dp.NotRun{}, Equal.cong(String, Dp.Verdict, z => DashPolicy.dp_verdict(z), n, x, Equal.sym(String, x, n, exn)), ex)
        case False{}:
          +inn2 = Equal.trans(Bool, DashPolicy.dp_in(n, t), Bool.or(LawsBase.text_same(x, n), DashPolicy.dp_in(n, t)), True{}, Equal.cong(Bool, Bool, z => Bool.or(z, DashPolicy.dp_in(n, t)), False{}, LawsBase.text_same(x, n), Equal.sym(Bool, LawsBase.text_same(x, n), False{}, ec)), inn)
          dpo.mem(n, t, dpo.head(n, t), {==}, LStg.stg.and_r(dpo.isnot(DashPolicy.dp_verdict(x)), dpo.all(t), all), inn2)

def DashPolicy.dash_policy_owned_refused(n, owned):
  Equal.trans(Dp.Verdict, Dp.verdict(n), DashPolicy.dp_verdict(n), Dp.NotRun{}, DashPolicy.dash_policy_spec(n), dpo.mem(n, DashPolicy.dp_owned(), dpo.head(n, DashPolicy.dp_owned()), {==}, {==}, owned))
