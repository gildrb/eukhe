# eukhe: the proof of LAW model_facts_ffi_malformed_exact
# The laws' reader reads every input as the entry does, stage by stage
# (mfm.*); where it finds no whole request, the entry answers its error.

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_model_facts.bend as FMF
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/model_facts.bend as ModelFacts

def mfm.mnat_some(r: Wr.Dec<Nat>) -> {ModelFacts.mfr.get_mnat.some(r) == FMF.get_mnat.some(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{n, +s}:
      {==}
    case Wr.Bad{}:
      {==}

def mfm.mnat_tag(t: Nat, +s: String) -> {ModelFacts.mfr.get_mnat.tag(t, s) == FMF.get_mnat.tag(t, s) : Wr.Dec<Maybe<&2, Nat>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      mfm.mnat_some(Wr.get_nat(s))
    case 2n+p:
      {==}

def mfm.mnat(r: Wr.Dec<Nat>) -> {ModelFacts.mfr.get_mnat(r) == FMF.get_mnat(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{t, +s}:
      mfm.mnat_tag(t, s)
    case Wr.Bad{}:
      {==}

def mfm.ans_known(r: Wr.Dec<Nat>) -> {ModelFacts.mfr.get_ans.known(r) == FMF.get_ans.known(r) : Wr.Dec<If.Ans>}:
  match r:
    case Wr.Got{v, +s}:
      {==}
    case Wr.Bad{}:
      {==}

def mfm.ans_tag(t: Nat, +s: String) -> {ModelFacts.mfr.get_ans.tag(t, s) == FMF.get_ans.tag(t, s) : Wr.Dec<If.Ans>}:
  match t:
    case 0n:
      mfm.ans_known(Wr.get_nat(s))
    case 1n:
      {==}
    case 2n+p:
      {==}

def mfm.ans(r: Wr.Dec<Nat>) -> {ModelFacts.mfr.get_ans(r) == FMF.get_ans(r) : Wr.Dec<If.Ans>}:
  match r:
    case Wr.Got{t, +s}:
      mfm.ans_tag(t, s)
    case Wr.Bad{}:
      {==}

def mfm.mbool_some(r: Wr.Dec<Bool>) -> {ModelFacts.mfr.get_mbool.some(r) == FMF.get_mbool.some(r) : Wr.Dec<Maybe<&2, Bool>>}:
  match r:
    case Wr.Got{b, +s}:
      {==}
    case Wr.Bad{}:
      {==}

def mfm.mbool_tag(t: Nat, +s: String) -> {ModelFacts.mfr.get_mbool.tag(t, s) == FMF.get_mbool.tag(t, s) : Wr.Dec<Maybe<&2, Bool>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      mfm.mbool_some(Wr.get_bool(s))
    case 2n+p:
      {==}

def mfm.mbool(r: Wr.Dec<Nat>) -> {ModelFacts.mfr.get_mbool(r) == FMF.get_mbool(r) : Wr.Dec<Maybe<&2, Bool>>}:
  match r:
    case Wr.Got{t, +s}:
      mfm.mbool_tag(t, s)
    case Wr.Bad{}:
      {==}

def mfm.ent_val(r: Wr.Dec<Nat>) -> {ModelFacts.mfr.get_ent.val(r) == FMF.get_ent.val(r) : Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>}:
  match r:
    case Wr.Got{v, +s}:
      {==}
    case Wr.Bad{}:
      {==}

def mfm.ent_in(t: Nat, +s: String) -> {ModelFacts.mfr.get_ent.in(t, s) == FMF.get_ent.in(t, s) : Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      mfm.ent_val(Wr.get_nat(s))
    case 2n+p:
      {==}

def mfm.ent_inner(r: Wr.Dec<Nat>) -> {ModelFacts.mfr.get_ent.inner(r) == FMF.get_ent.inner(r) : Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>}:
  match r:
    case Wr.Got{t, +s}:
      mfm.ent_in(t, s)
    case Wr.Bad{}:
      {==}

def mfm.ent_tag(t: Nat, +s: String) -> {ModelFacts.mfr.get_ent.tag(t, s) == FMF.get_ent.tag(t, s) : Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      mfm.ent_inner(Wr.get_nat(s))
    case 2n+p:
      {==}

def mfm.ent(r: Wr.Dec<Nat>) -> {ModelFacts.mfr.get_ent(r) == FMF.get_ent(r) : Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>}:
  match r:
    case Wr.Got{t, +s}:
      mfm.ent_tag(t, s)
    case Wr.Bad{}:
      {==}

def mfm.elv_tag(t: Nat, +s: String) -> {ModelFacts.mfr.get_elv.tag(t, s) == FMF.get_elv.tag(t, s) : Wr.Dec<Fx.ELv>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n+p:
      {==}

def mfm.elv(r: Wr.Dec<Nat>) -> {ModelFacts.mfr.get_elv(r) == FMF.get_elv(r) : Wr.Dec<Fx.ELv>}:
  match r:
    case Wr.Got{t, +s}:
      mfm.elv_tag(t, s)
    case Wr.Bad{}:
      {==}

def mfm.flag_d(a: If.Ans, r: Wr.Dec<Bool>) -> {ModelFacts.mfr.get_flag.d(a, r) == FMF.get_flag.d(a, r) : Wr.Dec<FMF.Req>}:
  match r:
    case Wr.Got{d, +s}:
      {==}
    case Wr.Bad{}:
      {==}

def mfm.flag(r: Wr.Dec<If.Ans>) -> {ModelFacts.mfr.get_flag(r) == FMF.get_flag(r) : Wr.Dec<FMF.Req>}:
  match r:
    case Wr.Got{a, +s}:
      mfm.flag_d(a, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def mfm.adaptive_a(c: Maybe<&2, Bool>, r: Wr.Dec<If.Ans>) -> {ModelFacts.mfr.get_adaptive.a(c, r) == FMF.get_adaptive.a(c, r) : Wr.Dec<FMF.Req>}:
  match r:
    case Wr.Got{a, +s}:
      {==}
    case Wr.Bad{}:
      {==}

def mfm.adaptive(r: Wr.Dec<Maybe<&2, Bool>>) -> {ModelFacts.mfr.get_adaptive(r) == FMF.get_adaptive(r) : Wr.Dec<FMF.Req>}:
  match r:
    case Wr.Got{c, +s}:
      %mfm.ans(Wr.get_nat(s)) : {ModelFacts.mfr.get_adaptive.a(c, ModelFacts.mfr.get_ans(Wr.get_nat(s))) == FMF.get_adaptive.a(c, _) : Wr.Dec<FMF.Req>}
      mfm.adaptive_a(c, ModelFacts.mfr.get_ans(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def mfm.effort_l(mi: Maybe<&2, Maybe<&2, Nat>>, lo: Maybe<&2, Maybe<&2, Nat>>, me: Maybe<&2, Maybe<&2, Nat>>, hi: Maybe<&2, Maybe<&2, Nat>>, xh: Maybe<&2, Maybe<&2, Nat>>, mx: Maybe<&2, Maybe<&2, Nat>>, r: Wr.Dec<Fx.ELv>) -> {ModelFacts.mfr.get_effort.l(mi, lo, me, hi, xh, mx, r) == FMF.get_effort.l(mi, lo, me, hi, xh, mx, r) : Wr.Dec<FMF.Req>}:
  match r:
    case Wr.Got{l, +s}:
      {==}
    case Wr.Bad{}:
      {==}

def mfm.effort_mx(mi: Maybe<&2, Maybe<&2, Nat>>, lo: Maybe<&2, Maybe<&2, Nat>>, me: Maybe<&2, Maybe<&2, Nat>>, hi: Maybe<&2, Maybe<&2, Nat>>, xh: Maybe<&2, Maybe<&2, Nat>>, r: Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>) -> {ModelFacts.mfr.get_effort.mx(mi, lo, me, hi, xh, r) == FMF.get_effort.mx(mi, lo, me, hi, xh, r) : Wr.Dec<FMF.Req>}:
  match r:
    case Wr.Got{mx, +s}:
      %mfm.elv(Wr.get_nat(s)) : {ModelFacts.mfr.get_effort.l(mi, lo, me, hi, xh, mx, ModelFacts.mfr.get_elv(Wr.get_nat(s))) == FMF.get_effort.l(mi, lo, me, hi, xh, mx, _) : Wr.Dec<FMF.Req>}
      mfm.effort_l(mi, lo, me, hi, xh, mx, ModelFacts.mfr.get_elv(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def mfm.effort_xh(mi: Maybe<&2, Maybe<&2, Nat>>, lo: Maybe<&2, Maybe<&2, Nat>>, me: Maybe<&2, Maybe<&2, Nat>>, hi: Maybe<&2, Maybe<&2, Nat>>, r: Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>) -> {ModelFacts.mfr.get_effort.xh(mi, lo, me, hi, r) == FMF.get_effort.xh(mi, lo, me, hi, r) : Wr.Dec<FMF.Req>}:
  match r:
    case Wr.Got{xh, +s}:
      %mfm.ent(Wr.get_nat(s)) : {ModelFacts.mfr.get_effort.mx(mi, lo, me, hi, xh, ModelFacts.mfr.get_ent(Wr.get_nat(s))) == FMF.get_effort.mx(mi, lo, me, hi, xh, _) : Wr.Dec<FMF.Req>}
      mfm.effort_mx(mi, lo, me, hi, xh, ModelFacts.mfr.get_ent(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def mfm.effort_hi(mi: Maybe<&2, Maybe<&2, Nat>>, lo: Maybe<&2, Maybe<&2, Nat>>, me: Maybe<&2, Maybe<&2, Nat>>, r: Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>) -> {ModelFacts.mfr.get_effort.hi(mi, lo, me, r) == FMF.get_effort.hi(mi, lo, me, r) : Wr.Dec<FMF.Req>}:
  match r:
    case Wr.Got{hi, +s}:
      %mfm.ent(Wr.get_nat(s)) : {ModelFacts.mfr.get_effort.xh(mi, lo, me, hi, ModelFacts.mfr.get_ent(Wr.get_nat(s))) == FMF.get_effort.xh(mi, lo, me, hi, _) : Wr.Dec<FMF.Req>}
      mfm.effort_xh(mi, lo, me, hi, ModelFacts.mfr.get_ent(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def mfm.effort_me(mi: Maybe<&2, Maybe<&2, Nat>>, lo: Maybe<&2, Maybe<&2, Nat>>, r: Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>) -> {ModelFacts.mfr.get_effort.me(mi, lo, r) == FMF.get_effort.me(mi, lo, r) : Wr.Dec<FMF.Req>}:
  match r:
    case Wr.Got{me, +s}:
      %mfm.ent(Wr.get_nat(s)) : {ModelFacts.mfr.get_effort.hi(mi, lo, me, ModelFacts.mfr.get_ent(Wr.get_nat(s))) == FMF.get_effort.hi(mi, lo, me, _) : Wr.Dec<FMF.Req>}
      mfm.effort_hi(mi, lo, me, ModelFacts.mfr.get_ent(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def mfm.effort_lo(mi: Maybe<&2, Maybe<&2, Nat>>, r: Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>) -> {ModelFacts.mfr.get_effort.lo(mi, r) == FMF.get_effort.lo(mi, r) : Wr.Dec<FMF.Req>}:
  match r:
    case Wr.Got{lo, +s}:
      %mfm.ent(Wr.get_nat(s)) : {ModelFacts.mfr.get_effort.me(mi, lo, ModelFacts.mfr.get_ent(Wr.get_nat(s))) == FMF.get_effort.me(mi, lo, _) : Wr.Dec<FMF.Req>}
      mfm.effort_me(mi, lo, ModelFacts.mfr.get_ent(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def mfm.effort(r: Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>) -> {ModelFacts.mfr.get_effort(r) == FMF.get_effort(r) : Wr.Dec<FMF.Req>}:
  match r:
    case Wr.Got{mi, +s}:
      %mfm.ent(Wr.get_nat(s)) : {ModelFacts.mfr.get_effort.lo(mi, ModelFacts.mfr.get_ent(Wr.get_nat(s))) == FMF.get_effort.lo(mi, _) : Wr.Dec<FMF.Req>}
      mfm.effort_lo(mi, ModelFacts.mfr.get_ent(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def mfm.row_k(m: Maybe<&2, Nat>, t: Nat, r: Wr.Dec<Nat>) -> {ModelFacts.mfr.get_row.k(m, t, r) == FMF.get_row.k(m, t, r) : Wr.Dec<Fx.PRow>}:
  match r:
    case Wr.Got{k, +s}:
      {==}
    case Wr.Bad{}:
      {==}

def mfm.row_t(m: Maybe<&2, Nat>, r: Wr.Dec<Nat>) -> {ModelFacts.mfr.get_row.t(m, r) == FMF.get_row.t(m, r) : Wr.Dec<Fx.PRow>}:
  match r:
    case Wr.Got{t, +s}:
      mfm.row_k(m, t, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def mfm.row_m(r: Wr.Dec<Maybe<&2, Nat>>) -> {ModelFacts.mfr.get_row.m(r) == FMF.get_row.m(r) : Wr.Dec<Fx.PRow>}:
  match r:
    case Wr.Got{m, +s}:
      mfm.row_t(m, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def mfm.row(+s: String) -> {ModelFacts.mfr.get_row(s) == FMF.get_row(s) : Wr.Dec<Fx.PRow>}:
  %mfm.mnat(Wr.get_nat(s)) : {ModelFacts.mfr.get_row.m(ModelFacts.mfr.get_mnat(Wr.get_nat(s))) == FMF.get_row.m(_) : Wr.Dec<Fx.PRow>}
  mfm.row_m(ModelFacts.mfr.get_mnat(Wr.get_nat(s)))

def mfm.rows_cons(x: Fx.PRow, r: Wr.Dec<List<&2, Fx.PRow>>) -> {ModelFacts.mfr.get_rows.cons(x, r) == FMF.get_rows.cons(x, r) : Wr.Dec<List<&2, Fx.PRow>>}:
  match r:
    case Wr.Got{xs, +s}:
      {==}
    case Wr.Bad{}:
      {==}

def mfm.rows_go(n: Nat, cur: Wr.Dec<Fx.PRow>) -> {ModelFacts.mfr.get_rows.go(n, cur) == FMF.get_rows.go(n, cur) : Wr.Dec<List<&2, Fx.PRow>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n++k:
      match cur:
        case Wr.Got{+x, +s}:
          %mfm.row(s) : {ModelFacts.mfr.get_rows.cons(x, ModelFacts.mfr.get_rows.go(k, ModelFacts.mfr.get_row(s))) == FMF.get_rows.cons(x, FMF.get_rows.go(k, _)) : Wr.Dec<List<&2, Fx.PRow>>}
          %mfm.rows_go(k, ModelFacts.mfr.get_row(s)) : {ModelFacts.mfr.get_rows.cons(x, ModelFacts.mfr.get_rows.go(k, ModelFacts.mfr.get_row(s))) == FMF.get_rows.cons(x, _) : Wr.Dec<List<&2, Fx.PRow>>}
          mfm.rows_cons(x, ModelFacts.mfr.get_rows.go(k, ModelFacts.mfr.get_row(s)))
        case Wr.Bad{}:
          {==}

def mfm.rows_count(n: Nat, +s: String) -> {ModelFacts.mfr.get_rows.count(n, s) == FMF.get_rows.count(n, s) : Wr.Dec<List<&2, Fx.PRow>>}:
  match n:
    case 0n:
      {==}
    case 1n++k:
      %mfm.row(s) : {ModelFacts.mfr.get_rows.go(k, ModelFacts.mfr.get_row(s)) == FMF.get_rows.go(k, _) : Wr.Dec<List<&2, Fx.PRow>>}
      mfm.rows_go(k, ModelFacts.mfr.get_row(s))

def mfm.rows(r: Wr.Dec<Nat>) -> {ModelFacts.mfr.get_rows(r) == FMF.get_rows(r) : Wr.Dec<List<&2, Fx.PRow>>}:
  match r:
    case Wr.Got{n, +s}:
      mfm.rows_count(n, s)
    case Wr.Bad{}:
      {==}

def mfm.price_t(rows: List<&2, Fx.PRow>, m: Nat, r: Wr.Dec<Nat>) -> {ModelFacts.mfr.get_price.t(rows, m, r) == FMF.get_price.t(rows, m, r) : Wr.Dec<FMF.Req>}:
  match r:
    case Wr.Got{t, +s}:
      {==}
    case Wr.Bad{}:
      {==}

def mfm.price_m(rows: List<&2, Fx.PRow>, r: Wr.Dec<Nat>) -> {ModelFacts.mfr.get_price.m(rows, r) == FMF.get_price.m(rows, r) : Wr.Dec<FMF.Req>}:
  match r:
    case Wr.Got{m, +s}:
      mfm.price_t(rows, m, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def mfm.price(r: Wr.Dec<List<&2, Fx.PRow>>) -> {ModelFacts.mfr.get_price(r) == FMF.get_price(r) : Wr.Dec<FMF.Req>}:
  match r:
    case Wr.Got{rows, +s}:
      mfm.price_m(rows, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def mfm.req_tag(t: Nat, +s: String) -> {ModelFacts.mfr.get_req.tag(t, s) == FMF.get_req.tag(t, s) : Wr.Dec<FMF.Req>}:
  match t:
    case 0n:
      %mfm.ans(Wr.get_nat(s)) : {ModelFacts.mfr.get_flag(ModelFacts.mfr.get_ans(Wr.get_nat(s))) == FMF.get_flag(_) : Wr.Dec<FMF.Req>}
      mfm.flag(ModelFacts.mfr.get_ans(Wr.get_nat(s)))
    case 1n:
      %mfm.mbool(Wr.get_nat(s)) : {ModelFacts.mfr.get_adaptive(ModelFacts.mfr.get_mbool(Wr.get_nat(s))) == FMF.get_adaptive(_) : Wr.Dec<FMF.Req>}
      mfm.adaptive(ModelFacts.mfr.get_mbool(Wr.get_nat(s)))
    case 2n:
      %mfm.ent(Wr.get_nat(s)) : {ModelFacts.mfr.get_effort(ModelFacts.mfr.get_ent(Wr.get_nat(s))) == FMF.get_effort(_) : Wr.Dec<FMF.Req>}
      mfm.effort(ModelFacts.mfr.get_ent(Wr.get_nat(s)))
    case 3n:
      %mfm.rows(Wr.get_nat(s)) : {ModelFacts.mfr.get_price(ModelFacts.mfr.get_rows(Wr.get_nat(s))) == FMF.get_price(_) : Wr.Dec<FMF.Req>}
      mfm.price(ModelFacts.mfr.get_rows(Wr.get_nat(s)))
    case 4n+p:
      {==}

def mfm.req_go(r: Wr.Dec<Nat>) -> {ModelFacts.mfr.get_req.go(r) == FMF.get_req.go(r) : Wr.Dec<FMF.Req>}:
  match r:
    case Wr.Got{t, +s}:
      mfm.req_tag(t, s)
    case Wr.Bad{}:
      {==}

def mfm.if_none(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def mfm.some_none(-A: Data, -x: A, -G: Type, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  %e : mfm.if_none(A, _, G)
  Unit{}

def mfm.end(b: Bool, -q: FMF.Req, no: {ModelFacts.mfr.end(b, q) == None{} : Maybe<&2, FMF.Req>}) -> {FMF.run.end(b, q) == SCon{'E', SCon{' ', "model facts: malformed request"}} : String}:
  match b:
    case True{}:
      mfm.some_none(FMF.Req, q, {FMF.answer(q) == SCon{'E', SCon{' ', "model facts: malformed request"}} : String}, no)
    case False{}:
      {==}

def mfm.whole(r: Wr.Dec<FMF.Req>, no: {ModelFacts.mfr.whole(r) == None{} : Maybe<&2, FMF.Req>}) -> {FMF.run(r) == SCon{'E', SCon{' ', "model facts: malformed request"}} : String}:
  match r:
    case Wr.Got{q, s}:
      mfm.end(Wr.end(s), q, no)
    case Wr.Bad{}:
      {==}

def ModelFacts.model_facts_ffi_malformed_exact(s, no):
  %mfm.req_go(Wr.get_nat(s)) : {FMF.run(_) == SCon{'E', SCon{' ', "model facts: malformed request"}} : String}
  mfm.whole(ModelFacts.mfr.get_req.go(Wr.get_nat(s)), no)
