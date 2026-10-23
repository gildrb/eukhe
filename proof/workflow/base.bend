# eukhe: lemmas the proofs of area workflow share

import Base
import ../../bend/ffi_workflow.bend as FW
import ../../bend/wire.bend as Wr
import ../../bend/workflow.bend as W
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/workflow.bend as Workflow
import ../base.bend as L
import ./wfw_sts_round_trip.bend as PWfwStsRoundTrip

# ---- workflow ----

# proof_workflow: the WF laws (LAWS.bend section workflow) of the dynamic
# workflow scheduler model in bend/workflow.bend.
#
# Taking and giving a unit move it between the two counters of a pool,
# so the pool's size stays; the counters laws go by induction on the
# events. The cache laws read the hit; the results law goes by
# induction on the items before the failed one.

def pw.add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %pw.add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def pw.take_size(p: W.Pool) -> {W.size(W.take(p)) == W.size(p) : Nat}:
  match p:
    case W.Pool{t, l}:
      match l:
        case 0n:
          {==}
        case 1n+m:
          pw.add_succ(t, m)

def pw.eq_comm(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+x 0n:
      {==}
    case 1n+x 1n+y:
      pw.eq_comm(x, y)

def pw.serves(s: W.Sts) -> {W.serves(s) == Workflow.wf_serves(s) : Bool}:
  match s:
    case W.Queued{}:
      {==}
    case W.Running{}:
      {==}
    case W.Finished{}:
      {==}
    case W.Erred{}:
      {==}
    case W.Cancelled{}:
      {==}
    case W.Cached{}:
      {==}

# a first position j of the rows from the i-th
def pw.off(i: Nat, m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{j}:
      Some{Nat.add(j, i)}

def pw.found_at(h: Bool, +i: Nat, -rf: Maybe<&2, Nat>, rw: Maybe<&2, Nat>, ih: {rf == pw.off(1n+i, rw) : Maybe<&2, Nat>}) -> {W.found.at(h, i, rf) == pw.off(i, Workflow.wf_first.at(h, rw)) : Maybe<&2, Nat>}:
  match h:
    case True{}:
      {==}
    case False{}:
      match rw:
        case None{}:
          ih
        case Some{j}:
          Equal.trans(Maybe<&2, Nat>, rf, Some{Nat.add(j, 1n+i)}, Some{1n+Nat.add(j, i)}, ih, Equal.cong(Nat, Maybe<&2, Nat>, n => Some{n}, Nat.add(j, 1n+i), 1n+Nat.add(j, i), Equal.sym(Nat, 1n+Nat.add(j, i), Nat.add(j, 1n+i), pw.add_succ(j, i))))

# the model's search from the i-th row is the spec's first position, i on
def pw.found(rs: List<&2, W.Row>, +k: Nat, +i: Nat) -> {W.found(rs, k, i) == pw.off(i, Workflow.wf_first(rs, k)) : Maybe<&2, Nat>}:
  match rs:
    case Nil{}:
      {==}
    case W.Row{+key, +s} <> +rest:
      %pw.eq_comm(key, k) : {W.found.at(Bool.and(_, W.serves(s)), i, W.found(rest, k, 1n+i)) == pw.off(i, Workflow.wf_first(W.Row{key, s} <> rest, k)) : Maybe<&2, Nat>}
      %Equal.sym(Bool, W.serves(s), Workflow.wf_serves(s), pw.serves(s)) : {W.found.at(Bool.and(Nat.is_eq(key, k), _), i, W.found(rest, k, 1n+i)) == pw.off(i, Workflow.wf_first(W.Row{key, s} <> rest, k)) : Maybe<&2, Nat>}
      pw.found_at(Bool.and(Nat.is_eq(key, k), Workflow.wf_serves(s)), i, W.found(rest, k, 1n+i), Workflow.wf_first(rest, k), pw.found(rest, k, 1n+i))

# ---- workflow_wire ----

# Place after PROOF.bend section wire: the proofs use its Laws.wire_*
# fills and wr_and_l / wr_and_r.

# a Nat that fits reads back (Laws.wire_nat_round_trip, turned around)
def pww.nat(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

# a sts reads back (turned around for rewriting)
def pww.sts(+s: W.Sts, +rest: String) -> {Wr.Got{s, rest} == FW.get_sts(FW.put_sts(s, rest)) : Wr.Dec<W.Sts>}:
  Equal.sym(Wr.Dec<W.Sts>, FW.get_sts(FW.put_sts(s, rest)), Wr.Got{s, rest}, Workflow.wfw_sts_round_trip(s, rest))

def Workflow.wfw_prior_round_trip(m, rest):
  match m:
    case None{}:
      {==}
    case Some{+s}:
      %pww.sts(s, rest) : {FW.get_prior.some(_) == Wr.Got{Some{s}, rest} : Wr.Dec<Maybe<&2, W.Sts>>}
      {==}

# a prior reads back (turned around for rewriting)
def pww.prior(+m: Maybe<&2, W.Sts>, +rest: String) -> {Wr.Got{m, rest} == FW.get_prior(FW.put_prior(m, rest)) : Wr.Dec<Maybe<&2, W.Sts>>}:
  Equal.sym(Wr.Dec<Maybe<&2, W.Sts>>, FW.get_prior(FW.put_prior(m, rest)), Wr.Got{m, rest}, Workflow.wfw_prior_round_trip(m, rest))

def Workflow.wfw_row_round_trip(r, rest, h):
  match r:
    case W.Row{+k, +s}:
      +z = rest
      %pww.nat(k, FW.put_sts(s, z), h) : {FW.get_row.go(_) == Wr.Got{W.Row{k, s}, z} : Wr.Dec<W.Row>}
      %pww.sts(s, z) : {FW.get_row.sts(k, _) == Wr.Got{W.Row{k, s}, z} : Wr.Dec<W.Row>}
      {==}

# a row reads back (turned around for rewriting)
def pww.row(+r: W.Row, +rest: String, h: {Workflow.wfw_row_fits(r) == True{} : Bool}) -> {Wr.Got{r, rest} == FW.get_row(FW.put_row(r, rest)) : Wr.Dec<W.Row>}:
  Equal.sym(Wr.Dec<W.Row>, FW.get_row(FW.put_row(r, rest)), Wr.Got{r, rest}, Workflow.wfw_row_round_trip(r, rest, h))

# the items of xs, then rest (W.Row; a copy of PROOF.bend wire's wr_items)
def pww.row_items(xs: List<&2, W.Row>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      FW.put_row(x, pww.row_items(t, rest))

def pww.row_put_go(xs: List<&2, W.Row>, -rest: String) ->
  {Wr.put_list.go(~W.Row, ~FW.put_row, xs, rest) == (List.length(&2, W.Row, xs), pww.row_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~W.Row, ~FW.put_row, t, rest), (List.length(&2, W.Row, t), pww.row_items(t, rest)), pww.row_put_go(t, rest)) : {Wr.put_list.step(~W.Row, ~FW.put_row, x, _) == (1n+List.length(&2, W.Row, t), FW.put_row(x, pww.row_items(t, rest))) : Nat & String}
      {==}

# a list is its count, then its items
def pww.row_put(+xs: List<&2, W.Row>, -rest: String) ->
  {Wr.put_list(~W.Row, ~FW.put_row, xs, rest) == Wr.put_nat(List.length(&2, W.Row, xs), pww.row_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~W.Row, ~FW.put_row, xs, rest), (List.length(&2, W.Row, xs), pww.row_items(xs, rest)), pww.row_put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, W.Row, xs), pww.row_items(xs, rest)) : String}
  {==}

# the item loop reads back x then t (wr_list_go_rt for W.Row)
def pww.row_go_rt(+t: List<&2, W.Row>, +x: W.Row, +rest: String,
  +hf: {Workflow.wfw_rows_fit(x <> t) == True{} : Bool}) ->
  {Wr.get_list.go(~W.Row, ~FW.get_row, List.length(&2, W.Row, t), FW.get_row(FW.put_row(x, pww.row_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, W.Row>>}:
  match t:
    case Nil{}:
      %pww.row(x, rest, L.wr_and_l(Workflow.wfw_row_fits(x), True{}, hf)) : {Wr.get_list.go(~W.Row, ~FW.get_row, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, W.Row>>}
      {==}
    case Con{+y, +u}:
      %pww.row(x, FW.put_row(y, pww.row_items(u, rest)), L.wr_and_l(Workflow.wfw_row_fits(x), Workflow.wfw_rows_fit(y <> u), hf)) : {Wr.get_list.go(~W.Row, ~FW.get_row, 1n+List.length(&2, W.Row, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, W.Row>>}
      %Equal.sym(Wr.Dec<List<&2, W.Row>>, Wr.get_list.go(~W.Row, ~FW.get_row, List.length(&2, W.Row, u), FW.get_row(FW.put_row(y, pww.row_items(u, rest)))), Wr.Got{y <> u, rest}, pww.row_go_rt(u, y, rest, L.wr_and_r(Workflow.wfw_row_fits(x), Workflow.wfw_rows_fit(y <> u), hf))) : {Wr.get_list.cons(W.Row, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, W.Row>>}
      {==}

def Workflow.wfw_rows_round_trip(xs, rest, h):
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, L.wr_and_l(LawsBase.wire_fits(0n), True{}, h))) : {Wr.get_list.start(~W.Row, ~FW.get_row, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, W.Row>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~W.Row, ~FW.put_row, x <> t, r), Wr.put_nat(List.length(&2, W.Row, x <> t), pww.row_items(x <> t, r)), pww.row_put(x <> t, r)) : {Wr.get_list(~W.Row, ~FW.get_row, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, W.Row>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, W.Row, x <> t), pww.row_items(x <> t, r))), Wr.Got{List.length(&2, W.Row, x <> t), pww.row_items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, W.Row, x <> t), pww.row_items(x <> t, r), L.wr_and_l(LawsBase.wire_fits(List.length(&2, W.Row, x <> t)), Workflow.wfw_rows_fit(x <> t), hh))) : {Wr.get_list.start(~W.Row, ~FW.get_row, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, W.Row>>}
      pww.row_go_rt(t, x, r, L.wr_and_r(LawsBase.wire_fits(List.length(&2, W.Row, x <> t)), Workflow.wfw_rows_fit(x <> t), hh))

# a list that fits reads back (turned around for rewriting)
def pww.rows(+xs: List<&2, W.Row>, +rest: String, h: {Bool.and(LawsBase.wire_fits(List.length(&2, W.Row, xs)), Workflow.wfw_rows_fit(xs)) == True{} : Bool}) ->
  {Wr.Got{xs, rest} == Wr.get_list(~W.Row, ~FW.get_row, Wr.put_list(~W.Row, ~FW.put_row, xs, rest)) : Wr.Dec<List<&2, W.Row>>}:
  Equal.sym(Wr.Dec<List<&2, W.Row>>, Wr.get_list(~W.Row, ~FW.get_row, Wr.put_list(~W.Row, ~FW.put_row, xs, rest)), Wr.Got{xs, rest}, Workflow.wfw_rows_round_trip(xs, rest, h))

def Workflow.wfw_pool_round_trip(p, rest, h):
  match p:
    case W.Pool{+t, +l}:
      +z = rest
      +hh = h
      %pww.nat(t, Wr.put_nat(l, z), L.wr_and_l(LawsBase.wire_fits(t), LawsBase.wire_fits(l), hh)) : {FW.get_pool.go(_) == Wr.Got{W.Pool{t, l}, z} : Wr.Dec<W.Pool>}
      %pww.nat(l, z, L.wr_and_r(LawsBase.wire_fits(t), LawsBase.wire_fits(l), hh)) : {FW.get_pool.left(t, _) == Wr.Got{W.Pool{t, l}, z} : Wr.Dec<W.Pool>}
      {==}

# a pool reads back (turned around for rewriting)
def pww.pool(+p: W.Pool, +rest: String, h: {Workflow.wfw_pool_fits(p) == True{} : Bool}) -> {Wr.Got{p, rest} == FW.get_pool(FW.put_pool(p, rest)) : Wr.Dec<W.Pool>}:
  Equal.sym(Wr.Dec<W.Pool>, FW.get_pool(FW.put_pool(p, rest)), Wr.Got{p, rest}, Workflow.wfw_pool_round_trip(p, rest, h))

def Workflow.wfw_req_round_trip(r, rest, h):
  match r:
    case FW.AdmitReq{+prior, +k, +rows, +p}:
      +z = rest
      +hh = h
      +lt = Bool.and(LawsBase.wire_fits(List.length(&2, W.Row, rows)), Workflow.wfw_rows_fit(rows))
      +h1 = L.wr_and_r(LawsBase.wire_fits(k), Bool.and(lt, Workflow.wfw_pool_fits(p)), hh)
      %pww.prior(prior, Wr.put_nat(k, Wr.put_list(~W.Row, ~FW.put_row, rows, FW.put_pool(p, z)))) : {FW.get_req.admit(_) == Wr.Got{FW.AdmitReq{prior, k, rows, p}, z} : Wr.Dec<FW.Req>}
      %pww.nat(k, Wr.put_list(~W.Row, ~FW.put_row, rows, FW.put_pool(p, z)), L.wr_and_l(LawsBase.wire_fits(k), Bool.and(lt, Workflow.wfw_pool_fits(p)), hh)) : {FW.get_req.key(prior, _) == Wr.Got{FW.AdmitReq{prior, k, rows, p}, z} : Wr.Dec<FW.Req>}
      %pww.rows(rows, FW.put_pool(p, z), L.wr_and_l(lt, Workflow.wfw_pool_fits(p), h1)) : {FW.get_req.rows(prior, k, _) == Wr.Got{FW.AdmitReq{prior, k, rows, p}, z} : Wr.Dec<FW.Req>}
      %pww.pool(p, z, L.wr_and_r(lt, Workflow.wfw_pool_fits(p), h1)) : {FW.get_req.pool(prior, k, rows, _) == Wr.Got{FW.AdmitReq{prior, k, rows, p}, z} : Wr.Dec<FW.Req>}
      {==}
    case FW.LimitsReq{+c, +m, +cap}:
      +z = rest
      +hh = h
      +h1 = L.wr_and_r(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(cap)), hh)
      %pww.nat(c, Wr.put_nat(m, Wr.put_nat(cap, z)), L.wr_and_l(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(cap)), hh)) : {FW.get_req.limits(_) == Wr.Got{FW.LimitsReq{c, m, cap}, z} : Wr.Dec<FW.Req>}
      %pww.nat(m, Wr.put_nat(cap, z), L.wr_and_l(LawsBase.wire_fits(m), LawsBase.wire_fits(cap), h1)) : {FW.get_req.max(c, _) == Wr.Got{FW.LimitsReq{c, m, cap}, z} : Wr.Dec<FW.Req>}
      %pww.nat(cap, z, L.wr_and_r(LawsBase.wire_fits(m), LawsBase.wire_fits(cap), h1)) : {FW.get_req.cap(c, m, _) == Wr.Got{FW.LimitsReq{c, m, cap}, z} : Wr.Dec<FW.Req>}
      {==}

# a req reads back (turned around for rewriting)
def pww.req(+r: FW.Req, +rest: String, h: {Workflow.wfw_req_fits(r) == True{} : Bool}) -> {Wr.Got{r, rest} == FW.get_req(FW.put_req(r, rest)) : Wr.Dec<FW.Req>}:
  Equal.sym(Wr.Dec<FW.Req>, FW.get_req(FW.put_req(r, rest)), Wr.Got{r, rest}, Workflow.wfw_req_round_trip(r, rest, h))
