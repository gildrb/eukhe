# eukhe: the proof of LAW failover_wait_saturation_exact

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

# max(a, b) > x when b > x
def rx.gt_max(+a: Nat, +b: Nat, +x: Nat, hb: {Nat.is_gt(b, x) == True{} : Bool}) -> {Nat.is_gt(Nat.max(a, b), x) == True{} : Bool}:
  match a b x:
    case 0n b x:
      hb
    case 1n+p 0n 0n:
      LLogicLogic.rp.absurdF({Nat.is_gt(1n+p, 0n) == True{} : Bool}, hb)
    case 1n+p 0n 1n+r:
      LLogicLogic.rp.absurdF({Nat.is_gt(1n+p, 1n+r) == True{} : Bool}, hb)
    case 1n+p 1n+q 0n:
      {==}
    case 1n+p 1n+q 1n+r:
      rx.gt_max(p, q, r, hb)

# Saturated server waits
# ----------------------

def rx.cw_len(ts: List<&2, R.Tried>, +c: Nat) -> {R.length(Retry.rs.cap_waits(ts, c)) == R.length(ts) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case t <> +rest:
      match t:
        case R.Tried{a, w}:
          %Equal.sym(Nat, R.length(Retry.rs.cap_waits(rest, c)), R.length(rest), rx.cw_len(rest, c)) : {1n+_ == 1n+R.length(rest) : Nat}
          {==}

def rx.cw_seen(+x: Nat, ts: List<&2, R.Tried>, +c: Nat) -> {R.seen(x, Retry.rs.cap_waits(ts, c)) == R.seen(x, ts) : Bool}:
  match ts:
    case Nil{}:
      {==}
    case t <> +rest:
      match t:
        case R.Tried{+a, w}:
          %Equal.sym(Bool, R.seen(x, Retry.rs.cap_waits(rest, c)), R.seen(x, rest), rx.cw_seen(x, rest, c)) : {Bool.or(Nat.is_eq(a, x), _) == Bool.or(Nat.is_eq(a, x), R.seen(x, rest)) : Bool}
          {==}

def rx.cw_all(xs: List<&2, Nat>, +ts: List<&2, R.Tried>, +c: Nat) -> {R.all_seen.go(xs, Retry.rs.cap_waits(ts, c)) == R.all_seen.go(xs, ts) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, R.seen(x, Retry.rs.cap_waits(ts, c)), R.seen(x, ts), rx.cw_seen(x, ts, c)) : {Bool.and(_, R.all_seen.go(rest, Retry.rs.cap_waits(ts, c))) == Bool.and(R.seen(x, ts), R.all_seen.go(rest, ts)) : Bool}
      %Equal.sym(Bool, R.all_seen.go(rest, Retry.rs.cap_waits(ts, c)), R.all_seen.go(rest, ts), rx.cw_all(rest, ts, c)) : {Bool.and(R.seen(x, ts), _) == Bool.and(R.seen(x, ts), R.all_seen.go(rest, ts)) : Bool}
      {==}

def rx.cw_last(ts: List<&2, R.Tried>, +a: Nat, -w: Maybe<&2, Nat>, -v: Maybe<&2, Nat>, +c: Nat) -> {R.Tried.at(R.last.go(Retry.rs.cap_waits(ts, c), R.Tried{a, v})) == R.Tried.at(R.last.go(ts, R.Tried{a, w})) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case t <> +rest:
      match t:
        case R.Tried{b, u}:
          rx.cw_last(rest, b, u, Retry.rs.cap_wait(u, c), c)

def rx.cw_pick(hit: Bool, w: Maybe<&2, Nat>, +acc: Nat, +c: Nat) -> {Nat.min(R.server.pick(hit, w, acc), c) == R.server.pick(hit, Retry.rs.cap_wait(w, c), Nat.min(acc, c)) : Nat}:
  match hit:
    case True{}:
      match w:
        case Some{y}:
          {==}
        case None{}:
          {==}
    case False{}:
      {==}

# the server's wait over saturated waits is the saturated server's wait
def rx.cw_server(+x: Nat, ts: List<&2, R.Tried>, +c: Nat, +acc: Nat) -> {R.server.go(x, Retry.rs.cap_waits(ts, c), Nat.min(acc, c)) == Nat.min(R.server.go(x, ts, acc), c) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case t <> +rest:
      match t:
        case R.Tried{+a, +w}:
          %rx.cw_pick(Nat.is_eq(a, x), w, acc, c) : {R.server.go(x, Retry.rs.cap_waits(rest, c), _) == Nat.min(R.server.go(x, rest, R.server.pick(Nat.is_eq(a, x), w, acc)), c) : Nat}
          rx.cw_server(x, rest, c, R.server.pick(Nat.is_eq(a, x), w, acc))

def rx.cw_fresh(xs: List<&2, Nat>, +ts: List<&2, R.Tried>, +c: Nat) -> {R.pick.fresh(xs, Retry.rs.cap_waits(ts, c)) == R.pick.fresh(xs, ts) : Maybe<&2, R.Switch>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, R.seen(x, Retry.rs.cap_waits(ts, c)), R.seen(x, ts), rx.cw_seen(x, ts, c)) : {R.pick.sel(Bool.not(_), R.Switch{x, 0n}, R.pick.fresh(rest, Retry.rs.cap_waits(ts, c))) == R.pick.fresh(x <> rest, ts) : Maybe<&2, R.Switch>}
      %Equal.sym(Maybe<&2, R.Switch>, R.pick.fresh(rest, Retry.rs.cap_waits(ts, c)), R.pick.fresh(rest, ts), rx.cw_fresh(rest, ts, c)) : {R.pick.sel(Bool.not(R.seen(x, ts)), R.Switch{x, 0n}, _) == R.pick.fresh(x <> rest, ts) : Maybe<&2, R.Switch>}
      {==}

def rx.not_le_of_gt(c: Cmp, e: {Cmp.is_gt(c) == True{} : Bool}) -> {Cmp.is_le(c) == False{} : Bool}:
  match c:
    case LT{}:
      LLogicLogic.rp.absurdF({True{} == False{} : Bool}, e)
    case EQ{}:
      LLogicLogic.rp.absurdF({True{} == False{} : Bool}, e)
    case GT{}:
      {==}

# a wait past max picks nobody: the pick goes to the rest
def rx.sel_off(+d: Nat, +m: Nat, +s: R.Switch, r: Maybe<&2, R.Switch>, h: {Nat.is_gt(d, m) == True{} : Bool}) -> {R.pick.sel(Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, m)), s, r) == r : Maybe<&2, R.Switch>}:
  %Equal.sym(Bool, Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, m)), False{}, LA.rx.and_f(Nat.is_gt(d, 0n), Nat.is_le(d, m), rx.not_le_of_gt(Nat.cmp(d, m), h))) : {R.pick.sel(_, s, r) == r : Maybe<&2, R.Switch>}
  {==}

def rx.cw_sel(gt: Bool, +w: Nat, +b: Nat, +m: Nat, +c: Nat, +x: Nat, +r: Maybe<&2, R.Switch>, +e: {Nat.is_gt(w, m) == gt : Bool}, +hc: {Nat.is_gt(c, m) == True{} : Bool}) -> {R.pick.sel(Bool.and(Nat.is_gt(Nat.max(b, Nat.min(w, c)), 0n), Nat.is_le(Nat.max(b, Nat.min(w, c)), m)), R.Switch{x, Nat.max(b, Nat.min(w, c))}, r) == R.pick.sel(Bool.and(Nat.is_gt(Nat.max(b, w), 0n), Nat.is_le(Nat.max(b, w), m)), R.Switch{x, Nat.max(b, w)}, r) : Maybe<&2, R.Switch>}:
  match gt:
    case False{}:
      +le = LA.rx.le_gt(w, m, c, LA.rx.le_of_not_gt(Nat.cmp(w, m), e), hc)
      %Equal.sym(Nat, Nat.min(w, c), w, LA.rx.min_l(w, c, le)) : {R.pick.sel(Bool.and(Nat.is_gt(Nat.max(b, _), 0n), Nat.is_le(Nat.max(b, _), m)), R.Switch{x, Nat.max(b, _)}, r) == R.pick.sel(Bool.and(Nat.is_gt(Nat.max(b, w), 0n), Nat.is_le(Nat.max(b, w), m)), R.Switch{x, Nat.max(b, w)}, r) : Maybe<&2, R.Switch>}
      {==}
    case True{}:
      +d1 = Nat.max(b, Nat.min(w, c))
      +d2 = Nat.max(b, w)
      +off1 = rx.sel_off(d1, m, R.Switch{x, d1}, r, rx.gt_max(b, Nat.min(w, c), m, LA.rx.gt_min(w, c, m, e, hc)))
      +off2 = rx.sel_off(d2, m, R.Switch{x, d2}, r, rx.gt_max(b, w, m, e))
      Equal.trans(Maybe<&2, R.Switch>, R.pick.sel(Bool.and(Nat.is_gt(d1, 0n), Nat.is_le(d1, m)), R.Switch{x, d1}, r), r, R.pick.sel(Bool.and(Nat.is_gt(d2, 0n), Nat.is_le(d2, m)), R.Switch{x, d2}, r), off1, Equal.sym(Maybe<&2, R.Switch>, R.pick.sel(Bool.and(Nat.is_gt(d2, 0n), Nat.is_le(d2, m)), R.Switch{x, d2}, r), r, off2))

def rx.cw_back(xs: List<&2, Nat>, +ts: List<&2, R.Tried>, +b: Nat, +m: Nat, +c: Nat, +hc: {Nat.is_gt(c, m) == True{} : Bool}) -> {R.pick.back(xs, Retry.rs.cap_waits(ts, c), b, m) == R.pick.back(xs, ts, b, m) : Maybe<&2, R.Switch>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      +W = R.server(x, ts)
      %Equal.sym(Nat, R.server.go(x, Retry.rs.cap_waits(ts, c), Nat.min(0n, c)), Nat.min(W, c), rx.cw_server(x, ts, c, 0n)) : {R.pick.sel(Bool.and(Nat.is_gt(Nat.max(b, _), 0n), Nat.is_le(Nat.max(b, _), m)), R.Switch{x, Nat.max(b, _)}, R.pick.back(rest, Retry.rs.cap_waits(ts, c), b, m)) == R.pick.back(x <> rest, ts, b, m) : Maybe<&2, R.Switch>}
      %Equal.sym(Maybe<&2, R.Switch>, R.pick.back(rest, Retry.rs.cap_waits(ts, c), b, m), R.pick.back(rest, ts, b, m), rx.cw_back(rest, ts, b, m, c, hc)) : {R.pick.sel(Bool.and(Nat.is_gt(Nat.max(b, Nat.min(W, c)), 0n), Nat.is_le(Nat.max(b, Nat.min(W, c)), m)), R.Switch{x, Nat.max(b, Nat.min(W, c))}, _) == R.pick.back(x <> rest, ts, b, m) : Maybe<&2, R.Switch>}
      rx.cw_sel(Nat.is_gt(W, m), W, b, m, c, x, R.pick.back(rest, ts, b, m), {==}, hc)

def rx.cw_mode(all: Bool, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy, +c: Nat, +hc: {Nat.is_gt(c, R.Policy.max(p)) == True{} : Bool}) -> {R.next.mode(all, last, len, Retry.rs.cap_waits(ts, c), p) == R.next.mode(all, last, len, ts, p) : Maybe<&2, R.Switch>}:
  match all:
    case True{}:
      %Equal.sym(Nat, R.length(Retry.rs.cap_waits(ts, c)), R.length(ts), rx.cw_len(ts, c)) : {R.pick.back(R.order(last, len), Retry.rs.cap_waits(ts, c), R.double(Nat.sub(_, len), R.Policy.base(p), R.Policy.max(p)), R.Policy.max(p)) == R.next.mode(True{}, last, len, ts, p) : Maybe<&2, R.Switch>}
      rx.cw_back(R.order(last, len), ts, R.backoff(p, len, ts), R.Policy.max(p), c, hc)
    case False{}:
      rx.cw_fresh(R.order(last, len), ts, c)

def rx.cw_budget(ok: Bool, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy, +c: Nat, hc: {Nat.is_gt(c, R.Policy.max(p)) == True{} : Bool}) -> {R.next.budget(ok, last, len, Retry.rs.cap_waits(ts, c), p) == R.next.budget(ok, last, len, ts, p) : Maybe<&2, R.Switch>}:
  match ok:
    case True{}:
      %Equal.sym(Bool, R.all_seen.go(R.upto(len, 0n), Retry.rs.cap_waits(ts, c)), R.all_seen(len, ts), rx.cw_all(R.upto(len, 0n), ts, c)) : {R.next.mode(_, last, len, Retry.rs.cap_waits(ts, c), p) == R.next.mode(R.all_seen(len, ts), last, len, ts, p) : Maybe<&2, R.Switch>}
      rx.cw_mode(R.all_seen(len, ts), last, len, ts, p, c, hc)
    case False{}:
      {==}

def wait_saturation_walk(+len: Nat, ts: List<&2, R.Tried>, +p: R.Policy, +c: Nat, hc: {Nat.is_gt(c, R.Policy.max(p)) == True{} : Bool}) -> {R.next(len, Retry.rs.cap_waits(ts, c), p) == R.next(len, ts, p) : Maybe<&2, R.Switch>}:
  match ts:
    case Nil{}:
      {==}
    case t <> +rest:
      match t:
        case R.Tried{+a, +w}:
          +S = R.Policy.switches(p)
          +ts2 = {R.Tried{a, Retry.rs.cap_wait(w, c)} <> Retry.rs.cap_waits(rest, c) : List<&2, R.Tried>}
          %Equal.sym(Nat, R.length(Retry.rs.cap_waits(rest, c)), R.length(rest), rx.cw_len(rest, c)) : {R.next.budget(Nat.is_le(1n+_, S), R.Tried.at(R.last.go(Retry.rs.cap_waits(rest, c), R.Tried{a, Retry.rs.cap_wait(w, c)})), len, ts2, p) == R.next(len, R.Tried{a, w} <> rest, p) : Maybe<&2, R.Switch>}
          %Equal.sym(Nat, R.Tried.at(R.last.go(Retry.rs.cap_waits(rest, c), R.Tried{a, Retry.rs.cap_wait(w, c)})), R.Tried.at(R.last.go(rest, R.Tried{a, w})), rx.cw_last(rest, a, w, Retry.rs.cap_wait(w, c), c)) : {R.next.budget(Nat.is_le(1n+R.length(rest), S), _, len, ts2, p) == R.next(len, R.Tried{a, w} <> rest, p) : Maybe<&2, R.Switch>}
          rx.cw_budget(Nat.is_le(1n+R.length(rest), S), R.Tried.at(R.last.go(rest, R.Tried{a, w})), len, R.Tried{a, w} <> rest, p, c, hc)

def Retry.failover_wait_saturation_exact(len, ts, p, c, above):
  wait_saturation_walk(len, ts, p, c, above)
