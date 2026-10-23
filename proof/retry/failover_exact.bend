# eukhe: the proof of LAW failover_exact

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/nat.bend as LNat
import ./base.bend as LA

# (R3) The failover walk, exactly
# -------------------------------

def rx.ints(k: Nat, +a: Nat) -> {R.upto(k, a) == Retry.rs.ints(k, a) : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      %rx.ints(j, 1n+a) : {a <> R.upto(j, 1n+a) == a <> _ : List<&2, Nat>}
      {==}

def rx.after(+l: Nat, +n: Nat) -> {R.order(l, n) == Retry.rs.after(l, n) : List<&2, Nat>}:
  %rx.ints(Nat.sub(n, 1n+l), 1n+l) : {R.order(l, n) == List.append(&2, Nat, _, Retry.rs.ints(Nat.min(l, n), 0n)) : List<&2, Nat>}
  %rx.ints(Nat.min(l, n), 0n) : {R.order(l, n) == List.append(&2, Nat, R.upto(Nat.sub(n, 1n+l), 1n+l), _) : List<&2, Nat>}
  {==}

def rx.tried(+x: Nat, ts: List<&2, R.Tried>) -> {R.seen(x, ts) == Retry.rs.tried(x, ts) : Bool}:
  match ts:
    case Nil{}:
      {==}
    case t <> +rest:
      match t:
        case R.Tried{at, w}:
          %rx.tried(x, rest) : {Bool.or(Nat.is_eq(at, x), R.seen(x, rest)) == Bool.or(Nat.is_eq(at, x), _) : Bool}
          {==}

def rx.all(xs: List<&2, Nat>, +ts: List<&2, R.Tried>) -> {R.all_seen.go(xs, ts) == Retry.rs.all_tried(xs, ts) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %rx.tried(x, ts) : {Bool.and(R.seen(x, ts), R.all_seen.go(rest, ts)) == Bool.and(_, Retry.rs.all_tried(rest, ts)) : Bool}
      %rx.all(rest, ts) : {Bool.and(R.seen(x, ts), R.all_seen.go(rest, ts)) == Bool.and(R.seen(x, ts), _) : Bool}
      {==}

def rx.pick(hit: Bool, w: Maybe<&2, Nat>, +acc: Nat) -> {R.server.pick(hit, w, acc) == Retry.rs.wait.pick(hit, w, acc) : Nat}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def rx.wait(+x: Nat, ts: List<&2, R.Tried>, +acc: Nat) -> {R.server.go(x, ts, acc) == Retry.rs.wait(x, ts, acc) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case t <> +rest:
      match t:
        case R.Tried{+a, +w}:
          %rx.pick(Nat.is_eq(a, x), w, acc) : {R.server.go(x, rest, R.server.pick(Nat.is_eq(a, x), w, acc)) == Retry.rs.wait(x, rest, _) : Nat}
          rx.wait(x, rest, R.server.pick(Nat.is_eq(a, x), w, acc))

def rx.sel(ok: Bool, +s: R.Switch, r: Maybe<&2, R.Switch>) -> {R.pick.sel(ok, s, r) == Retry.rs.first(ok, s, r) : Maybe<&2, R.Switch>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def rx.fresh(xs: List<&2, Nat>, +ts: List<&2, R.Tried>) -> {R.pick.fresh(xs, ts) == Retry.rs.fresh(xs, ts) : Maybe<&2, R.Switch>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %rx.tried(x, ts) : {R.pick.fresh(x <> rest, ts) == Retry.rs.first(Bool.not(_), R.Switch{x, 0n}, Retry.rs.fresh(rest, ts)) : Maybe<&2, R.Switch>}
      %rx.fresh(rest, ts) : {R.pick.fresh(x <> rest, ts) == Retry.rs.first(Bool.not(R.seen(x, ts)), R.Switch{x, 0n}, _) : Maybe<&2, R.Switch>}
      rx.sel(Bool.not(R.seen(x, ts)), R.Switch{x, 0n}, R.pick.fresh(rest, ts))

def rx.back(xs: List<&2, Nat>, +ts: List<&2, R.Tried>, +b: Nat, +m: Nat) -> {R.pick.back(xs, ts, b, m) == Retry.rs.back(xs, ts, b, m) : Maybe<&2, R.Switch>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      +d = Nat.max(b, R.server(x, ts))
      %rx.wait(x, ts, 0n) : {R.pick.back(x <> rest, ts, b, m) == Retry.rs.first(Bool.and(Nat.is_gt(Nat.max(b, _), 0n), Nat.is_le(Nat.max(b, _), m)), R.Switch{x, Nat.max(b, _)}, Retry.rs.back(rest, ts, b, m)) : Maybe<&2, R.Switch>}
      %rx.back(rest, ts, b, m) : {R.pick.back(x <> rest, ts, b, m) == Retry.rs.first(Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, m)), R.Switch{x, d}, _) : Maybe<&2, R.Switch>}
      rx.sel(Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, m)), R.Switch{x, d}, R.pick.back(rest, ts, b, m))

def rx.count(ts: List<&2, R.Tried>) -> {R.length(ts) == Retry.rs.count(ts) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case t <> +rest:
      %rx.count(rest) : {1n+R.length(rest) == 1n+_ : Nat}
      {==}

def rx.newest(ts: List<&2, R.Tried>, +t: R.Tried) -> {R.Tried.at(R.last.go(ts, t)) == Retry.rs.newest(ts, t) : Nat}:
  match ts:
    case Nil{}:
      match t:
        case R.Tried{a, w}:
          {==}
    case u <> +rest:
      rx.newest(rest, u)

# 1 + k <= s is k < s
def rx.le_succ(+k: Nat, +s: Nat) -> {Nat.is_le(1n+k, s) == Nat.is_lt(k, s) : Bool}:
  match k s:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LNat.rp.le_zero(q)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      rx.le_succ(p, q)

def rx.returns(all: Bool, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> {R.next.mode(all, last, len, ts, p) == Retry.rs.returns(all, last, len, ts, p) : Maybe<&2, R.Switch>}:
  match all:
    case True{}:
      +B = R.Policy.base(p)
      +M = R.Policy.max(p)
      %rx.after(last, len) : {R.next.mode(True{}, last, len, ts, p) == Retry.rs.back(_, ts, Nat.min(Retry.rs.twice(Nat.sub(Retry.rs.count(ts), len), B), M), M) : Maybe<&2, R.Switch>}
      %rx.count(ts) : {R.next.mode(True{}, last, len, ts, p) == Retry.rs.back(R.order(last, len), ts, Nat.min(Retry.rs.twice(Nat.sub(_, len), B), M), M) : Maybe<&2, R.Switch>}
      %LA.rx.double(Nat.sub(R.length(ts), len), B, M) : {R.next.mode(True{}, last, len, ts, p) == Retry.rs.back(R.order(last, len), ts, _, M) : Maybe<&2, R.Switch>}
      rx.back(R.order(last, len), ts, R.backoff(p, len, ts), M)
    case False{}:
      %rx.after(last, len) : {R.next.mode(False{}, last, len, ts, p) == Retry.rs.fresh(_, ts) : Maybe<&2, R.Switch>}
      rx.fresh(R.order(last, len), ts)

def rx.budget(ok: Bool, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> {R.next.budget(ok, last, len, ts, p) == Retry.rs.budget(ok, last, len, ts, p) : Maybe<&2, R.Switch>}:
  match ok:
    case True{}:
      %rx.ints(len, 0n) : {R.next.budget(True{}, last, len, ts, p) == Retry.rs.returns(Retry.rs.all_tried(_, ts), last, len, ts, p) : Maybe<&2, R.Switch>}
      %rx.all(R.upto(len, 0n), ts) : {R.next.budget(True{}, last, len, ts, p) == Retry.rs.returns(_, last, len, ts, p) : Maybe<&2, R.Switch>}
      rx.returns(R.all_seen.go(R.upto(len, 0n), ts), last, len, ts, p)
    case False{}:
      {==}

def failover_exact(+len: Nat, ts: List<&2, R.Tried>, +p: R.Policy) -> {R.next(len, ts, p) == Retry.rs.next(len, ts, p) : Maybe<&2, R.Switch>}:
  match ts:
    case Nil{}:
      {==}
    case +t <> +rest:
      +S = R.Policy.switches(p)
      %rx.newest(rest, t) : {R.next(len, t <> rest, p) == Retry.rs.budget(Nat.is_lt(Retry.rs.count(rest), S), _, len, t <> rest, p) : Maybe<&2, R.Switch>}
      %rx.count(rest) : {R.next(len, t <> rest, p) == Retry.rs.budget(Nat.is_lt(_, S), R.Tried.at(R.last.go(rest, t)), len, t <> rest, p) : Maybe<&2, R.Switch>}
      %rx.le_succ(R.length(rest), S) : {R.next(len, t <> rest, p) == Retry.rs.budget(_, R.Tried.at(R.last.go(rest, t)), len, t <> rest, p) : Maybe<&2, R.Switch>}
      rx.budget(Nat.is_le(R.length(t <> rest), S), R.Tried.at(R.last.go(rest, t)), len, t <> rest, p)

def Retry.failover_exact(len, ts, p):
  failover_exact(len, ts, p)
