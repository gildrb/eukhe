# eukhe: lemmas the proofs of the failover walk share (area retry, R3):
# the model's helpers are the laws' (seen is rs.tried, server is rs.wait,
# length is rs.count, the newest attempt is rs.newest); a switch is the
# fresh pick or the return pick over the chain order after the provider
# that just failed (fw.split); the chain order holds every provider of the
# chain but that one, each at its rs.rank, and nothing past the chain; a
# pick over it is the first one it allows (fw.*_nearest, fw.*_some).

import Base
import ../../../bend/retry.bend as R
import ../../../laws/retry.bend as Retry
import ../../base/bool.bend as LBool
import ../../base/logic/bool.bend as LLogicBool
import ../../base/logic/logic.bend as LLogicLogic
import ../../base/logic/nat.bend as LLogicNat
import ../../base/nat.bend as LNat
import ../../base/retry.bend as LRetry
import ../base.bend as LA

# The model's helpers are the laws'
# ---------------------------------

def fw.tried(+x: Nat, ts: List<&2, R.Tried>) -> {R.seen(x, ts) == Retry.rs.tried(x, ts) : Bool}:
  match ts:
    case Nil{}:
      {==}
    case t <> +rest:
      match t:
        case R.Tried{at, w}:
          %fw.tried(x, rest) : {Bool.or(Nat.is_eq(at, x), R.seen(x, rest)) == Bool.or(Nat.is_eq(at, x), _) : Bool}
          {==}

def fw.ints(k: Nat, +a: Nat) -> {R.upto(k, a) == Retry.rs.ints(k, a) : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      %fw.ints(j, 1n+a) : {a <> R.upto(j, 1n+a) == a <> _ : List<&2, Nat>}
      {==}

# the all-seen walk over a, ..., a+k-1 (hit: whether a was tried) is the
# laws' all-tried test of those providers
def fw.all(k: Nat, hit: Bool, +a: Nat, +ts: List<&2, R.Tried>, e: {R.seen(a, ts) == hit : Bool}) -> {R.seen_run(k, hit, a, ts) == Retry.rs.all_tried(Retry.rs.ints(k, a), ts) : Bool}:
  match k hit:
    case 0n h:
      {==}
    case 1n+j False{}:
      %fw.tried(a, ts) : {False{} == Bool.and(_, Retry.rs.all_tried(Retry.rs.ints(j, 1n+a), ts)) : Bool}
      %Equal.sym(Bool, R.seen(a, ts), False{}, e) : {False{} == Bool.and(_, Retry.rs.all_tried(Retry.rs.ints(j, 1n+a), ts)) : Bool}
      {==}
    case 1n+j True{}:
      %fw.tried(a, ts) : {R.seen_run(j, R.seen(1n+a, ts), 1n+a, ts) == Bool.and(_, Retry.rs.all_tried(Retry.rs.ints(j, 1n+a), ts)) : Bool}
      %Equal.sym(Bool, R.seen(a, ts), True{}, e) : {R.seen_run(j, R.seen(1n+a, ts), 1n+a, ts) == Bool.and(_, Retry.rs.all_tried(Retry.rs.ints(j, 1n+a), ts)) : Bool}
      fw.all(j, R.seen(1n+a, ts), 1n+a, ts, {==})

# the model's all-seen test is the laws' all-tried test of the chain
def fw.all_seen(+len: Nat, +ts: List<&2, R.Tried>) -> {R.all_seen(len, ts) == Retry.rs.all_tried(Retry.rs.ints(len, 0n), ts) : Bool}:
  fw.all(len, R.seen(0n, ts), 0n, ts, {==})

def fw.pick(hit: Bool, w: Maybe<&2, Nat>, +acc: Nat) -> {R.server.pick(hit, w, acc) == Retry.rs.wait.pick(hit, w, acc) : Nat}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def fw.wait(+x: Nat, ts: List<&2, R.Tried>, +acc: Nat) -> {R.server.go(x, ts, acc) == Retry.rs.wait(x, ts, acc) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case t <> +rest:
      match t:
        case R.Tried{+a, +w}:
          %fw.pick(Nat.is_eq(a, x), w, acc) : {R.server.go(x, rest, R.server.pick(Nat.is_eq(a, x), w, acc)) == Retry.rs.wait(x, rest, _) : Nat}
          fw.wait(x, rest, R.server.pick(Nat.is_eq(a, x), w, acc))

def fw.count(ts: List<&2, R.Tried>) -> {R.length(ts) == Retry.rs.count(ts) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case t <> +rest:
      %fw.count(rest) : {1n+R.length(rest) == 1n+_ : Nat}
      {==}

def fw.newest(ts: List<&2, R.Tried>, +t: R.Tried) -> {R.Tried.at(R.last.go(ts, t)) == Retry.rs.newest(ts, t) : Nat}:
  match ts:
    case Nil{}:
      match t:
        case R.Tried{a, w}:
          {==}
    case u <> +rest:
      fw.newest(rest, u)

# 1 + k <= s is k < s
def fw.le_succ(+k: Nat, +s: Nat) -> {Nat.is_le(1n+k, s) == Nat.is_lt(k, s) : Bool}:
  match k s:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LNat.rp.le_zero(q)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      fw.le_succ(p, q)

# the backoff of a return is R3's: the base doubled per attempt past the
# first len, at most max
def fw.backoff(+sw: Nat, +b: Nat, +m: Nat, +len: Nat, +ts: List<&2, R.Tried>) -> {R.backoff(R.Policy{sw, b, m}, len, ts) == Nat.min(Retry.rs.twice(Nat.sub(Retry.rs.count(ts), len), b), m) : Nat}:
  %fw.count(ts) : {R.backoff(R.Policy{sw, b, m}, len, ts) == Nat.min(Retry.rs.twice(Nat.sub(_, len), b), m) : Nat}
  LA.rx.double(Nat.sub(R.length(ts), len), b, m)

# the return wait of x is R3's
def fw.return_wait(+x: Nat, +sw: Nat, +b: Nat, +m: Nat, +len: Nat, +ts: List<&2, R.Tried>) -> {Nat.max(R.backoff(R.Policy{sw, b, m}, len, ts), R.server(x, ts)) == Retry.rs.return_wait(x, len, ts, b, m) : Nat}:
  %fw.wait(x, ts, 0n) : {Nat.max(R.backoff(R.Policy{sw, b, m}, len, ts), R.server(x, ts)) == Nat.max(Nat.min(Retry.rs.twice(Nat.sub(Retry.rs.count(ts), len), b), m), _) : Nat}
  %fw.backoff(sw, b, m, len, ts) : {Nat.max(R.backoff(R.Policy{sw, b, m}, len, ts), R.server(x, ts)) == Nat.max(_, R.server(x, ts)) : Nat}
  {==}

# The provider that just failed was tried
# ---------------------------------------

def fw.or_r(a: Bool, -b: Bool, eb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      eb

def fw.last_seen(ts: List<&2, R.Tried>, +t: R.Tried) -> {R.seen(R.Tried.at(R.last.go(ts, t)), t <> ts) == True{} : Bool}:
  match ts:
    case Nil{}:
      match t:
        case R.Tried{+a, w}:
          %Equal.sym(Bool, Nat.is_eq(a, a), True{}, LNat.child.pc.eq_refl(a)) : {Bool.or(_, R.seen(a, Nil{})) == True{} : Bool}
          {==}
    case +u <> +rest:
      match t:
        case R.Tried{+a, +w}:
          fw.or_r(Nat.is_eq(a, R.Tried.at(R.last.go(rest, u))), R.seen(R.Tried.at(R.last.go(rest, u)), u <> rest), fw.last_seen(rest, u))

def fw.seen_ne_go(c: Bool, +x: Nat, +y: Nat, +ts: List<&2, R.Tried>, ec: {Nat.is_eq(x, y) == c : Bool}, hx: {R.seen(x, ts) == True{} : Bool}, hy: {R.seen(y, ts) == False{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      +exy = LLogicNat.rp.eq_true(x, y, ec)
      +sx = Equal.trans(Bool, True{}, R.seen(x, ts), R.seen(y, ts), Equal.sym(Bool, R.seen(x, ts), True{}, hx), Equal.cong(Nat, Bool, z => R.seen(z, ts), x, y, exy))
      LLogicLogic.rp.absurdT({True{} == False{} : Bool}, Equal.trans(Bool, True{}, R.seen(y, ts), False{}, sx, hy))
    case False{}:
      {==}

# a provider tried and one not tried are two providers
def fw.seen_ne(+x: Nat, +y: Nat, +ts: List<&2, R.Tried>, hx: {R.seen(x, ts) == True{} : Bool}, hy: {R.seen(y, ts) == False{} : Bool}) -> {Nat.is_eq(x, y) == False{} : Bool}:
  fw.seen_ne_go(Nat.is_eq(x, y), x, y, ts, {==}, hx, hy)

# Maybe facts
# -----------

def fw.If(m: Maybe<&2, R.Switch>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

def fw.none_some(-G: Type, -s: R.Switch, e: {None{} == Some{s} : Maybe<&2, R.Switch>}) -> G:
  %e : fw.If(_, G)
  Unit{}

def fw.to_of(m: Maybe<&2, R.Switch>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{s}:
      match s:
        case R.Switch{to, w}:
          to

def fw.not_t(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      LLogicLogic.rp.absurdF({True{} == False{} : Bool}, e)
    case False{}:
      {==}

# The walk's switch
# -----------------

# the fresh pick over the order while some provider was not tried, else
# the return pick
def fw.Mode(all: Bool, len: Nat, ts: List<&2, R.Tried>, last: Nat, p: R.Policy, to: Nat, w: Nat) -> Type:
  match all:
    case True{}:
      {R.all_seen(len, ts) == True{} : Bool} & {R.pick.back(R.order(last, len), ts, R.backoff(p, len, ts), R.Policy.max(p)) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}
    case False{}:
      {R.all_seen(len, ts) == False{} : Bool} & {R.pick.fresh(R.order(last, len), ts) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}

def fw.Split(len: Nat, ts: List<&2, R.Tried>, last: Nat, p: R.Policy, to: Nat, w: Nat) -> Type:
  {Nat.is_le(R.length(ts), R.Policy.switches(p)) == True{} : Bool} & Sigma<&1, &1, Bool, all => fw.Mode(all, len, ts, last, p, to, w)>

def fw.mode(all: Bool, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy, -to: Nat, -w: Nat, ea: {R.all_seen(len, ts) == all : Bool}, got: {R.next.mode(all, last, len, ts, p) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}) -> Sigma<&1, &1, Bool, a => fw.Mode(a, len, ts, last, p, to, w)>:
  match all:
    case True{}:
      (True{}, (ea, got))
    case False{}:
      (False{}, (ea, Equal.trans(Maybe<&2, R.Switch>, R.pick.fresh(R.order(last, len), ts), R.fresh(last, len, ts), Some{R.Switch{to, w}}, LRetry.rp.fresh_order(last, len, ts), got)))

def fw.budget(ok: Bool, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy, -to: Nat, -w: Nat, eok: {Nat.is_le(R.length(ts), R.Policy.switches(p)) == ok : Bool}, got: {R.next.budget(ok, last, len, ts, p) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}) -> fw.Split(len, ts, last, p, to, w):
  match ok:
    case True{}:
      (eok, fw.mode(R.all_seen(len, ts), last, len, ts, p, to, w, {==}, got))
    case False{}:
      fw.none_some(fw.Split(len, ts, last, p, to, w), R.Switch{to, w}, got)

# a switch of a request with attempts: within the budget, and the fresh or
# the return pick over the order after the provider that just failed
def fw.split(+len: Nat, +t: R.Tried, +rest: List<&2, R.Tried>, +p: R.Policy, -to: Nat, -w: Nat, got: {R.next(len, t <> rest, p) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}) -> fw.Split(len, t <> rest, R.Tried.at(R.last.go(rest, t)), p, to, w):
  fw.budget(Nat.is_le(R.length(t <> rest), R.Policy.switches(p)), R.Tried.at(R.last.go(rest, t)), len, t <> rest, p, to, w, {==}, got)

# what a fresh pick guarantees of its switch: no wait, not the last
# provider, not tried
def fw.fresh_of(+ts: List<&2, R.Tried>, -to: Nat, -w: Nat, +xs: List<&2, Nat>, +l: Nat, nin: {LLogicBool.rp.notin(l, xs) == True{} : Bool}, pf: {R.pick.fresh(xs, ts) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}) -> {Bool.and(Nat.is_eq(w, 0n), Bool.and(Bool.not(Nat.is_eq(to, l)), Bool.not(R.seen(to, ts)))) == True{} : Bool}:
  Equal.trans(Bool, LLogicBool.rp.fresh_ok(Some{R.Switch{to, w}}, l, ts), LLogicBool.rp.fresh_ok(R.pick.fresh(xs, ts), l, ts), True{}, Equal.cong(Maybe<&2, R.Switch>, Bool, m => LLogicBool.rp.fresh_ok(m, l, ts), Some{R.Switch{to, w}}, R.pick.fresh(xs, ts), Equal.sym(Maybe<&2, R.Switch>, R.pick.fresh(xs, ts), Some{R.Switch{to, w}}, pf)), LRetry.rp.fresh_inv(xs, l, ts, nin))

# what a return pick guarantees of its switch: the wait is the backoff,
# and never less than its server's wait; not the last provider; the wait
# is positive and at most max
def fw.back_of(+ts: List<&2, R.Tried>, -to: Nat, -w: Nat, +xs: List<&2, Nat>, +l: Nat, +b: Nat, +m: Nat, nin: {LLogicBool.rp.notin(l, xs) == True{} : Bool}, pb: {R.pick.back(xs, ts, b, m) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}) -> {Bool.and(Nat.is_eq(Nat.max(b, R.server(to, ts)), w), Bool.and(Bool.not(Nat.is_eq(to, l)), Bool.and(Nat.is_gt(w, 0n), Nat.is_le(w, m)))) == True{} : Bool}:
  Equal.trans(Bool, LLogicBool.rp.back_ok(Some{R.Switch{to, w}}, l, ts, b, m), LLogicBool.rp.back_ok(R.pick.back(xs, ts, b, m), l, ts, b, m), True{}, Equal.cong(Maybe<&2, R.Switch>, Bool, k => LLogicBool.rp.back_ok(k, l, ts, b, m), Some{R.Switch{to, w}}, R.pick.back(xs, ts, b, m), Equal.sym(Maybe<&2, R.Switch>, R.pick.back(xs, ts, b, m), Some{R.Switch{to, w}}, pb)), LRetry.rp.back_inv(xs, l, ts, b, m, nin))

# Nat facts
# ---------

def fw.le_pred(a: Nat, b: Nat, h: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n b:
      LNat.rp.le_zero(b)
    case 1n+p 0n:
      LLogicLogic.rp.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      fw.le_pred(p, q, h)

# a <= y and a != y give 1 + a <= y
def fw.le_ne(a: Nat, y: Nat, lo: {Nat.is_le(a, y) == True{} : Bool}, ne: {Nat.is_eq(a, y) == False{} : Bool}) -> {Nat.is_le(1n+a, y) == True{} : Bool}:
  match a y:
    case 0n 0n:
      LLogicLogic.rp.absurdT({Nat.is_le(1n, 0n) == True{} : Bool}, ne)
    case 0n 1n+q:
      LNat.rp.le_zero(q)
    case 1n+p 0n:
      LLogicLogic.rp.absurdF({Nat.is_le(2n+p, 0n) == True{} : Bool}, lo)
    case 1n+p 1n+q:
      fw.le_ne(p, q, lo, ne)

# y > last gives 1 + last <= y
def fw.gt_le(y: Nat, last: Nat, h: {Nat.is_gt(y, last) == True{} : Bool}) -> {Nat.is_le(1n+last, y) == True{} : Bool}:
  match y last:
    case 0n 0n:
      LLogicLogic.rp.absurdF({Nat.is_le(1n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      LLogicLogic.rp.absurdF({Nat.is_le(2n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      LNat.rp.le_zero(p)
    case 1n+p 1n+q:
      fw.gt_le(p, q, h)

# y not past last and other than it is below it
def fw.lt_of(y: Nat, last: Nat, ngt: {Nat.is_gt(y, last) == False{} : Bool}, ne: {Nat.is_eq(y, last) == False{} : Bool}) -> {Nat.is_lt(y, last) == True{} : Bool}:
  match y last:
    case 0n 0n:
      LLogicLogic.rp.absurdT({Nat.is_lt(0n, 0n) == True{} : Bool}, ne)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LLogicLogic.rp.absurdT({Nat.is_lt(1n+p, 0n) == True{} : Bool}, ngt)
    case 1n+p 1n+q:
      fw.lt_of(p, q, ngt, ne)

# below both is below their min
def fw.lt_min(y: Nat, a: Nat, b: Nat, ha: {Nat.is_lt(y, a) == True{} : Bool}, hb: {Nat.is_lt(y, b) == True{} : Bool}) -> {Nat.is_lt(y, Nat.min(a, b)) == True{} : Bool}:
  match y a b:
    case 0n 0n b:
      LLogicLogic.rp.absurdF({Nat.is_lt(0n, Nat.min(0n, b)) == True{} : Bool}, ha)
    case 0n 1n+p 0n:
      LLogicLogic.rp.absurdF({Nat.is_lt(0n, Nat.min(1n+p, 0n)) == True{} : Bool}, hb)
    case 0n 1n+p 1n+q:
      {==}
    case 1n+x 0n b:
      LLogicLogic.rp.absurdF({Nat.is_lt(1n+x, Nat.min(0n, b)) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(1n+x, 0n), True{}, LNat.pu.lt_zero_f(1n+x), ha))
    case 1n+x 1n+p 0n:
      LLogicLogic.rp.absurdF({Nat.is_lt(1n+x, Nat.min(1n+p, 0n)) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(1n+x, 0n), True{}, LNat.pu.lt_zero_f(1n+x), hb))
    case 1n+x 1n+p 1n+q:
      fw.lt_min(x, p, q, ha, hb)

# 1 + (a + j) <= last gives a not past last
def fw.ngt(a: Nat, j: Nat, last: Nat, h: {Nat.is_le(1n+Nat.add(a, j), last) == True{} : Bool}) -> {Nat.is_gt(a, last) == False{} : Bool}:
  match a last:
    case 0n 0n:
      LLogicLogic.rp.absurdF({Nat.is_gt(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LLogicLogic.rp.absurdF({Nat.is_gt(1n+p, 0n) == False{} : Bool}, h)
    case 1n+p 1n+q:
      fw.ngt(p, j, q, h)

# 1 + (a + j) <= len gives a below len
def fw.lt_head(a: Nat, j: Nat, len: Nat, h: {Nat.is_le(1n+Nat.add(a, j), len) == True{} : Bool}) -> {Nat.is_lt(a, len) == True{} : Bool}:
  match a len:
    case 0n 0n:
      LLogicLogic.rp.absurdF({Nat.is_lt(0n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LLogicLogic.rp.absurdF({Nat.is_lt(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      fw.lt_head(p, j, q, h)

# a + (1 + j) <= c is 1 + (a + j) <= c
def fw.le_shift(+a: Nat, +j: Nat, +c: Nat, h: {Nat.is_le(Nat.add(a, 1n+j), c) == True{} : Bool}) -> {Nat.is_le(1n+Nat.add(a, j), c) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(1n+Nat.add(a, j), c), Nat.is_le(Nat.add(a, 1n+j), c), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, c), 1n+Nat.add(a, j), Nat.add(a, 1n+j), Equal.sym(Nat, Nat.add(a, 1n+j), 1n+Nat.add(a, j), LNat.add_succ(a, j))), h)

# x - n is 0 when n is past x
def fw.sub_zero(n: Nat, x: Nat, e: {Nat.is_le(n, x) == False{} : Bool}) -> {Nat.sub(x, n) == 0n : Nat}:
  match n x:
    case 0n 0n:
      LLogicLogic.rp.absurdT({Nat.sub(0n, 0n) == 0n : Nat}, e)
    case 0n 1n+q:
      LLogicLogic.rp.absurdT({Nat.sub(1n+q, 0n) == 0n : Nat}, e)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      fw.sub_zero(p, q, e)

def fw.sub_self(x: Nat) -> {Nat.sub(x, x) == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      fw.sub_self(p)

# a past last: a - last is one more than a - (1 + last)
def fw.sub_succ(a: Nat, last: Nat, h: {Nat.is_gt(a, last) == True{} : Bool}) -> {Nat.sub(a, last) == 1n+Nat.sub(a, 1n+last) : Nat}:
  match a last:
    case 0n 0n:
      LLogicLogic.rp.absurdF({Nat.sub(0n, 0n) == 1n+Nat.sub(0n, 1n) : Nat}, h)
    case 0n 1n+q:
      LLogicLogic.rp.absurdF({Nat.sub(0n, 1n+q) == 1n+Nat.sub(0n, 2n+q) : Nat}, h)
    case 1n+p 0n:
      Equal.cong(Nat, Nat, z => 1n+z, p, Nat.sub(p, 0n), LNat.pj.sub_zero(p))
    case 1n+p 1n+q:
      fw.sub_succ(p, q, h)

def fw.gt_succ(a: Nat, last: Nat, h: {Nat.is_gt(a, last) == True{} : Bool}) -> {Nat.is_gt(1n+a, last) == True{} : Bool}:
  match a last:
    case 0n 0n:
      LLogicLogic.rp.absurdF({Nat.is_gt(1n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      LLogicLogic.rp.absurdF({Nat.is_gt(1n, 1n+q) == True{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      fw.gt_succ(p, q, h)

def fw.gt_self(last: Nat) -> {Nat.is_gt(1n+last, last) == True{} : Bool}:
  match last:
    case 0n:
      {==}
    case 1n+p:
      fw.gt_self(p)

def fw.or_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def fw.not_f(b: Bool, e: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.rp.absurdT({False{} == True{} : Bool}, e)

# The chain order
# ---------------

# y is an element of xs
def fw.mem(+y: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      Bool.or(Nat.is_eq(x, y), fw.mem(y, rest))

# whether the head of xs is y
def fw.hd(xs: List<&2, Nat>, +y: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      Nat.is_eq(x, y)

def fw.mem_app(xs: List<&2, Nat>, +ys: List<&2, Nat>, +y: Nat) -> {fw.mem(y, List.append(&2, Nat, xs, ys)) == Bool.or(fw.mem(y, xs), fw.mem(y, ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, fw.mem(y, List.append(&2, Nat, rest, ys)), Bool.or(fw.mem(y, rest), fw.mem(y, ys)), fw.mem_app(rest, ys, y)) : {Bool.or(Nat.is_eq(x, y), _) == Bool.or(Bool.or(Nat.is_eq(x, y), fw.mem(y, rest)), fw.mem(y, ys)) : Bool}
      fw.or_assoc(Nat.is_eq(x, y), fw.mem(y, rest), fw.mem(y, ys))

def fw.mem_app_l(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +y: Nat, h: {fw.mem(y, xs) == True{} : Bool}) -> {fw.mem(y, List.append(&2, Nat, xs, ys)) == True{} : Bool}:
  %Equal.sym(Bool, fw.mem(y, List.append(&2, Nat, xs, ys)), Bool.or(fw.mem(y, xs), fw.mem(y, ys)), fw.mem_app(xs, ys, y)) : {_ == True{} : Bool}
  LBool.rp.or_l(fw.mem(y, xs), fw.mem(y, ys), h)

def fw.mem_app_r(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +y: Nat, h: {fw.mem(y, ys) == True{} : Bool}) -> {fw.mem(y, List.append(&2, Nat, xs, ys)) == True{} : Bool}:
  %Equal.sym(Bool, fw.mem(y, List.append(&2, Nat, xs, ys)), Bool.or(fw.mem(y, xs), fw.mem(y, ys)), fw.mem_app(xs, ys, y)) : {_ == True{} : Bool}
  LBool.rp.or_r(fw.mem(y, xs), fw.mem(y, ys), h)

# a <= y < a + k: y is one of a, ..., a+k-1 (c: whether a is y)
def fw.mem_upto(k: Nat, c: Bool, +a: Nat, +y: Nat, +ec: {Nat.is_eq(a, y) == c : Bool}, lo: {Nat.is_le(a, y) == True{} : Bool}, hi: {Nat.is_lt(y, Nat.add(a, k)) == True{} : Bool}) -> {fw.mem(y, R.upto(k, a)) == True{} : Bool}:
  match k c:
    case 0n c:
      +hy = Equal.trans(Bool, Nat.is_lt(y, a), Nat.is_lt(y, Nat.add(a, 0n)), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(y, z), a, Nat.add(a, 0n), Equal.sym(Nat, Nat.add(a, 0n), a, LNat.add_zero(a))), hi)
      LLogicLogic.rp.absurdT({fw.mem(y, R.upto(0n, a)) == True{} : Bool}, Equal.trans(Bool, True{}, Nat.is_lt(a, a), False{}, Equal.sym(Bool, Nat.is_lt(a, a), True{}, LNat.pc.le_lt_trans(a, y, a, lo, hy)), LNat.pt.lt_irrefl(a)))
    case 1n+j True{}:
      %Equal.sym(Bool, Nat.is_eq(a, y), True{}, ec) : {Bool.or(_, fw.mem(y, R.upto(j, 1n+a))) == True{} : Bool}
      {==}
    case 1n+j False{}:
      %Equal.sym(Bool, Nat.is_eq(a, y), False{}, ec) : {Bool.or(_, fw.mem(y, R.upto(j, 1n+a))) == True{} : Bool}
      fw.mem_upto(j, Nat.is_eq(1n+a, y), 1n+a, y, {==}, fw.le_ne(a, y, lo, ec), Equal.trans(Bool, Nat.is_lt(y, 1n+Nat.add(a, j)), Nat.is_lt(y, Nat.add(a, 1n+j)), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(y, z), 1n+Nat.add(a, j), Nat.add(a, 1n+j), Equal.sym(Nat, Nat.add(a, 1n+j), 1n+Nat.add(a, j), LNat.add_succ(a, j))), hi))

def fw.mem_seg(c: Bool, +last: Nat, +len: Nat, +y: Nat, ec: {Nat.is_gt(y, last) == c : Bool}, +hy: {Nat.is_lt(y, len) == True{} : Bool}, ne: {Nat.is_eq(y, last) == False{} : Bool}) -> {fw.mem(y, R.order(last, len)) == True{} : Bool}:
  match c:
    case True{}:
      +lo = fw.gt_le(y, last, ec)
      +e = LNat.pu.sub_add(1n+last, len, LNat.pc.lt_to_le(1n+last, len, LNat.pc.le_lt_trans(1n+last, y, len, lo, hy)))
      +hi = Equal.trans(Bool, Nat.is_lt(y, Nat.add(1n+last, Nat.sub(len, 1n+last))), Nat.is_lt(y, len), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(y, z), Nat.add(1n+last, Nat.sub(len, 1n+last)), len, e), hy)
      fw.mem_app_l(R.upto(Nat.sub(len, 1n+last), 1n+last), R.upto(Nat.min(last, len), 0n), y, fw.mem_upto(Nat.sub(len, 1n+last), Nat.is_eq(1n+last, y), 1n+last, y, {==}, lo, hi))
    case False{}:
      +hi = fw.lt_min(y, last, len, fw.lt_of(y, last, ec, ne), hy)
      fw.mem_app_r(R.upto(Nat.sub(len, 1n+last), 1n+last), R.upto(Nat.min(last, len), 0n), y, fw.mem_upto(Nat.min(last, len), Nat.is_eq(0n, y), 0n, y, {==}, LNat.rp.le_zero(y), hi))

# every provider of the chain other than last is in the order after last
def fw.order_mem(+last: Nat, +len: Nat, +y: Nat, hy: {Nat.is_lt(y, len) == True{} : Bool}, ne: {Nat.is_eq(y, last) == False{} : Bool}) -> {fw.mem(y, R.order(last, len)) == True{} : Bool}:
  fw.mem_seg(Nat.is_gt(y, last), last, len, y, {==}, hy, ne)

# every element of xs is below len
def fw.below(xs: List<&2, Nat>, +len: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(Nat.is_lt(x, len), fw.below(rest, len))

def fw.below_upto(k: Nat, +a: Nat, +len: Nat, h: {Nat.is_le(Nat.add(a, k), len) == True{} : Bool}) -> {fw.below(R.upto(k, a), len) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n++j:
      +h2 = fw.le_shift(a, j, len, h)
      LBool.rp.and_tt(Nat.is_lt(a, len), fw.below(R.upto(j, 1n+a), len), fw.lt_head(a, j, len, h2), fw.below_upto(j, 1n+a, len, h2))

def fw.below_app(xs: List<&2, Nat>, +ys: List<&2, Nat>, +len: Nat, +hx: {fw.below(xs, len) == True{} : Bool}, hy: {fw.below(ys, len) == True{} : Bool}) -> {fw.below(List.append(&2, Nat, xs, ys), len) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +x <> +rest:
      LBool.rp.and_tt(Nat.is_lt(x, len), fw.below(List.append(&2, Nat, rest, ys), len), LLogicBool.rp.and_l(Nat.is_lt(x, len), fw.below(rest, len), hx), fw.below_app(rest, ys, len, LLogicBool.rp.and_r(Nat.is_lt(x, len), fw.below(rest, len), hx), hy))

def fw.seg1_below(c: Bool, +last: Nat, +len: Nat, ec: {Nat.is_le(1n+last, len) == c : Bool}) -> {fw.below(R.upto(Nat.sub(len, 1n+last), 1n+last), len) == True{} : Bool}:
  match c:
    case True{}:
      +e = LNat.pu.sub_add(1n+last, len, ec)
      fw.below_upto(Nat.sub(len, 1n+last), 1n+last, len, Equal.trans(Bool, Nat.is_le(Nat.add(1n+last, Nat.sub(len, 1n+last)), len), Nat.is_le(len, len), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, len), Nat.add(1n+last, Nat.sub(len, 1n+last)), len, e), LNat.child.pc.le_refl(len)))
    case False{}:
      Equal.cong(Nat, Bool, k => fw.below(R.upto(k, 1n+last), len), Nat.sub(len, 1n+last), 0n, fw.sub_zero(1n+last, len, ec))

# the order after last holds no provider past the chain
def fw.order_below(+last: Nat, +len: Nat) -> {fw.below(R.order(last, len), len) == True{} : Bool}:
  fw.below_app(R.upto(Nat.sub(len, 1n+last), 1n+last), R.upto(Nat.min(last, len), 0n), len, fw.seg1_below(Nat.is_le(1n+last, len), last, len, {==}), fw.below_upto(Nat.min(last, len), 0n, len, LNat.pj.min_le_r(last, len)))

# the place of each element of xs in the order is r0, r0+1, ...
def fw.ranked(xs: List<&2, Nat>, +r0: Nat, +last: Nat, +len: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(Nat.is_eq(Retry.rs.rank(last, x, len), r0), fw.ranked(rest, 1n+r0, last, len))

def fw.len_upto(k: Nat, +a: Nat) -> {List.length(&2, Nat, R.upto(k, a)) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Nat, R.upto(j, 1n+a)), j, fw.len_upto(j, 1n+a))

# the providers past last are ranked from a - (1 + last)
def fw.rk_up1(k: Nat, +a: Nat, +last: Nat, +len: Nat, +ha: {Nat.is_gt(a, last) == True{} : Bool}) -> {fw.ranked(R.upto(k, a), Nat.sub(a, 1n+last), last, len) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(Bool, Nat.is_gt(a, last), True{}, ha) : {Bool.and(Nat.is_eq(Retry.rs.rank.pick(_, last, a, len), Nat.sub(a, 1n+last)), fw.ranked(R.upto(j, 1n+a), 1n+Nat.sub(a, 1n+last), last, len)) == True{} : Bool}
      +tail = Equal.trans(Bool, fw.ranked(R.upto(j, 1n+a), 1n+Nat.sub(a, 1n+last), last, len), fw.ranked(R.upto(j, 1n+a), Nat.sub(a, last), last, len), True{}, Equal.cong(Nat, Bool, z => fw.ranked(R.upto(j, 1n+a), z, last, len), 1n+Nat.sub(a, 1n+last), Nat.sub(a, last), Equal.sym(Nat, Nat.sub(a, last), 1n+Nat.sub(a, 1n+last), fw.sub_succ(a, last, ha))), fw.rk_up1(j, 1n+a, last, len, fw.gt_succ(a, last, ha)))
      LBool.rp.and_tt(Nat.is_eq(Nat.sub(a, 1n+last), Nat.sub(a, 1n+last)), fw.ranked(R.upto(j, 1n+a), 1n+Nat.sub(a, 1n+last), last, len), LNat.child.pc.eq_refl(Nat.sub(a, 1n+last)), tail)

# the providers before last are ranked from a + (len - (1 + last))
def fw.rk_up2(k: Nat, +a: Nat, +last: Nat, +len: Nat, h: {Nat.is_le(Nat.add(a, k), last) == True{} : Bool}) -> {fw.ranked(R.upto(k, a), Nat.add(a, Nat.sub(len, 1n+last)), last, len) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n++j:
      +h2 = fw.le_shift(a, j, last, h)
      %Equal.sym(Bool, Nat.is_gt(a, last), False{}, fw.ngt(a, j, last, h2)) : {Bool.and(Nat.is_eq(Retry.rs.rank.pick(_, last, a, len), Nat.add(a, Nat.sub(len, 1n+last))), fw.ranked(R.upto(j, 1n+a), 1n+Nat.add(a, Nat.sub(len, 1n+last)), last, len)) == True{} : Bool}
      LBool.rp.and_tt(Nat.is_eq(Nat.add(a, Nat.sub(len, 1n+last)), Nat.add(a, Nat.sub(len, 1n+last))), fw.ranked(R.upto(j, 1n+a), 1n+Nat.add(a, Nat.sub(len, 1n+last)), last, len), LNat.child.pc.eq_refl(Nat.add(a, Nat.sub(len, 1n+last))), fw.rk_up2(j, 1n+a, last, len, h2))

def fw.rk_app(xs: List<&2, Nat>, +ys: List<&2, Nat>, +r0: Nat, +last: Nat, +len: Nat, +hx: {fw.ranked(xs, r0, last, len) == True{} : Bool}, hy: {fw.ranked(ys, Nat.add(r0, List.length(&2, Nat, xs)), last, len) == True{} : Bool}) -> {fw.ranked(List.append(&2, Nat, xs, ys), r0, last, len) == True{} : Bool}:
  match xs:
    case Nil{}:
      Equal.trans(Bool, fw.ranked(ys, r0, last, len), fw.ranked(ys, Nat.add(r0, 0n), last, len), True{}, Equal.cong(Nat, Bool, z => fw.ranked(ys, z, last, len), r0, Nat.add(r0, 0n), Equal.sym(Nat, Nat.add(r0, 0n), r0, LNat.add_zero(r0))), hy)
    case +x <> +rest:
      +n = List.length(&2, Nat, rest)
      +hy2 = Equal.trans(Bool, fw.ranked(ys, 1n+Nat.add(r0, n), last, len), fw.ranked(ys, Nat.add(r0, 1n+n), last, len), True{}, Equal.cong(Nat, Bool, z => fw.ranked(ys, z, last, len), 1n+Nat.add(r0, n), Nat.add(r0, 1n+n), Equal.sym(Nat, Nat.add(r0, 1n+n), 1n+Nat.add(r0, n), LNat.add_succ(r0, n))), hy)
      LBool.rp.and_tt(Nat.is_eq(Retry.rs.rank(last, x, len), r0), fw.ranked(List.append(&2, Nat, rest, ys), 1n+r0, last, len), LLogicBool.rp.and_l(Nat.is_eq(Retry.rs.rank(last, x, len), r0), fw.ranked(rest, 1n+r0, last, len), hx), fw.rk_app(rest, ys, 1n+r0, last, len, LLogicBool.rp.and_r(Nat.is_eq(Retry.rs.rank(last, x, len), r0), fw.ranked(rest, 1n+r0, last, len), hx), hy2))

# the order after last ranks its providers 0, 1, ... (each at its rs.rank)
def fw.order_ranked(+last: Nat, +len: Nat) -> {fw.ranked(R.order(last, len), 0n, last, len) == True{} : Bool}:
  +L = Nat.sub(len, 1n+last)
  +s1 = Equal.trans(Bool, fw.ranked(R.upto(L, 1n+last), 0n, last, len), fw.ranked(R.upto(L, 1n+last), Nat.sub(last, last), last, len), True{}, Equal.cong(Nat, Bool, z => fw.ranked(R.upto(L, 1n+last), z, last, len), 0n, Nat.sub(last, last), Equal.sym(Nat, Nat.sub(last, last), 0n, fw.sub_self(last))), fw.rk_up1(L, 1n+last, last, len, fw.gt_self(last)))
  +s2 = Equal.trans(Bool, fw.ranked(R.upto(Nat.min(last, len), 0n), List.length(&2, Nat, R.upto(L, 1n+last)), last, len), fw.ranked(R.upto(Nat.min(last, len), 0n), L, last, len), True{}, Equal.cong(Nat, Bool, z => fw.ranked(R.upto(Nat.min(last, len), 0n), z, last, len), List.length(&2, Nat, R.upto(L, 1n+last)), L, fw.len_upto(L, 1n+last)), fw.rk_up2(Nat.min(last, len), 0n, last, len, LNat.rp.min_le(last, len)))
  fw.rk_app(R.upto(L, 1n+last), R.upto(Nat.min(last, len), 0n), 0n, last, len, s1, s2)

# a member of a list ranked from r0 is ranked r0 or later (c: whether the
# head is y)
def fw.ranked_ge(xs: List<&2, Nat>, c: Bool, +r0: Nat, +last: Nat, +len: Nat, +y: Nat, ec: {fw.hd(xs, y) == c : Bool}, hr: {fw.ranked(xs, r0, last, len) == True{} : Bool}, hm: {fw.mem(y, xs) == True{} : Bool}) -> {Nat.is_le(r0, Retry.rs.rank(last, y, len)) == True{} : Bool}:
  match xs c:
    case Nil{} c:
      LLogicLogic.rp.absurdF({Nat.is_le(r0, Retry.rs.rank(last, y, len)) == True{} : Bool}, hm)
    case Con{+x, rest} True{}:
      +exy = LLogicNat.rp.eq_true(x, y, ec)
      +er = LLogicNat.rp.eq_true(Retry.rs.rank(last, x, len), r0, LLogicBool.rp.and_l(Nat.is_eq(Retry.rs.rank(last, x, len), r0), fw.ranked(rest, 1n+r0, last, len), hr))
      %exy : {Nat.is_le(r0, Retry.rs.rank(last, _, len)) == True{} : Bool}
      %er : {Nat.is_le(_, Retry.rs.rank(last, x, len)) == True{} : Bool}
      LNat.child.pc.le_refl(Retry.rs.rank(last, x, len))
    case Con{+x, +rest} False{}:
      +hm2 = Equal.trans(Bool, fw.mem(y, rest), Bool.or(Nat.is_eq(x, y), fw.mem(y, rest)), True{}, Equal.cong(Bool, Bool, b => Bool.or(b, fw.mem(y, rest)), False{}, Nat.is_eq(x, y), Equal.sym(Bool, Nat.is_eq(x, y), False{}, ec)), hm)
      fw.le_pred(r0, Retry.rs.rank(last, y, len), fw.ranked_ge(rest, fw.hd(rest, y), 1n+r0, last, len, y, {==}, LLogicBool.rp.and_r(Nat.is_eq(Retry.rs.rank(last, x, len), r0), fw.ranked(rest, 1n+r0, last, len), hr), hm2))

# The picks
# ---------

def fw.pick_lt(m: Maybe<&2, R.Switch>, +len: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{s}:
      match s:
        case R.Switch{to, w}:
          Nat.is_lt(to, len)

def fw.sel_lt(c: Bool, +x: Nat, +d: Nat, r: Maybe<&2, R.Switch>, +len: Nat, hx: {Nat.is_lt(x, len) == True{} : Bool}, hr: {fw.pick_lt(r, len) == True{} : Bool}) -> {fw.pick_lt(R.pick.sel(c, R.Switch{x, d}, r), len) == True{} : Bool}:
  match c:
    case True{}:
      hx
    case False{}:
      hr

def fw.fresh_lt(xs: List<&2, Nat>, +ts: List<&2, R.Tried>, +len: Nat, +hb: {fw.below(xs, len) == True{} : Bool}) -> {fw.pick_lt(R.pick.fresh(xs, ts), len) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      fw.sel_lt(Bool.not(R.seen(x, ts)), x, 0n, R.pick.fresh(rest, ts), len, LLogicBool.rp.and_l(Nat.is_lt(x, len), fw.below(rest, len), hb), fw.fresh_lt(rest, ts, len, LLogicBool.rp.and_r(Nat.is_lt(x, len), fw.below(rest, len), hb)))

def fw.back_lt(xs: List<&2, Nat>, +ts: List<&2, R.Tried>, +b: Nat, +m: Nat, +len: Nat, +hb: {fw.below(xs, len) == True{} : Bool}) -> {fw.pick_lt(R.pick.back(xs, ts, b, m), len) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      +d = Nat.max(b, R.server(x, ts))
      fw.sel_lt(Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, m)), x, d, R.pick.back(rest, ts, b, m), len, LLogicBool.rp.and_l(Nat.is_lt(x, len), fw.below(rest, len), hb), fw.back_lt(rest, ts, b, m, len, LLogicBool.rp.and_r(Nat.is_lt(x, len), fw.below(rest, len), hb)))

# whether the head of xs is not tried (Nil: False)
def fw.hs(xs: List<&2, Nat>, +ts: List<&2, R.Tried>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      Bool.not(R.seen(x, ts))

# whether a return to the head of xs may go out (Nil: False)
def fw.ok(+x: Nat, +ts: List<&2, R.Tried>, +b: Nat, +m: Nat) -> Bool:
  Bool.and(Nat.is_gt(Nat.max(b, R.server(x, ts)), 0n), Nat.is_le(Nat.max(b, R.server(x, ts)), m))

def fw.hb(xs: List<&2, Nat>, +ts: List<&2, R.Tried>, +b: Nat, +m: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      fw.ok(x, ts, b, m)

# a fresh pick over a ranked list is no later than any provider of it not
# tried (c: whether the head is y; d: whether the head is not tried)
def fw.fresh_nearest(xs: List<&2, Nat>, c: Bool, d: Bool, +r0: Nat, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, -to: Nat, -w: Nat, +y: Nat, ec: {fw.hd(xs, y) == c : Bool}, ed: {fw.hs(xs, ts) == d : Bool}, +hr: {fw.ranked(xs, r0, last, len) == True{} : Bool}, hp: {R.pick.fresh(xs, ts) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}, +hm: {fw.mem(y, xs) == True{} : Bool}, hy: {R.seen(y, ts) == False{} : Bool}) -> {Nat.is_le(Retry.rs.rank(last, to, len), Retry.rs.rank(last, y, len)) == True{} : Bool}:
  match xs c d:
    case Nil{} c d:
      fw.none_some({Nat.is_le(Retry.rs.rank(last, to, len), Retry.rs.rank(last, y, len)) == True{} : Bool}, R.Switch{to, w}, hp)
    case Con{+x, +rest} c True{}:
      +hp2 = Equal.trans(Maybe<&2, R.Switch>, Some{R.Switch{x, 0n}}, R.pick.fresh(x <> rest, ts), Some{R.Switch{to, w}}, Equal.cong(Bool, Maybe<&2, R.Switch>, k => R.pick.sel(k, R.Switch{x, 0n}, R.pick.fresh(rest, ts)), True{}, Bool.not(R.seen(x, ts)), Equal.sym(Bool, Bool.not(R.seen(x, ts)), True{}, ed)), hp)
      +eto = Equal.cong(Maybe<&2, R.Switch>, Nat, k => fw.to_of(k), Some{R.Switch{x, 0n}}, Some{R.Switch{to, w}}, hp2)
      +er = LLogicNat.rp.eq_true(Retry.rs.rank(last, x, len), r0, LLogicBool.rp.and_l(Nat.is_eq(Retry.rs.rank(last, x, len), r0), fw.ranked(rest, 1n+r0, last, len), hr))
      %eto : {Nat.is_le(Retry.rs.rank(last, _, len), Retry.rs.rank(last, y, len)) == True{} : Bool}
      %Equal.sym(Nat, Retry.rs.rank(last, x, len), r0, er) : {Nat.is_le(_, Retry.rs.rank(last, y, len)) == True{} : Bool}
      fw.ranked_ge(x <> rest, fw.hd(x <> rest, y), r0, last, len, y, {==}, hr, hm)
    case Con{+x, +rest} True{} False{}:
      +exy = LLogicNat.rp.eq_true(x, y, ec)
      +sx = fw.not_f(R.seen(x, ts), ed)
      LLogicLogic.rp.absurdT({Nat.is_le(Retry.rs.rank(last, to, len), Retry.rs.rank(last, y, len)) == True{} : Bool}, Equal.trans(Bool, True{}, R.seen(y, ts), False{}, Equal.trans(Bool, True{}, R.seen(x, ts), R.seen(y, ts), Equal.sym(Bool, R.seen(x, ts), True{}, sx), Equal.cong(Nat, Bool, z => R.seen(z, ts), x, y, exy)), hy))
    case Con{+x, +rest} False{} False{}:
      +hp2 = Equal.trans(Maybe<&2, R.Switch>, R.pick.fresh(rest, ts), R.pick.fresh(x <> rest, ts), Some{R.Switch{to, w}}, Equal.cong(Bool, Maybe<&2, R.Switch>, k => R.pick.sel(k, R.Switch{x, 0n}, R.pick.fresh(rest, ts)), False{}, Bool.not(R.seen(x, ts)), Equal.sym(Bool, Bool.not(R.seen(x, ts)), False{}, ed)), hp)
      +hm2 = Equal.trans(Bool, fw.mem(y, rest), Bool.or(Nat.is_eq(x, y), fw.mem(y, rest)), True{}, Equal.cong(Bool, Bool, b => Bool.or(b, fw.mem(y, rest)), False{}, Nat.is_eq(x, y), Equal.sym(Bool, Nat.is_eq(x, y), False{}, ec)), hm)
      fw.fresh_nearest(rest, fw.hd(rest, y), fw.hs(rest, ts), 1n+r0, last, len, ts, to, w, y, {==}, {==}, LLogicBool.rp.and_r(Nat.is_eq(Retry.rs.rank(last, x, len), r0), fw.ranked(rest, 1n+r0, last, len), hr), hp2, hm2, hy)

# a return pick over a ranked list is no later than any provider of it a
# return may go to (c: whether the head is y; d: whether the head may)
def fw.back_nearest(xs: List<&2, Nat>, c: Bool, d: Bool, +r0: Nat, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +b: Nat, +m: Nat, -to: Nat, -w: Nat, +y: Nat, ec: {fw.hd(xs, y) == c : Bool}, ed: {fw.hb(xs, ts, b, m) == d : Bool}, +hr: {fw.ranked(xs, r0, last, len) == True{} : Bool}, hp: {R.pick.back(xs, ts, b, m) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}, +hm: {fw.mem(y, xs) == True{} : Bool}, hy: {fw.ok(y, ts, b, m) == True{} : Bool}) -> {Nat.is_le(Retry.rs.rank(last, to, len), Retry.rs.rank(last, y, len)) == True{} : Bool}:
  match xs c d:
    case Nil{} c d:
      fw.none_some({Nat.is_le(Retry.rs.rank(last, to, len), Retry.rs.rank(last, y, len)) == True{} : Bool}, R.Switch{to, w}, hp)
    case Con{+x, +rest} c True{}:
      +dx = Nat.max(b, R.server(x, ts))
      +hp2 = Equal.trans(Maybe<&2, R.Switch>, Some{R.Switch{x, dx}}, R.pick.back(x <> rest, ts, b, m), Some{R.Switch{to, w}}, Equal.cong(Bool, Maybe<&2, R.Switch>, k => R.pick.sel(k, R.Switch{x, dx}, R.pick.back(rest, ts, b, m)), True{}, fw.ok(x, ts, b, m), Equal.sym(Bool, fw.ok(x, ts, b, m), True{}, ed)), hp)
      +eto = Equal.cong(Maybe<&2, R.Switch>, Nat, k => fw.to_of(k), Some{R.Switch{x, dx}}, Some{R.Switch{to, w}}, hp2)
      +er = LLogicNat.rp.eq_true(Retry.rs.rank(last, x, len), r0, LLogicBool.rp.and_l(Nat.is_eq(Retry.rs.rank(last, x, len), r0), fw.ranked(rest, 1n+r0, last, len), hr))
      %eto : {Nat.is_le(Retry.rs.rank(last, _, len), Retry.rs.rank(last, y, len)) == True{} : Bool}
      %Equal.sym(Nat, Retry.rs.rank(last, x, len), r0, er) : {Nat.is_le(_, Retry.rs.rank(last, y, len)) == True{} : Bool}
      fw.ranked_ge(x <> rest, fw.hd(x <> rest, y), r0, last, len, y, {==}, hr, hm)
    case Con{+x, +rest} True{} False{}:
      +exy = LLogicNat.rp.eq_true(x, y, ec)
      LLogicLogic.rp.absurdF({Nat.is_le(Retry.rs.rank(last, to, len), Retry.rs.rank(last, y, len)) == True{} : Bool}, Equal.trans(Bool, False{}, fw.ok(y, ts, b, m), True{}, Equal.trans(Bool, False{}, fw.ok(x, ts, b, m), fw.ok(y, ts, b, m), Equal.sym(Bool, fw.ok(x, ts, b, m), False{}, ed), Equal.cong(Nat, Bool, z => fw.ok(z, ts, b, m), x, y, exy)), hy))
    case Con{+x, +rest} False{} False{}:
      +dx = Nat.max(b, R.server(x, ts))
      +hp2 = Equal.trans(Maybe<&2, R.Switch>, R.pick.back(rest, ts, b, m), R.pick.back(x <> rest, ts, b, m), Some{R.Switch{to, w}}, Equal.cong(Bool, Maybe<&2, R.Switch>, k => R.pick.sel(k, R.Switch{x, dx}, R.pick.back(rest, ts, b, m)), False{}, fw.ok(x, ts, b, m), Equal.sym(Bool, fw.ok(x, ts, b, m), False{}, ed)), hp)
      +hm2 = Equal.trans(Bool, fw.mem(y, rest), Bool.or(Nat.is_eq(x, y), fw.mem(y, rest)), True{}, Equal.cong(Bool, Bool, k => Bool.or(k, fw.mem(y, rest)), False{}, Nat.is_eq(x, y), Equal.sym(Bool, Nat.is_eq(x, y), False{}, ec)), hm)
      fw.back_nearest(rest, fw.hd(rest, y), fw.hb(rest, ts, b, m), 1n+r0, last, len, ts, b, m, to, w, y, {==}, {==}, LLogicBool.rp.and_r(Nat.is_eq(Retry.rs.rank(last, x, len), r0), fw.ranked(rest, 1n+r0, last, len), hr), hp2, hm2, hy)

# a fresh pick over a list holding a provider not tried is a switch
def fw.fresh_some(xs: List<&2, Nat>, c: Bool, d: Bool, +ts: List<&2, R.Tried>, +y: Nat, ec: {fw.hd(xs, y) == c : Bool}, ed: {fw.hs(xs, ts) == d : Bool}, hm: {fw.mem(y, xs) == True{} : Bool}, hy: {R.seen(y, ts) == False{} : Bool}) -> {Retry.rs.is_switch(R.pick.fresh(xs, ts)) == True{} : Bool}:
  match xs c d:
    case Nil{} c d:
      LLogicLogic.rp.absurdF({Retry.rs.is_switch(R.pick.fresh(Nil{}, ts)) == True{} : Bool}, hm)
    case Con{+x, +rest} c True{}:
      %Equal.sym(Bool, Bool.not(R.seen(x, ts)), True{}, ed) : {Retry.rs.is_switch(R.pick.sel(_, R.Switch{x, 0n}, R.pick.fresh(rest, ts))) == True{} : Bool}
      {==}
    case Con{+x, +rest} True{} False{}:
      +exy = LLogicNat.rp.eq_true(x, y, ec)
      +sx = fw.not_f(R.seen(x, ts), ed)
      LLogicLogic.rp.absurdT({Retry.rs.is_switch(R.pick.fresh(x <> rest, ts)) == True{} : Bool}, Equal.trans(Bool, True{}, R.seen(y, ts), False{}, Equal.trans(Bool, True{}, R.seen(x, ts), R.seen(y, ts), Equal.sym(Bool, R.seen(x, ts), True{}, sx), Equal.cong(Nat, Bool, z => R.seen(z, ts), x, y, exy)), hy))
    case Con{+x, +rest} False{} False{}:
      +hm2 = Equal.trans(Bool, fw.mem(y, rest), Bool.or(Nat.is_eq(x, y), fw.mem(y, rest)), True{}, Equal.cong(Bool, Bool, k => Bool.or(k, fw.mem(y, rest)), False{}, Nat.is_eq(x, y), Equal.sym(Bool, Nat.is_eq(x, y), False{}, ec)), hm)
      %Equal.sym(Bool, Bool.not(R.seen(x, ts)), False{}, ed) : {Retry.rs.is_switch(R.pick.sel(_, R.Switch{x, 0n}, R.pick.fresh(rest, ts))) == True{} : Bool}
      fw.fresh_some(rest, fw.hd(rest, y), fw.hs(rest, ts), ts, y, {==}, {==}, hm2, hy)

# a return pick over a list holding a provider a return may go to is a
# switch
def fw.back_some(xs: List<&2, Nat>, c: Bool, d: Bool, +ts: List<&2, R.Tried>, +b: Nat, +m: Nat, +y: Nat, ec: {fw.hd(xs, y) == c : Bool}, ed: {fw.hb(xs, ts, b, m) == d : Bool}, hm: {fw.mem(y, xs) == True{} : Bool}, hy: {fw.ok(y, ts, b, m) == True{} : Bool}) -> {Retry.rs.is_switch(R.pick.back(xs, ts, b, m)) == True{} : Bool}:
  match xs c d:
    case Nil{} c d:
      LLogicLogic.rp.absurdF({Retry.rs.is_switch(R.pick.back(Nil{}, ts, b, m)) == True{} : Bool}, hm)
    case Con{+x, +rest} c True{}:
      %Equal.sym(Bool, fw.ok(x, ts, b, m), True{}, ed) : {Retry.rs.is_switch(R.pick.sel(_, R.Switch{x, Nat.max(b, R.server(x, ts))}, R.pick.back(rest, ts, b, m))) == True{} : Bool}
      {==}
    case Con{+x, +rest} True{} False{}:
      +exy = LLogicNat.rp.eq_true(x, y, ec)
      LLogicLogic.rp.absurdF({Retry.rs.is_switch(R.pick.back(x <> rest, ts, b, m)) == True{} : Bool}, Equal.trans(Bool, False{}, fw.ok(y, ts, b, m), True{}, Equal.trans(Bool, False{}, fw.ok(x, ts, b, m), fw.ok(y, ts, b, m), Equal.sym(Bool, fw.ok(x, ts, b, m), False{}, ed), Equal.cong(Nat, Bool, z => fw.ok(z, ts, b, m), x, y, exy)), hy))
    case Con{+x, +rest} False{} False{}:
      +hm2 = Equal.trans(Bool, fw.mem(y, rest), Bool.or(Nat.is_eq(x, y), fw.mem(y, rest)), True{}, Equal.cong(Bool, Bool, k => Bool.or(k, fw.mem(y, rest)), False{}, Nat.is_eq(x, y), Equal.sym(Bool, Nat.is_eq(x, y), False{}, ec)), hm)
      %Equal.sym(Bool, fw.ok(x, ts, b, m), False{}, ed) : {Retry.rs.is_switch(R.pick.sel(_, R.Switch{x, Nat.max(b, R.server(x, ts))}, R.pick.back(rest, ts, b, m))) == True{} : Bool}
      fw.back_some(rest, fw.hd(rest, y), fw.hb(rest, ts, b, m), ts, b, m, y, {==}, {==}, hm2, hy)

# every provider of a, ..., a+k-1 tried: so is a + i for i below k
def fw.ints_has(k: Nat, i: Nat, +a: Nat, +ts: List<&2, R.Tried>, +h: {Retry.rs.all_tried(Retry.rs.ints(k, a), ts) == True{} : Bool}, hi: {Nat.is_lt(i, k) == True{} : Bool}) -> {Retry.rs.tried(Nat.add(i, a), ts) == True{} : Bool}:
  match k i:
    case 0n i:
      LLogicLogic.rp.absurdF({Retry.rs.tried(Nat.add(i, a), ts) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(i, 0n), True{}, Equal.sym(Bool, Nat.is_lt(i, 0n), False{}, LA.rx.lt_zero(i)), hi))
    case 1n+j 0n:
      LLogicBool.rp.and_l(Retry.rs.tried(a, ts), Retry.rs.all_tried(Retry.rs.ints(j, 1n+a), ts), h)
    case 1n+j 1n++ip:
      +ih = fw.ints_has(j, ip, 1n+a, ts, LLogicBool.rp.and_r(Retry.rs.tried(a, ts), Retry.rs.all_tried(Retry.rs.ints(j, 1n+a), ts), h), hi)
      Equal.trans(Bool, Retry.rs.tried(1n+Nat.add(ip, a), ts), Retry.rs.tried(Nat.add(ip, 1n+a), ts), True{}, Equal.cong(Nat, Bool, z => Retry.rs.tried(z, ts), 1n+Nat.add(ip, a), Nat.add(ip, 1n+a), Equal.sym(Nat, Nat.add(ip, 1n+a), 1n+Nat.add(ip, a), LNat.add_succ(ip, a))), ih)

# every provider of the chain tried: so is x below len
def fw.all_has(+len: Nat, +x: Nat, +ts: List<&2, R.Tried>, +all: {R.all_seen(len, ts) == True{} : Bool}, chain: {Nat.is_lt(x, len) == True{} : Bool}) -> {R.seen(x, ts) == True{} : Bool}:
  +h = Equal.trans(Bool, Retry.rs.all_tried(Retry.rs.ints(len, 0n), ts), R.all_seen(len, ts), True{}, Equal.sym(Bool, R.all_seen(len, ts), Retry.rs.all_tried(Retry.rs.ints(len, 0n), ts), fw.all_seen(len, ts)), all)
  +hx = Equal.trans(Bool, Retry.rs.tried(x, ts), Retry.rs.tried(Nat.add(x, 0n), ts), True{}, Equal.cong(Nat, Bool, z => Retry.rs.tried(z, ts), x, Nat.add(x, 0n), Equal.sym(Nat, Nat.add(x, 0n), x, LNat.add_zero(x))), fw.ints_has(len, x, 0n, ts, h, chain))
  Equal.trans(Bool, R.seen(x, ts), Retry.rs.tried(x, ts), True{}, fw.tried(x, ts), hx)
