# eukhe: lemmas the proofs of area revive share

import Base
import ../../bend/ffi_revive.bend as FR
import ../../bend/revive.bend as Rv
import ../../bend/wire.bend as Wr
import ../../laws/revive.bend as Revive
import ../base/nat.bend as LNat

# Impossible cases
# ----------------

def rvb.if_some(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

def rvb.if_none(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

# a None that is a Some proves anything
def rvb.none_some(-A: Data, -x: A, -G: Type, e: {None{} == Some{x} : Maybe<&2, A>}) -> G:
  %e : rvb.if_some(A, _, G)
  Unit{}

# a Some that is None proves anything
def rvb.some_none(-A: Data, -x: A, -G: Type, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  %e : rvb.if_none(A, _, G)
  Unit{}

def rvb.or(m: Maybe<&2, Rv.Facts>, d: Rv.Facts) -> Rv.Facts:
  match m:
    case None{}:
      d
    case Some{x}:
      x

# Some is injective
def rvb.some_inj(+x: Rv.Facts, -y: Rv.Facts, e: {Some{x} == Some{y} : Maybe<&2, Rv.Facts>}) -> {x == y : Rv.Facts}:
  Equal.cong(Maybe<&2, Rv.Facts>, Rv.Facts, m => rvb.or(m, x), Some{x}, Some{y}, e)

# The reader, stage by stage
# --------------------------

def rvb.k(fl: Bool, a: Bool, l: Maybe<&2, Nat>, b: Rv.Busy, n: Nat, m: Nat, r: Wr.Dec<Nat>) -> {Revive.rv_read.k(fl, a, l, b, n, m, r) == FR.get_facts.skew(fl, a, l, b, n, m, r) : Wr.Dec<Rv.Facts>}:
  match r:
    case Wr.Got{k, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rvb.m(fl: Bool, a: Bool, l: Maybe<&2, Nat>, b: Rv.Busy, n: Nat, r: Wr.Dec<Nat>) -> {Revive.rv_read.m(fl, a, l, b, n, r) == FR.get_facts.max(fl, a, l, b, n, r) : Wr.Dec<Rv.Facts>}:
  match r:
    case Wr.Got{m, s}:
      rvb.k(fl, a, l, b, n, m, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rvb.n(fl: Bool, a: Bool, l: Maybe<&2, Nat>, b: Rv.Busy, r: Wr.Dec<Nat>) -> {Revive.rv_read.n(fl, a, l, b, r) == FR.get_facts.now.n(fl, a, l, b, r) : Wr.Dec<Rv.Facts>}:
  match r:
    case Wr.Got{n, s}:
      rvb.m(fl, a, l, b, n, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rvb.at(fl: Bool, a: Bool, l: Maybe<&2, Nat>, r: Wr.Dec<Nat>) -> {Revive.rv_read.at(fl, a, l, r) == FR.get_facts.now(fl, a, l, FR.get_busy.at(r)) : Wr.Dec<Rv.Facts>}:
  match r:
    case Wr.Got{at, s}:
      rvb.n(fl, a, l, Rv.Stamp{at}, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rvb.busy_tag(fl: Bool, a: Bool, l: Maybe<&2, Nat>, t: Nat, s: String) -> {Revive.rv_read.busy.tag(fl, a, l, t, s) == FR.get_facts.now(fl, a, l, FR.get_busy.tag(t, s)) : Wr.Dec<Rv.Facts>}:
  match t:
    case 0n:
      rvb.n(fl, a, l, Rv.NoBusy{}, Wr.get_nat(s))
    case 1n:
      rvb.n(fl, a, l, Rv.Unread{}, Wr.get_nat(s))
    case 2n:
      rvb.at(fl, a, l, Wr.get_nat(s))
    case 3n+p:
      {==}

def rvb.busy(fl: Bool, a: Bool, l: Maybe<&2, Nat>, r: Wr.Dec<Nat>) -> {Revive.rv_read.busy(fl, a, l, r) == FR.get_facts.now(fl, a, l, FR.get_busy(r)) : Wr.Dec<Rv.Facts>}:
  match r:
    case Wr.Got{t, s}:
      rvb.busy_tag(fl, a, l, t, s)
    case Wr.Bad{}:
      {==}

def rvb.pid(fl: Bool, a: Bool, r: Wr.Dec<Nat>) -> {Revive.rv_read.pid(fl, a, r) == FR.get_facts.busy(fl, a, FR.get_lease.pid(r)) : Wr.Dec<Rv.Facts>}:
  match r:
    case Wr.Got{p, s}:
      rvb.busy(fl, a, Some{p}, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rvb.lease_tag(fl: Bool, a: Bool, t: Nat, s: String) -> {Revive.rv_read.lease.tag(fl, a, t, s) == FR.get_facts.busy(fl, a, FR.get_lease.tag(t, s)) : Wr.Dec<Rv.Facts>}:
  match t:
    case 0n:
      rvb.busy(fl, a, None{}, Wr.get_nat(s))
    case 1n:
      rvb.pid(fl, a, Wr.get_nat(s))
    case 2n+p:
      {==}

def rvb.lease(fl: Bool, a: Bool, r: Wr.Dec<Nat>) -> {Revive.rv_read.lease(fl, a, r) == FR.get_facts.busy(fl, a, FR.get_lease(r)) : Wr.Dec<Rv.Facts>}:
  match r:
    case Wr.Got{t, s}:
      rvb.lease_tag(fl, a, t, s)
    case Wr.Bad{}:
      {==}

def rvb.archived(fl: Bool, r: Wr.Dec<Bool>) -> {Revive.rv_read.archived(fl, r) == FR.get_facts.lease(fl, r) : Wr.Dec<Rv.Facts>}:
  match r:
    case Wr.Got{a, s}:
      rvb.lease(fl, a, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

# the entry reads every input as the laws' reader does
def rvb.failed(r: Wr.Dec<Bool>) -> {Revive.rv_read.failed(r) == FR.get_facts.archived(r) : Wr.Dec<Rv.Facts>}:
  match r:
    case Wr.Got{fl, s}:
      rvb.archived(fl, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

# The decision
# ------------

def rvb.and_t(x: Bool) -> {x == Bool.and(x, True{}) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def rvb.of_succ(b: Bool, p: Nat, q: Nat, m: Nat, k: Nat) -> {Revive.rv_fresh.of(b, 1n+p, 1n+q, m, k) == Revive.rv_fresh.of(b, p, q, m, k) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the spec's freshness (two cases on at <= now) is the model's
def rvb.fresh(at: Nat, now: Nat, +m: Nat, +k: Nat) -> {Revive.rv_fresh.of(Nat.is_le(at, now), at, now, m, k) == Bool.and(Nat.is_le(at, Nat.add(now, k)), Nat.is_le(Nat.sub(now, at), m)) : Bool}:
  match at now:
    case 0n 0n:
      match k:
        case 0n:
          {==}
        case 1n+j:
          {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      match m:
        case 0n:
          rvb.and_t(Nat.is_le(1n+p, k))
        case 1n+j:
          rvb.and_t(Nat.is_le(1n+p, k))
    case 1n++p 1n++q:
      Equal.trans(Bool, Revive.rv_fresh.of(Nat.is_le(p, q), 1n+p, 1n+q, m, k), Revive.rv_fresh.of(Nat.is_le(p, q), p, q, m, k), Bool.and(Nat.is_le(p, Nat.add(q, k)), Nat.is_le(Nat.sub(q, p), m)),
        rvb.of_succ(Nat.is_le(p, q), p, q, m, k), rvb.fresh(p, q, m, k))

def rvb.put_fresh(ok: Bool) -> {FR.put_veto(Rv.veto.fresh(ok)) == Revive.rv_reply.fresh(ok) : String}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def rvb.stamp(+at: Nat, +now: Nat, +m: Nat, +k: Nat) -> {FR.put_veto(Rv.veto.fresh(Rv.fresh_at(at, now, m, k))) == Revive.rv_reply.fresh(Revive.rv_fresh(at, now, m, k)) : String}:
  %rvb.fresh(at, now, m, k) : {FR.put_veto(Rv.veto.fresh(_)) == Revive.rv_reply.fresh(Revive.rv_fresh(at, now, m, k)) : String}
  rvb.put_fresh(Revive.rv_fresh(at, now, m, k))

def rvb.busy_reply(b: Rv.Busy, +now: Nat, +m: Nat, +k: Nat) -> {FR.put_veto(Rv.veto.busy(b, now, m, k)) == Revive.rv_reply.busy(b, now, m, k) : String}:
  match b:
    case Rv.NoBusy{}:
      {==}
    case Rv.Unread{}:
      {==}
    case Rv.Stamp{at}:
      rvb.stamp(at, now, m, k)

# the entry's veto, put on the wire, is the spec's reply
def rvb.reply(f: Rv.Facts) -> {FR.put_veto(Rv.veto(f)) == Revive.rv_reply(f) : String}:
  match f:
    case Rv.Facts{fl, a, l, b, n, m, k}:
      match fl:
        case True{}:
          {==}
        case False{}:
          match a:
            case True{}:
              {==}
            case False{}:
              match l:
                case Some{p}:
                  {==}
                case None{}:
                  rvb.busy_reply(b, n, m, k)

# The age of the busy evidence
# ----------------------------

# r is never r + k + 1
def rvb.ne_more(r: Nat, -k: Nat) -> {Nat.is_eq(r, 1n+Nat.add(r, k)) == False{} : Bool}:
  match r:
    case 0n:
      {==}
    case 1n+q:
      rvb.ne_more(q, k)

# one more ms of a run is one more tick at its end
def rvb.since_snoc(c: Nat, +h: Nat, r: Nat) -> {Rv.since(1n+c, h, r) == Rv.tick(h, Rv.since(c, h, r)) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      rvb.since_snoc(p, h, Rv.tick(h, r))

# with no refresh (h = 0) a run only counts on
def rvb.since_zero(c: Nat, +r: Nat) -> {Nat.add(c, r) == Rv.since(c, 0n, r) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n++p:
      %LNat.wn_add_succ_r(p, r) : {_ == Rv.since(p, 0n, 1n+r) : Nat}
      rvb.since_zero(p, 1n+r)

# the remainder loop of Nat.mod, r counted and m left before its wrap, runs
# as a run with a refresh every r + m + 1 ms
def rvb.go_since(n: Nat, m: Nat, -d: Nat, +r: Nat) -> {Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)) == Rv.since(n, 1n+Nat.add(r, m), r) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          %Equal.sym(Nat, Nat.add(r, 0n), r, LNat.wn_add_zero_r(r)) : {Pair.snd(Nat, Nat, Nat.divmod.go(1n+np, 0n, d, r)) == Rv.since(1n+np, 1n+_, r) : Nat}
          %Equal.sym(Bool, Nat.is_eq(r, r), True{}, LNat.child.pc.eq_refl(r)) : {Pair.snd(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n)) == Rv.since(np, 1n+r, Rv.tick.put(_, r)) : Nat}
          rvb.go_since(np, r, 1n+d, 0n)
        case 1n+mp:
          %Equal.sym(Nat, Nat.add(r, 1n+mp), 1n+Nat.add(r, mp), LNat.wn_add_succ_r(r, mp)) : {Pair.snd(Nat, Nat, Nat.divmod.go(1n+np, 1n+mp, d, r)) == Rv.since(1n+np, 1n+_, r) : Nat}
          %Equal.sym(Bool, Nat.is_eq(r, 1n+Nat.add(r, mp)), False{}, rvb.ne_more(r, mp)) : {Pair.snd(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r)) == Rv.since(np, 2n+Nat.add(r, mp), Rv.tick.put(_, r)) : Nat}
          rvb.go_since(np, mp, d, 1n+r)

# c mod h is the time since the last record of a run c ms from its start
def rvb.mod_since(+c: Nat, +h: Nat) -> {Nat.mod(c, h) == Rv.since(c, h, 0n) : Nat}:
  match h:
    case 0n:
      %LNat.wn_add_zero_r(c) : {_ == Rv.since(c, 0n, 0n) : Nat}
      rvb.since_zero(c, 0n)
    case 1n+bp:
      rvb.go_since(c, bp, 0n, 0n)

# a tick takes c mod h to (c + 1) mod h
def rvb.mod_step(+c: Nat, +h: Nat) -> {Nat.mod(1n+c, h) == Rv.tick(h, Nat.mod(c, h)) : Nat}:
  %Equal.sym(Nat, Nat.mod(1n+c, h), Rv.since(1n+c, h, 0n), rvb.mod_since(1n+c, h)) : {_ == Rv.tick(h, Nat.mod(c, h)) : Nat}
  %Equal.sym(Nat, Nat.mod(c, h), Rv.since(c, h, 0n), rvb.mod_since(c, h)) : {Rv.since(1n+c, h, 0n) == Rv.tick(h, _) : Nat}
  rvb.since_snoc(c, h, 0n)

# c more ms from x mod h leave (x + c) mod h
def rvb.since_mod(c: Nat, +h: Nat, +x: Nat) -> {Rv.since(c, h, Nat.mod(x, h)) == Nat.mod(Nat.add(x, c), h) : Nat}:
  match c:
    case 0n:
      %Equal.sym(Nat, Nat.add(x, 0n), x, LNat.wn_add_zero_r(x)) : {Nat.mod(x, h) == Nat.mod(_, h) : Nat}
      {==}
    case 1n+p:
      %rvb.mod_step(x, h) : {Rv.since(p, h, _) == Nat.mod(Nat.add(x, 1n+p), h) : Nat}
      %Equal.sym(Nat, Nat.add(x, 1n+p), 1n+Nat.add(x, p), LNat.wn_add_succ_r(x, p)) : {Rv.since(p, h, Nat.mod(1n+x, h)) == Nat.mod(_, h) : Nat}
      rvb.since_mod(p, h, 1n+x)
