# eukhe: lemmas the proofs of area revive share

import Base
import ../../bend/ffi_revive.bend as FR
import ../../bend/revive.bend as Rv
import ../../bend/wire.bend as Wr
import ../../laws/revive.bend as Revive

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
