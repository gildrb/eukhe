# eukhe: the proof of LAW lease_keeps_holder
# An ask and a stop never touch the holder; a release frees it only for
# its key, a crash only for its origin: otherwise the holder stays.

import Base
import ../../bend/lease.bend as Ls
import ../../laws/lease.bend as Lease
import ./base.bend as LA

def kh.MD(m: Maybe<&2, Ls.Lease>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

def kh.none_some(-G: Type, -x: Ls.Lease, h: {None{} == Some{x} : Maybe<&2, Ls.Lease>}) -> G:
  %h : kh.MD(_, G)
  Unit{}

def kh.key(m: Maybe<&2, Ls.Lease>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{x}:
      match x:
        case Ls.Lease{k, o}:
          k

def kh.org(m: Maybe<&2, Ls.Lease>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{x}:
      match x:
        case Ls.Lease{k, o}:
          o

# a release of another key keeps the holder
def kh.rel(hit: Bool, +hk: Nat, +ho: Nat, +j: Nat, +n: Nat, +q: List<&2, Ls.Waiter>, eh: {hit == False{} : Bool}) -> {Ls.L.holder(Ls.release.holder(hit, Ls.Lease{hk, ho}, j, n, q)) == Some{Ls.Lease{hk, ho}} : Maybe<&2, Ls.Lease>}:
  match hit:
    case True{}:
      LA.lease.pl.absurd({Ls.L.holder(Ls.release.holder(True{}, Ls.Lease{hk, ho}, j, n, q)) == Some{Ls.Lease{hk, ho}} : Maybe<&2, Ls.Lease>}, eh)
    case False{}:
      {==}

# a crash of another origin keeps the holder
def kh.cra(hit: Bool, +hk: Nat, +ho: Nat, +n: Nat, +d: List<&2, Ls.Waiter>, eh: {hit == False{} : Bool}) -> {Ls.L.holder(Ls.settle(n, Ls.crash.put(hit, Ls.Lease{hk, ho}), d)) == Some{Ls.Lease{hk, ho}} : Maybe<&2, Ls.Lease>}:
  match hit:
    case True{}:
      LA.lease.pl.absurd({Ls.L.holder(Ls.settle(n, Ls.crash.put(True{}, Ls.Lease{hk, ho}), d)) == Some{Ls.Lease{hk, ho}} : Maybe<&2, Ls.Lease>}, eh)
    case False{}:
      {==}

# a key equal to one that is not j is not j
def kh.ne_at(+a: Nat, +b: Nat, +j: Nat, e: {a == b : Nat}, f: {Nat.is_eq(b, j) == False{} : Bool}) -> {Nat.is_eq(a, j) == False{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {Nat.is_eq(_, j) == False{} : Bool}
  f

def kh.go(+n: Nat, h: Maybe<&2, Ls.Lease>, +q: List<&2, Ls.Waiter>, +e: Ls.Ev, +k: Nat, +o: Nat, +holds: {h == Some{Ls.Lease{k, o}} : Maybe<&2, Ls.Lease>}, other: {Ls.hits(e, Ls.Waiter{k, o, True{}}) == False{} : Bool}) -> {Ls.L.holder(Ls.step(Ls.L{n, h, q}, e)) == Some{Ls.Lease{k, o}} : Maybe<&2, Ls.Lease>}:
  match h:
    case None{}:
      kh.none_some({Ls.L.holder(Ls.step(Ls.L{n, None{}, q}, e)) == Some{Ls.Lease{k, o}} : Maybe<&2, Ls.Lease>}, Ls.Lease{k, o}, holds)
    case Some{x}:
      match x:
        case Ls.Lease{+hk, +ho}:
          match e:
            case Ls.Ask{p}:
              holds
            case Ls.Release{+j}:
              +ek = Equal.cong(Maybe<&2, Ls.Lease>, Nat, m => kh.key(m), Some{Ls.Lease{hk, ho}}, Some{Ls.Lease{k, o}}, holds)
              Equal.trans(Maybe<&2, Ls.Lease>, Ls.L.holder(Ls.release.holder(Nat.is_eq(hk, j), Ls.Lease{hk, ho}, j, n, q)), Some{Ls.Lease{hk, ho}}, Some{Ls.Lease{k, o}}, kh.rel(Nat.is_eq(hk, j), hk, ho, j, n, q, kh.ne_at(hk, k, j, ek, other)), holds)
            case Ls.Stop{j}:
              holds
            case Ls.Crash{+p}:
              +eo = Equal.cong(Maybe<&2, Ls.Lease>, Nat, m => kh.org(m), Some{Ls.Lease{hk, ho}}, Some{Ls.Lease{k, o}}, holds)
              Equal.trans(Maybe<&2, Ls.Lease>, Ls.L.holder(Ls.settle(n, Ls.crash.put(Nat.is_eq(ho, p), Ls.Lease{hk, ho}), Ls.drop(Ls.Crash{p}, q))), Some{Ls.Lease{hk, ho}}, Some{Ls.Lease{k, o}}, kh.cra(Nat.is_eq(ho, p), hk, ho, n, Ls.drop(Ls.Crash{p}, q), kh.ne_at(ho, o, p, eo, other)), holds)

def Lease.lease_keeps_holder(s, e, k, o, holds, other):
  match s:
    case Ls.L{n, h, q}:
      kh.go(n, h, q, e, k, o, holds, other)
