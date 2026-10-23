# eukhe: the proof of LAW lease_keeps_waiters

import Base
import ../../bend/lease.bend as Ls
import ../../laws/lease.bend as Lease
import ./base.bend as LA

def pl.MD(m: Maybe<&2, Ls.Lease>, A: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      A

def pl.none_some(-A: Type, -x: Ls.Lease, e: {None{} == Some{x} : Maybe<&2, Ls.Lease>}) -> A:
  %e : pl.MD(_, A)
  Unit{}

# Waiters
# -------

def pl.org(w: Ls.Waiter) -> Nat:
  match w:
    case Ls.Waiter{k, o, l}:
      o

def pl.lease_of(w: Ls.Waiter) -> Maybe<&2, Ls.Lease>:
  match w:
    case Ls.Waiter{k, o, l}:
      Some{Ls.Lease{k, o}}

def pl.in_append(+x: Ls.Waiter, q: List<&2, Ls.Waiter>, +ys: List<&2, Ls.Waiter>, i: Ls.In(x, q)) -> Ls.In(x, List.append(&2, Ls.Waiter, q, ys)):
  match q:
    case Nil{}:
      match i:
    case +w <> +t:
      match i:
        case Inl{eq}:
          Inl{eq}
        case Inr{it}:
          Inr{pl.in_append(x, t, ys, it)}

def pl.in_put(b: Bool, +w: Ls.Waiter, +x: Ls.Waiter, +r: List<&2, Ls.Waiter>, i: Ls.In(x, r)) -> Ls.In(x, Ls.drop.put(b, w, r)):
  match b:
    case True{}:
      i
    case False{}:
      Inr{i}

# a waiter e does not end stays
def pl.in_drop(+e: Ls.Ev, q: List<&2, Ls.Waiter>, +x: Ls.Waiter, i: Ls.In(x, q), miss: {Ls.hits(e, x) == False{} : Bool}) -> Ls.In(x, Ls.drop(e, q)):
  match q:
    case Nil{}:
      match i:
    case +w <> +t:
      match i:
        case Inl{eq}:
          %eq : Ls.In(x, Ls.drop.put(Ls.hits(e, _), _, Ls.drop(e, t)))
          %Equal.sym(Bool, Ls.hits(e, x), False{}, miss) : Ls.In(x, Ls.drop.put(_, x, Ls.drop(e, t)))
          Inl{{==}}
        case Inr{it}:
          pl.in_put(Ls.hits(e, w), w, x, Ls.drop(e, t), pl.in_drop(e, t, x, it, miss))

# and stays live
def pl.in_mark(+e: Ls.Ev, q: List<&2, Ls.Waiter>, +k: Nat, +o: Nat, i: Ls.In(Ls.Waiter{k, o, True{}}, q), miss: {Ls.hits(e, Ls.Waiter{k, o, True{}}) == False{} : Bool}) -> Ls.In(Ls.Waiter{k, o, True{}}, Ls.mark(e, q)):
  match q:
    case Nil{}:
      match i:
    case w <> +t:
      match w:
        case Ls.Waiter{+wk, +wo, +wl}:
          match i:
            case Inl{+eq}:
              +ek = Equal.cong(Ls.Waiter, Nat, v => Ls.Waiter.key(v), Ls.Waiter{k, o, True{}}, Ls.Waiter{wk, wo, wl}, eq)
              +eo = Equal.cong(Ls.Waiter, Nat, v => pl.org(v), Ls.Waiter{k, o, True{}}, Ls.Waiter{wk, wo, wl}, eq)
              +el = Equal.cong(Ls.Waiter, Bool, v => Ls.Waiter.live(v), Ls.Waiter{k, o, True{}}, Ls.Waiter{wk, wo, wl}, eq)
              %ek : Ls.In(Ls.Waiter{k, o, True{}}, Ls.Waiter{_, wo, Bool.and(wl, Bool.not(Ls.hits(e, Ls.Waiter{_, wo, wl})))} <> Ls.mark(e, t))
              %eo : Ls.In(Ls.Waiter{k, o, True{}}, Ls.Waiter{k, _, Bool.and(wl, Bool.not(Ls.hits(e, Ls.Waiter{k, _, wl})))} <> Ls.mark(e, t))
              %el : Ls.In(Ls.Waiter{k, o, True{}}, Ls.Waiter{k, o, Bool.and(_, Bool.not(Ls.hits(e, Ls.Waiter{k, o, _})))} <> Ls.mark(e, t))
              %Equal.sym(Bool, Ls.hits(e, Ls.Waiter{k, o, True{}}), False{}, miss) : Ls.In(Ls.Waiter{k, o, True{}}, Ls.Waiter{k, o, Bool.and(True{}, Bool.not(_))} <> Ls.mark(e, t))
              Inl{{==}}
            case Inr{it}:
              Inr{pl.in_mark(e, t, k, o, it, miss)}

# Kept: no event drops a waiter it does not name
# ----------------------------------------------

def pl.pick_kept(+k: Nat, +o: Nat, +n: Nat, q: List<&2, Ls.Waiter>, i: Ls.In(Ls.Waiter{k, o, True{}}, q)) -> Ls.Kept(k, o, Ls.L{n, Ls.pick(q), Ls.after(q)}):
  match q:
    case Nil{}:
      match i:
    case w <> +t:
      match w:
        case Ls.Waiter{+wk, +wo, +wl}:
          match wl:
            case True{}:
              match i:
                case Inl{eq}:
                  Inl{Equal.sym(Maybe<&2, Ls.Lease>, Some{Ls.Lease{k, o}}, Some{Ls.Lease{wk, wo}}, Equal.cong(Ls.Waiter, Maybe<&2, Ls.Lease>, v => pl.lease_of(v), Ls.Waiter{k, o, True{}}, Ls.Waiter{wk, wo, True{}}, eq))}
                case Inr{it}:
                  Inr{it}
            case False{}:
              match i:
                case Inl{eq}:
                  LA.lease.pl.absurd(Ls.Kept(k, o, Ls.L{n, Ls.pick(t), Ls.after(t)}), Equal.cong(Ls.Waiter, Bool, v => Ls.Waiter.live(v), Ls.Waiter{k, o, True{}}, Ls.Waiter{wk, wo, False{}}, eq))
                case Inr{it}:
                  pl.pick_kept(k, o, n, t, it)

def pl.settle_kept(+k: Nat, +o: Nat, +n: Nat, h: Maybe<&2, Ls.Lease>, +q: List<&2, Ls.Waiter>, kp: Or({h == Some{Ls.Lease{k, o}} : Maybe<&2, Ls.Lease>}, Ls.In(Ls.Waiter{k, o, True{}}, q))) -> Ls.Kept(k, o, Ls.settle(n, h, q)):
  match h:
    case None{}:
      match kp:
        case Inl{e}:
          pl.none_some(Ls.Kept(k, o, Ls.settle(n, None{}, q)), Ls.Lease{k, o}, e)
        case Inr{i}:
          pl.pick_kept(k, o, n, q, i)
    case Some{x}:
      kp

def pl.release_kept(hit: Bool, +x: Ls.Lease, +j: Nat, +k: Nat, +o: Nat, +n: Nat, +q: List<&2, Ls.Waiter>, i: Ls.In(Ls.Waiter{k, o, True{}}, q), miss: {Nat.is_eq(k, j) == False{} : Bool}) -> Ls.Kept(k, o, Ls.release.holder(hit, x, j, n, q)):
  match hit:
    case True{}:
      pl.settle_kept(k, o, n, None{}, q, Inr{i})
    case False{}:
      Inr{pl.in_drop(Ls.Release{j}, q, Ls.Waiter{k, o, True{}}, i, miss)}

def pl.keeps_release(+j: Nat, +k: Nat, +o: Nat, +n: Nat, h: Maybe<&2, Ls.Lease>, +q: List<&2, Ls.Waiter>, i: Ls.In(Ls.Waiter{k, o, True{}}, q), miss: {Nat.is_eq(k, j) == False{} : Bool}) -> Ls.Kept(k, o, Ls.release(j, n, h, q)):
  match h:
    case None{}:
      pl.settle_kept(k, o, n, None{}, Ls.drop(Ls.Release{j}, q), Inr{pl.in_drop(Ls.Release{j}, q, Ls.Waiter{k, o, True{}}, i, miss)})
    case Some{x}:
      match x:
        case Ls.Lease{+hk, +ho}:
          pl.release_kept(Nat.is_eq(hk, j), Ls.Lease{hk, ho}, j, k, o, n, q, i, miss)

def pl.keeps(+s: Ls.L, +e: Ls.Ev, +k: Nat, +o: Nat, i: Ls.In(Ls.Waiter{k, o, True{}}, Ls.L.queue(s)), miss: {Ls.hits(e, Ls.Waiter{k, o, True{}}) == False{} : Bool}) -> Ls.Kept(k, o, Ls.step(s, e)):
  match s:
    case Ls.L{+n, h, +q}:
      match e:
        case Ls.Ask{p}:
          pl.settle_kept(k, o, 1n+n, h, List.append(&2, Ls.Waiter, q, [Ls.Waiter{n, p, True{}}]), Inr{pl.in_append(Ls.Waiter{k, o, True{}}, q, [Ls.Waiter{n, p, True{}}], i)})
        case Ls.Release{+j}:
          pl.keeps_release(j, k, o, n, h, q, i, miss)
        case Ls.Stop{+j}:
          Inr{pl.in_mark(Ls.Stop{j}, q, k, o, i, miss)}
        case Ls.Crash{+p}:
          pl.settle_kept(k, o, n, Ls.crash.holder(p, h), Ls.drop(Ls.Crash{p}, q), Inr{pl.in_drop(Ls.Crash{p}, q, Ls.Waiter{k, o, True{}}, i, miss)})

def lease_keeps_waiters(+s: Ls.L, +e: Ls.Ev, +k: Nat, +o: Nat, waits: Ls.In(Ls.Waiter{k, o, True{}}, Ls.L.queue(s)), other: {Ls.hits(e, Ls.Waiter{k, o, True{}}) == False{} : Bool}) -> Ls.Kept(k, o, Ls.step(s, e)):
  pl.keeps(s, e, k, o, waits, other)

def Lease.lease_keeps_waiters(s, e, k, o, waits, other):
  lease_keeps_waiters(s, e, k, o, waits, other)
