# eukhe: the proof of LAW lease_step_exact
# Piece by piece: the model's pick and after are the laws' first and rest,
# its drop is the laws' left (its `hits` is the laws', lease_hits_exact),
# its mark is the laws' dead, its crash of the holder is the laws' unless;
# so each settle, and each step, is the laws'.

import Base
import ../../bend/lease.bend as Ls
import ../../laws/lease.bend as Lease
import ./lease_hits_exact.bend as PHits

def se.first(q: List<&2, Ls.Waiter>) -> {Ls.pick(q) == Lease.lw_first(q) : Maybe<&2, Ls.Lease>}:
  match q:
    case Nil{}:
      {==}
    case w <> t:
      match w:
        case Ls.Waiter{k, o, l}:
          match l:
            case True{}:
              {==}
            case False{}:
              se.first(t)

def se.rest(q: List<&2, Ls.Waiter>) -> {Ls.after(q) == Lease.lw_rest(q) : List<&2, Ls.Waiter>}:
  match q:
    case Nil{}:
      {==}
    case w <> t:
      match w:
        case Ls.Waiter{k, o, l}:
          match l:
            case True{}:
              {==}
            case False{}:
              se.rest(t)

def se.settle(+n: Nat, h: Maybe<&2, Ls.Lease>, +q: List<&2, Ls.Waiter>) -> {Ls.settle(n, h, q) == Lease.lw_settle(n, h, q) : Ls.L}:
  match h:
    case None{}:
      %se.first(q) : {Ls.L{n, Ls.pick(q), Ls.after(q)} == Ls.L{n, _, Lease.lw_rest(q)} : Ls.L}
      %se.rest(q) : {Ls.L{n, Ls.pick(q), Ls.after(q)} == Ls.L{n, Ls.pick(q), _} : Ls.L}
      {==}
    case Some{x}:
      {==}

def se.settle_at(+n: Nat, +h1: Maybe<&2, Ls.Lease>, -h2: Maybe<&2, Ls.Lease>, +q1: List<&2, Ls.Waiter>, -q2: List<&2, Ls.Waiter>, eh: {h1 == h2 : Maybe<&2, Ls.Lease>}, eq: {q1 == q2 : List<&2, Ls.Waiter>}) -> {Ls.settle(n, h1, q1) == Lease.lw_settle(n, h2, q2) : Ls.L}:
  %eh : {Ls.settle(n, h1, q1) == Lease.lw_settle(n, _, q2) : Ls.L}
  %eq : {Ls.settle(n, h1, q1) == Lease.lw_settle(n, h1, _) : Ls.L}
  se.settle(n, h1, q1)

def se.keep(b: Bool, w: Ls.Waiter, r: List<&2, Ls.Waiter>) -> {Ls.drop.put(b, w, r) == Lease.lw_keep(b, w, r) : List<&2, Ls.Waiter>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def se.left(+e: Ls.Ev, q: List<&2, Ls.Waiter>) -> {Ls.drop(e, q) == Lease.lw_left(e, q) : List<&2, Ls.Waiter>}:
  match q:
    case Nil{}:
      {==}
    case w <> +t:
      match w:
        case Ls.Waiter{+k, +o, +l}:
          +x = {Ls.Waiter{k, o, l} : Ls.Waiter}
          %se.left(e, t) : {Ls.drop.put(Ls.hits(e, x), x, Ls.drop(e, t)) == Lease.lw_keep(Lease.lw_hits(e, k, o), x, _) : List<&2, Ls.Waiter>}
          %Lease.lease_hits_exact(e, k, o, l) : {Ls.drop.put(Ls.hits(e, x), x, Ls.drop(e, t)) == Lease.lw_keep(_, x, Ls.drop(e, t)) : List<&2, Ls.Waiter>}
          se.keep(Ls.hits(e, x), x, Ls.drop(e, t))

def se.one(b: Bool, +k: Nat, +o: Nat, l: Bool) -> {Ls.Waiter{k, o, Bool.and(l, Bool.not(b))} == Lease.lw_dead.one(b, k, o, l) : Ls.Waiter}:
  match b:
    case True{}:
      match l:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match l:
        case True{}:
          {==}
        case False{}:
          {==}

def se.dead(+j: Nat, q: List<&2, Ls.Waiter>) -> {Ls.mark(Ls.Stop{j}, q) == Lease.lw_dead(j, q) : List<&2, Ls.Waiter>}:
  match q:
    case Nil{}:
      {==}
    case w <> +t:
      match w:
        case Ls.Waiter{+k, +o, +l}:
          +w1 = {Ls.Waiter{k, o, Bool.and(l, Bool.not(Nat.is_eq(k, j)))} : Ls.Waiter}
          %se.dead(j, t) : {w1 <> Ls.mark(Ls.Stop{j}, t) == Lease.lw_dead.one(Nat.is_eq(k, j), k, o, l) <> _ : List<&2, Ls.Waiter>}
          %se.one(Nat.is_eq(k, j), k, o, l) : {w1 <> Ls.mark(Ls.Stop{j}, t) == _ <> Ls.mark(Ls.Stop{j}, t) : List<&2, Ls.Waiter>}
          {==}

def se.unless_put(b: Bool, x: Ls.Lease) -> {Ls.crash.put(b, x) == Lease.lw_unless.put(b, x) : Maybe<&2, Ls.Lease>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def se.unless(+p: Nat, h: Maybe<&2, Ls.Lease>) -> {Ls.crash.holder(p, h) == Lease.lw_unless(h, p) : Maybe<&2, Ls.Lease>}:
  match h:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case Ls.Lease{hk, +ho}:
          se.unless_put(Nat.is_eq(ho, p), Ls.Lease{hk, ho})

def se.rel(b: Bool, +hk: Nat, +ho: Nat, +j: Nat, +n: Nat, +q: List<&2, Ls.Waiter>) -> {Ls.release.holder(b, Ls.Lease{hk, ho}, j, n, q) == Lease.lw_release(b, j, n, Some{Ls.Lease{hk, ho}}, q) : Ls.L}:
  match b:
    case True{}:
      se.settle(n, None{}, q)
    case False{}:
      %se.left(Ls.Release{j}, q) : {Ls.L{n, Some{Ls.Lease{hk, ho}}, Ls.drop(Ls.Release{j}, q)} == Ls.L{n, Some{Ls.Lease{hk, ho}}, _} : Ls.L}
      {==}

def se.release(+j: Nat, +n: Nat, h: Maybe<&2, Ls.Lease>, +q: List<&2, Ls.Waiter>) -> {Ls.release(j, n, h, q) == Lease.lw_release(Lease.lw_is(Lease.lw_hkey(h), j), j, n, h, q) : Ls.L}:
  match h:
    case None{}:
      se.settle_at(n, None{}, None{}, Ls.drop(Ls.Release{j}, q), Lease.lw_left(Ls.Release{j}, q), {==}, se.left(Ls.Release{j}, q))
    case Some{x}:
      match x:
        case Ls.Lease{+hk, +ho}:
          se.rel(Nat.is_eq(hk, j), hk, ho, j, n, q)

def se.step(+s: Ls.L, +e: Ls.Ev) -> {Ls.step(s, e) == Lease.lw_step(s, e) : Ls.L}:
  match s:
    case Ls.L{+n, h, +q}:
      match e:
        case Ls.Ask{+o}:
          se.settle(1n+n, h, List.append(&2, Ls.Waiter, q, [Ls.Waiter{n, o, True{}}]))
        case Ls.Release{+j}:
          se.release(j, n, h, q)
        case Ls.Stop{+j}:
          %se.dead(j, q) : {Ls.L{n, h, Ls.mark(Ls.Stop{j}, q)} == Ls.L{n, h, _} : Ls.L}
          {==}
        case Ls.Crash{+p}:
          se.settle_at(n, Ls.crash.holder(p, h), Lease.lw_unless(h, p), Ls.drop(Ls.Crash{p}, q), Lease.lw_left(Ls.Crash{p}, q), se.unless(p, h), se.left(Ls.Crash{p}, q))

def Lease.lease_step_exact(s, e):
  se.step(s, e)
