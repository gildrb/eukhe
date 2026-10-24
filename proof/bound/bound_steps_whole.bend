# eukhe: the proof of LAW bound_steps_whole: every text adds its bytes and newlines and sets whether the output ends inside a line, whatever the stream stored; a look reads only those counts

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

# a stream's counts, its stored bytes set aside
def sw.cnt(s: Bd.St) -> Bd.St:
  match s:
    case Bd.St{c, b, nl, op, sd}:
      Bd.St{c, b, nl, op, 0n}

def sw.head(f: Bool, +c: Bd.Cap, +b: Nat, +nl: Nat, o: Bool, +sd: Nat, +n: Nat) -> {sw.cnt(Bound.bd_fst.act(Bd.out.head(f, c, b, nl, o, sd, n))) == Bd.St{c, b, nl, o, 0n} : Bd.St}:
  match f:
    case True{}:
      {==}
    case False{}:
      {==}

def sw.tail(tr: Bool, +c: Bd.Cap, +b: Nat, +nl: Nat, o: Bool, +sd: Nat) -> {sw.cnt(Bound.bd_fst.act(Bd.out.tail(tr, c, b, nl, o, sd))) == Bd.St{c, b, nl, o, 0n} : Bd.St}:
  match tr:
    case True{}:
      {==}
    case False{}:
      {==}

def sw.go(t: Bool, c: Bd.Cap, +b: Nat, +nl: Nat, +sd: Nat, +n: Nat, +k: Nat, o: Bool) -> {sw.cnt(Bound.bd_fst.act(Bd.out.go(t, c, b, nl, sd, n, k, o))) == Bd.St{c, Nat.add(b, n), Nat.add(nl, k), o, 0n} : Bd.St}:
  match t:
    case False{}:
      match c:
        case Bd.Cap{+cb, +ck, +ct}:
          sw.head(Bool.or(Nat.is_lt(cb, b), Nat.is_le(ck, nl)), Bd.Cap{cb, ck, ct}, Nat.add(b, n), Nat.add(nl, k), o, sd, n)
    case True{}:
      match c:
        case Bd.Cap{+cb, +ck, +ct}:
          sw.tail(Nat.is_lt(Nat.add(Nat.add(cb, cb), 8n), Nat.add(sd, n)), Bd.Cap{cb, ck, ct}, Nat.add(b, n), Nat.add(nl, k), o, Nat.add(sd, n))

def sw.cap(s: Bd.St) -> Bd.Cap:
  match s:
    case Bd.St{c, b, nl, op, sd}:
      c

def sw.b(s: Bd.St) -> Nat:
  match s:
    case Bd.St{c, b, nl, op, sd}:
      b

def sw.nl(s: Bd.St) -> Nat:
  match s:
    case Bd.St{c, b, nl, op, sd}:
      nl

# a text adds its counts, whatever the stream stored
def sw.out(s: Bd.St, +n: Nat, +k: Nat, o: Bool) -> {sw.cnt(Bound.bd_fst.act(Bd.out(s, n, k, o))) == Bd.St{sw.cap(s), Nat.add(sw.b(s), n), Nat.add(sw.nl(s), k), o, 0n} : Bd.St}:
  match s:
    case Bd.St{c, +b, +nl, op, +sd}:
      match c:
        case Bd.Cap{+cb, +ck, +ct}:
          sw.go(ct, Bd.Cap{cb, ck, ct}, b, nl, sd, n, k, o)

def sw.cnt_eq(s: Bd.St, +rest: List<&2, Bound.BdText>, +n: Nat, +k: Nat, o: Bool) -> {sw.cnt(Bound.bd_drive(rest, Bd.St{sw.cap(s), Nat.add(sw.b(s), n), Nat.add(sw.nl(s), k), o, 0n})) == sw.cnt(Bound.bd_drive(rest, Bd.St{sw.cap(sw.cnt(s)), Nat.add(sw.b(sw.cnt(s)), n), Nat.add(sw.nl(sw.cnt(s)), k), o, 0n})) : Bd.St}:
  match s:
    case Bd.St{c, b, nl, op, sd}:
      {==}

# the counts after the texts depend only on the counts before them
def sw.same(es: List<&2, Bound.BdText>, +s: Bd.St) -> {sw.cnt(Bound.bd_drive(es, s)) == sw.cnt(Bound.bd_drive(es, sw.cnt(s))) : Bd.St}:
  match es:
    case Nil{}:
      match s:
        case Bd.St{c, b, nl, op, sd}:
          {==}
    case +e <> +rest:
      match e:
        case Bound.BdText{+n, +k, +o}:
          +s1 = Bound.bd_fst.act(Bd.out(s, n, k, o))
          +s2 = Bound.bd_fst.act(Bd.out(sw.cnt(s), n, k, o))
          %Equal.sym(Bd.St, sw.cnt(Bound.bd_drive(rest, s1)), sw.cnt(Bound.bd_drive(rest, sw.cnt(s1))), sw.same(rest, s1)) : {_ == sw.cnt(Bound.bd_drive(rest, s2)) : Bd.St}
          %Equal.sym(Bd.St, sw.cnt(Bound.bd_drive(rest, s2)), sw.cnt(Bound.bd_drive(rest, sw.cnt(s2))), sw.same(rest, s2)) : {sw.cnt(Bound.bd_drive(rest, sw.cnt(s1))) == _ : Bd.St}
          %Equal.sym(Bd.St, sw.cnt(s1), Bd.St{sw.cap(s), Nat.add(sw.b(s), n), Nat.add(sw.nl(s), k), o, 0n}, sw.out(s, n, k, o)) : {sw.cnt(Bound.bd_drive(rest, _)) == sw.cnt(Bound.bd_drive(rest, sw.cnt(s2))) : Bd.St}
          %Equal.sym(Bd.St, sw.cnt(s2), Bd.St{sw.cap(sw.cnt(s)), Nat.add(sw.b(sw.cnt(s)), n), Nat.add(sw.nl(sw.cnt(s)), k), o, 0n}, sw.out(sw.cnt(s), n, k, o)) : {sw.cnt(Bound.bd_drive(rest, Bd.St{sw.cap(s), Nat.add(sw.b(s), n), Nat.add(sw.nl(s), k), o, 0n})) == sw.cnt(Bound.bd_drive(rest, _)) : Bd.St}
          sw.cnt_eq(s, rest, n, k, o)

def sw.sum(es: List<&2, Bound.BdText>, +c: Bd.Cap, +b: Nat, +nl: Nat, op: Bool) -> {sw.cnt(Bound.bd_drive(es, Bd.St{c, b, nl, op, 0n})) == Bd.St{c, Nat.add(b, Bound.bd_sum_n(es)), Nat.add(nl, Bound.bd_sum_k(es)), Bound.bd_last(es, op), 0n} : Bd.St}:
  match es:
    case Nil{}:
      %Equal.sym(Nat, Nat.add(b, 0n), b, LBound.bnd.add_zero(b)) : {Bd.St{c, b, nl, op, 0n} == Bd.St{c, _, Nat.add(nl, 0n), op, 0n} : Bd.St}
      %Equal.sym(Nat, Nat.add(nl, 0n), nl, LBound.bnd.add_zero(nl)) : {Bd.St{c, b, nl, op, 0n} == Bd.St{c, b, _, op, 0n} : Bd.St}
      {==}
    case +e <> +rest:
      match e:
        case Bound.BdText{+n, +k, +o}:
          +s0 = {Bd.St{c, b, nl, op, 0n} : Bd.St}
          +s1 = Bound.bd_fst.act(Bd.out(s0, n, k, o))
          %Equal.sym(Bd.St, sw.cnt(Bound.bd_drive(rest, s1)), sw.cnt(Bound.bd_drive(rest, sw.cnt(s1))), sw.same(rest, s1)) : {_ == Bd.St{c, Nat.add(b, Nat.add(n, Bound.bd_sum_n(rest))), Nat.add(nl, Nat.add(k, Bound.bd_sum_k(rest))), Bound.bd_last(rest, o), 0n} : Bd.St}
          %Equal.sym(Bd.St, sw.cnt(s1), Bd.St{c, Nat.add(b, n), Nat.add(nl, k), o, 0n}, sw.out(s0, n, k, o)) : {sw.cnt(Bound.bd_drive(rest, _)) == Bd.St{c, Nat.add(b, Nat.add(n, Bound.bd_sum_n(rest))), Nat.add(nl, Nat.add(k, Bound.bd_sum_k(rest))), Bound.bd_last(rest, o), 0n} : Bd.St}
          %Equal.sym(Bd.St, sw.cnt(Bound.bd_drive(rest, Bd.St{c, Nat.add(b, n), Nat.add(nl, k), o, 0n})), Bd.St{c, Nat.add(Nat.add(b, n), Bound.bd_sum_n(rest)), Nat.add(Nat.add(nl, k), Bound.bd_sum_k(rest)), Bound.bd_last(rest, o), 0n}, sw.sum(rest, c, Nat.add(b, n), Nat.add(nl, k), o)) : {_ == Bd.St{c, Nat.add(b, Nat.add(n, Bound.bd_sum_n(rest))), Nat.add(nl, Nat.add(k, Bound.bd_sum_k(rest))), Bound.bd_last(rest, o), 0n} : Bd.St}
          %LBound.bnd.add_assoc(b, n, Bound.bd_sum_n(rest)) : {Bd.St{c, Nat.add(Nat.add(b, n), Bound.bd_sum_n(rest)), Nat.add(Nat.add(nl, k), Bound.bd_sum_k(rest)), Bound.bd_last(rest, o), 0n} == Bd.St{c, _, Nat.add(nl, Nat.add(k, Bound.bd_sum_k(rest))), Bound.bd_last(rest, o), 0n} : Bd.St}
          %LBound.bnd.add_assoc(nl, k, Bound.bd_sum_k(rest)) : {Bd.St{c, Nat.add(Nat.add(b, n), Bound.bd_sum_n(rest)), Nat.add(Nat.add(nl, k), Bound.bd_sum_k(rest)), Bound.bd_last(rest, o), 0n} == Bd.St{c, Nat.add(Nat.add(b, n), Bound.bd_sum_n(rest)), _, Bound.bd_last(rest, o), 0n} : Bd.St}
          {==}

# a look reads only the counts
def sw.look(s: Bd.St, x: Bd.Body) -> {Bound.bd_seen_slice(Bd.look(s, x)) == Bound.bd_seen_slice(Bd.look(sw.cnt(s), x)) : Bd.Slice}:
  match s:
    case Bd.St{c, b, nl, op, sd}:
      match x:
        case Bd.Body{xs, o, hc, tc, mc}:
          {==}

def sw.fin(w: Bd.Win, +c: Bd.Cap, +x: Bd.Body, +len: Nat, +n: Nat, +nk: Nat, l: Bool, hl: {n == Bound.bd_lines(nk, l) : Nat}) -> {Bound.bd_seen_slice(Bd.look.of(c, len, nk, l, x, len, w)) == Bd.slice.of(Bd.Cap.tail(c), len, n, w) : Bd.Slice}:
  match w:
    case Bd.Win{+kb, +kl}:
      match l:
        case False{}:
          %hl : {Bd.Slice{Bd.span.of(Bd.Cap.tail(c), len, kb), Nat.sub(len, kb), Nat.sub(_, kl)} == Bd.Slice{Bd.span.of(Bd.Cap.tail(c), len, kb), Nat.sub(len, kb), Nat.sub(n, kl)} : Bd.Slice}
          {==}
        case True{}:
          %hl : {Bd.Slice{Bd.span.of(Bd.Cap.tail(c), len, kb), Nat.sub(len, kb), Nat.sub(_, kl)} == Bd.Slice{Bd.span.of(Bd.Cap.tail(c), len, kb), Nat.sub(len, kb), Nat.sub(n, kl)} : Bd.Slice}
          {==}

def Bound.bound_steps_whole(c, es, x, bytes, lines):
  match x:
    case Bd.Body{+xs, +o, +hc, +tc, +mc}:
      +bx = {Bd.Body{xs, o, hc, tc, mc} : Bd.Body}
      +d = Bound.bd_drive(es, Bd.St{c, 0n, 0n, False{}, 0n})
      +nk = Bound.bd_sum_k(es)
      +l = Bound.bd_last(es, False{})
      %Equal.sym(Bd.Slice, Bound.bd_seen_slice(Bd.look(d, bx)), Bound.bd_seen_slice(Bd.look(sw.cnt(d), bx)), sw.look(d, bx)) : {_ == Bd.slice(c, bx) : Bd.Slice}
      %Equal.sym(Bd.St, sw.cnt(d), Bd.St{c, Bound.bd_sum_n(es), nk, l, 0n}, sw.sum(es, c, 0n, 0n, False{})) : {Bound.bd_seen_slice(Bd.look(_, bx)) == Bd.slice(c, bx) : Bd.Slice}
      %bytes : {Bound.bd_seen_slice(Bd.look(Bd.St{c, _, nk, l, 0n}, bx)) == Bd.slice(c, bx) : Bd.Slice}
      %Equal.sym(Nat, Bd.total(xs), Bound.bd_total(xs), LBound.bnd.total(xs)) : {Bound.bd_seen_slice(Bd.look.of(c, Bound.bd_total(xs), nk, l, bx, _, Bd.window(c, bx))) == Bd.slice.of(Bd.Cap.tail(c), _, List.length(&2, Nat, xs), Bd.window(c, bx)) : Bd.Slice}
      sw.fin(Bd.window(c, bx), c, bx, Bound.bd_total(xs), List.length(&2, Nat, xs), nk, l, lines)
