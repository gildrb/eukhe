# proof_infer: the inference layer laws of S6 (forced calls, the strict
# schema budget, the repetition guard, early compaction), about
# bend/infer.bend.
#
# A forced call: by induction on the replies and the retries; a retry's
# tries all carry the provider's support (`pi.flags_sup`). The budget:
# a take and its drop split every count (`pi.count_split`), ranking keeps
# every count (`pi.count_rank`) and sorts by priority (`pi.sorted_rank`),
# and a sorted list's take dominates its drop (`pi.dom_split`). The guard:
# the counter of period p is at least m exactly when the first m chunks
# each equal the chunk p before them (`pi.each_cycle`), so the guard fires
# exactly at a periodic window (`pi.fires_periodic`, `pi.cut_go`,
# `pi.keep_go`), and k equal chunks in a row end in one (`pi.run_loops`,
# `pi.rep_go`). Compaction:
# while below the threshold the next size stays within the limit
# (`pi.compact_go`).

import Base
import ./infer.bend as If

# Logic
# -----

def pi.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pi.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pi.BD(_, Unit, A)
  Unit{}

def pi.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pi.BD(_, A, Unit)
  Unit{}

def pi.void(-A: Type, e: Empty) -> A:
  match e:

def pi.flip(-a: Bool, h: {a == True{} : Bool}, g: {a == False{} : Bool}) -> Empty:
  pi.absurd(Empty, Equal.trans(Bool, True{}, a, False{}, Equal.sym(Bool, a, True{}, h), g))

def pi.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pi.absurdF({False{} == True{} : Bool}, h)

def pi.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pi.absurdF({b == True{} : Bool}, h)

def pi.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def pi.or_l(a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      pi.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pi.or_r(a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      pi.absurd({b == False{} : Bool}, h)
    case False{}:
      h

# Forced calls
# ------------

def pi.fst_next(-t: If.Try, p: List<&2, If.Try> & If.Forced) -> {t <> Pair.fst(List<&2, If.Try>, If.Forced, p) == Pair.fst(List<&2, If.Try>, If.Forced, If.force.next(t, p)) : List<&2, If.Try>}:
  (ts, o) = p
  {==}

def pi.snd_next(-t: If.Try, p: List<&2, If.Try> & If.Forced) -> {Pair.snd(List<&2, If.Try>, If.Forced, p) == Pair.snd(List<&2, If.Try>, If.Forced, If.force.next(t, p)) : If.Forced}:
  (ts, o) = p
  {==}

def pi.le0(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pi.bounded_go(+replies: List<&2, Bool>, +r: Nat, +flag: Bool, +sup: Bool) -> {Nat.is_le(List.length(&2, If.Try, Pair.fst(List<&2, If.Try>, If.Forced, If.force.go(replies, r, flag, sup))), 1n+r) == True{} : Bool}:
  match replies:
    case Nil{}:
      pi.le0(r)
    case c <> rest:
      match c:
        case True{}:
          match r:
            case 0n:
              {==}
            case 1n+q:
              {==}
        case False{}:
          match r:
            case 0n:
              {==}
            case 1n+q:
              %pi.fst_next(If.Try{flag}, If.force.go(rest, q, sup, sup)) : {Nat.is_le(List.length(&2, If.Try, _), 2n+q) == True{} : Bool}
              pi.bounded_go(rest, q, sup, sup)

def pi.first_go(+replies: List<&2, Bool>, +r: Nat, +flag: Bool, +sup: Bool) -> {List.head(&2, If.Try, Pair.fst(List<&2, If.Try>, If.Forced, If.force.go(replies, r, flag, sup))) == Some{If.Try{flag}} : Maybe<&2, If.Try>}:
  match replies:
    case Nil{}:
      {==}
    case c <> rest:
      match c:
        case True{}:
          match r:
            case 0n:
              {==}
            case 1n+q:
              {==}
        case False{}:
          match r:
            case 0n:
              {==}
            case 1n+q:
              %pi.fst_next(If.Try{flag}, If.force.go(rest, q, sup, sup)) : {List.head(&2, If.Try, _) == Some{If.Try{flag}} : Maybe<&2, If.Try>}
              {==}

def pi.nxx(f: Bool) -> {True{} == Bool.not(Bool.xor(f, f)) : Bool}:
  match f:
    case True{}:
      {==}
    case False{}:
      {==}

# every try of a retry carries the provider's support
def pi.flags_sup(+replies: List<&2, Bool>, +r: Nat, +f: Bool) -> {If.flags(Pair.fst(List<&2, If.Try>, If.Forced, If.force.go(replies, r, f, f)), f) == True{} : Bool}:
  match replies:
    case Nil{}:
      %pi.nxx(f) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case c <> rest:
      match c:
        case True{}:
          match r:
            case 0n:
              %pi.nxx(f) : {Bool.and(_, True{}) == True{} : Bool}
              {==}
            case 1n+q:
              %pi.nxx(f) : {Bool.and(_, True{}) == True{} : Bool}
              {==}
        case False{}:
          match r:
            case 0n:
              %pi.nxx(f) : {Bool.and(_, True{}) == True{} : Bool}
              {==}
            case 1n+q:
              -F = Pair.fst(List<&2, If.Try>, If.Forced, If.force.go(rest, q, f, f))
              %pi.fst_next(If.Try{f}, If.force.go(rest, q, f, f)) : {If.flags(_, f) == True{} : Bool}
              %pi.nxx(f) : {Bool.and(_, If.flags(F, f)) == True{} : Bool}
              pi.flags_sup(rest, q, f)

def pi.drop0(xs: List<&2, If.Try>) -> {xs == List.drop(&2, If.Try, xs, 0n) : List<&2, If.Try>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

def pi.retry_go(+replies: List<&2, Bool>, +r: Nat, +flag: Bool, +sup: Bool) -> {If.flags(List.drop(&2, If.Try, Pair.fst(List<&2, If.Try>, If.Forced, If.force.go(replies, r, flag, sup)), 1n), sup) == True{} : Bool}:
  match replies:
    case Nil{}:
      {==}
    case c <> rest:
      match c:
        case True{}:
          match r:
            case 0n:
              {==}
            case 1n+q:
              {==}
        case False{}:
          match r:
            case 0n:
              {==}
            case 1n+q:
              %pi.fst_next(If.Try{flag}, If.force.go(rest, q, sup, sup)) : {If.flags(List.drop(&2, If.Try, _, 1n), sup) == True{} : Bool}
              %pi.drop0(Pair.fst(List<&2, If.Try>, If.Forced, If.force.go(rest, q, sup, sup))) : {If.flags(_, sup) == True{} : Bool}
              pi.flags_sup(rest, q, sup)

def pi.reports_go(+replies: List<&2, Bool>, +r: Nat, +flag: Bool, +sup: Bool) -> {If.Forced.called(Pair.snd(List<&2, If.Try>, If.Forced, If.force.go(replies, r, flag, sup))) == If.called_within(1n+r, replies) : Bool}:
  match replies:
    case Nil{}:
      {==}
    case c <> rest:
      match c:
        case True{}:
          match r:
            case 0n:
              {==}
            case 1n+q:
              {==}
        case False{}:
          match r:
            case 0n:
              {==}
            case 1n+q:
              %pi.snd_next(If.Try{flag}, If.force.go(rest, q, sup, sup)) : {If.Forced.called(_) == If.called_within(1n+q, rest) : Bool}
              pi.reports_go(rest, q, sup, sup)

def pi.force_bounded(+r: Nat, +replies: List<&2, Bool>, +sup: Bool, +free: Bool) -> {Nat.is_le(List.length(&2, If.Try, Pair.fst(List<&2, If.Try>, If.Forced, If.force(r, replies, sup, free))), 1n+r) == True{} : Bool}:
  pi.bounded_go(replies, r, Bool.and(sup, free), sup)

def pi.force_first_flag(+r: Nat, +replies: List<&2, Bool>, +sup: Bool, +free: Bool) -> {List.head(&2, If.Try, Pair.fst(List<&2, If.Try>, If.Forced, If.force(r, replies, sup, free))) == Some{If.Try{Bool.and(sup, free)}} : Maybe<&2, If.Try>}:
  pi.first_go(replies, r, Bool.and(sup, free), sup)

def pi.force_retry_flag(+r: Nat, +replies: List<&2, Bool>, +sup: Bool, +free: Bool) -> {If.flags(List.drop(&2, If.Try, Pair.fst(List<&2, If.Try>, If.Forced, If.force(r, replies, sup, free)), 1n), sup) == True{} : Bool}:
  pi.retry_go(replies, r, Bool.and(sup, free), sup)

def pi.force_reports(+r: Nat, +replies: List<&2, Bool>, +sup: Bool, +free: Bool) -> {If.Forced.called(Pair.snd(List<&2, If.Try>, If.Forced, If.force(r, replies, sup, free))) == If.called_within(1n+r, replies) : Bool}:
  pi.reports_go(replies, r, Bool.and(sup, free), sup)

# Numbers
# -------

def pi.le_trans(a: Nat, b: Nat, c: Nat, +ab: {Nat.is_le(a, b) == True{} : Bool}, +bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      pi.le0(c)
    case 1n+p 0n _:
      pi.absurdF({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      pi.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      pi.le_trans(p, q, r, ab, bc)

def pi.lt_le(a: Nat, b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      pi.absurdF({True{} == True{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      pi.absurdF({False{} == True{} : Bool}, h)
    case 1n+p 1n+q:
      pi.lt_le(p, q, h)

def pi.nle_le(a: Nat, b: Nat, +h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      pi.absurd({True{} == True{} : Bool}, h)
    case 0n 1n+q:
      pi.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pi.nle_le(p, q, h)

# The strict schema budget
# ------------------------

def pi.take_len(xs: List<&2, If.Tool>, n: Nat) -> {Nat.is_le(List.length(&2, If.Tool, List.take(&2, If.Tool, xs, n)), n) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      pi.le0(n)
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      pi.take_len(t, p)

def pi.strict_within_cap(+cap: Nat, +ts: List<&2, If.Tool>) -> {Nat.is_le(List.length(&2, If.Tool, Pair.fst(List<&2, If.Tool>, List<&2, If.Tool>, If.strict(cap, ts))), cap) == True{} : Bool}:
  pi.take_len(If.rank(ts), cap)

# a count, with one more when b
def pi.cnt(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      1n+n
    case False{}:
      n

def pi.count_go(b: Bool, +h: If.Tool, +X: List<&2, If.Tool>, +i: Nat) -> {pi.cnt(b, If.count(X, i)) == If.count.go(h <> X, i, b) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pi.count_cons(+h: If.Tool, +X: List<&2, If.Tool>, +i: Nat) -> {pi.cnt(Nat.is_eq(If.Tool.id(h), i), If.count(X, i)) == If.count(h <> X, i) : Nat}:
  pi.count_go(Nat.is_eq(If.Tool.id(h), i), h, X, i)

def pi.cnt_add(b: Bool, +x: Nat, +y: Nat) -> {pi.cnt(b, Nat.add(x, y)) == Nat.add(pi.cnt(b, x), y) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pi.cnt_comm(a: Bool, b: Bool, +n: Nat) -> {pi.cnt(a, pi.cnt(b, n)) == pi.cnt(b, pi.cnt(a, n)) : Nat}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# a take and its drop split every count
def pi.count_split(+xs: List<&2, If.Tool>, +n: Nat, +i: Nat) -> {Nat.add(If.count(List.take(&2, If.Tool, xs, n), i), If.count(List.drop(&2, If.Tool, xs, n), i)) == If.count(xs, i) : Nat}:
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      +b = Nat.is_eq(If.Tool.id(h), i)
      +T = List.take(&2, If.Tool, t, p)
      +D = If.count(List.drop(&2, If.Tool, t, p), i)
      %pi.count_cons(h, T, i) : {Nat.add(_, D) == If.count(h <> t, i) : Nat}
      %pi.count_cons(h, t, i) : {Nat.add(pi.cnt(b, If.count(T, i)), D) == _ : Nat}
      %pi.cnt_add(b, If.count(T, i), D) : {_ == pi.cnt(b, If.count(t, i)) : Nat}
      Equal.cong(Nat, Nat, k => pi.cnt(b, k), Nat.add(If.count(T, i), D), If.count(t, i), pi.count_split(t, p, i))

def pi.count_ins_go(+xs: List<&2, If.Tool>, +t: If.Tool, hit: Bool, +i: Nat) -> {If.count(t <> xs, i) == If.count(If.ins.go(xs, t, hit), i) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case u <> rest:
      match hit:
        case True{}:
          {==}
        case False{}:
          +bu = Nat.is_eq(If.Tool.id(u), i)
          +bt = Nat.is_eq(If.Tool.id(t), i)
          +I = If.ins.go(rest, t, If.low.at(rest, t))
          %pi.count_cons(u, I, i) : {If.count(t <> u <> rest, i) == _ : Nat}
          %pi.count_ins_go(rest, t, If.low.at(rest, t), i) : {If.count(t <> u <> rest, i) == pi.cnt(bu, _) : Nat}
          %pi.count_cons(t, rest, i) : {If.count(t <> u <> rest, i) == pi.cnt(bu, _) : Nat}
          %pi.count_cons(t, u <> rest, i) : {_ == pi.cnt(bu, pi.cnt(bt, If.count(rest, i))) : Nat}
          %pi.count_cons(u, rest, i) : {pi.cnt(bt, _) == pi.cnt(bu, pi.cnt(bt, If.count(rest, i))) : Nat}
          pi.cnt_comm(bt, bu, If.count(rest, i))

# ranking keeps every count
def pi.count_rank(+ts: List<&2, If.Tool>, +i: Nat) -> {If.count(ts, i) == If.count(If.rank(ts), i) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case t <> rest:
      +R = If.rank(rest)
      %pi.count_ins_go(R, t, If.low.at(R, t), i) : {If.count(t <> rest, i) == _ : Nat}
      %pi.count_cons(t, R, i) : {If.count(t <> rest, i) == _ : Nat}
      %pi.count_cons(t, rest, i) : {_ == pi.cnt(Nat.is_eq(If.Tool.id(t), i), If.count(R, i)) : Nat}
      %pi.count_rank(rest, i) : {pi.cnt(Nat.is_eq(If.Tool.id(t), i), If.count(rest, i)) == pi.cnt(Nat.is_eq(If.Tool.id(t), i), _) : Nat}
      {==}

def pi.strict_keeps_every_tool(+cap: Nat, +ts: List<&2, If.Tool>, +i: Nat) -> {Nat.add(If.count(Pair.fst(List<&2, If.Tool>, List<&2, If.Tool>, If.strict(cap, ts)), i), If.count(Pair.snd(List<&2, If.Tool>, List<&2, If.Tool>, If.strict(cap, ts)), i)) == If.count(ts, i) : Nat}:
  +R = If.rank(ts)
  Equal.trans(Nat, Nat.add(If.count(List.take(&2, If.Tool, R, cap), i), If.count(List.drop(&2, If.Tool, R, cap), i)), If.count(R, i), If.count(ts, i), pi.count_split(R, cap, i), Equal.sym(Nat, If.count(ts, i), If.count(R, i), pi.count_rank(ts, i)))

# every tool of ys has a priority of at most p
def pi.below(ys: List<&2, If.Tool>, +p: Nat) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case +y <> rest:
      Bool.and(Nat.is_le(If.Tool.prio(y), p), pi.below(rest, p))

# priorities never rise along xs
def pi.sorted(xs: List<&2, If.Tool>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> +rest:
      Bool.and(pi.below(rest, If.Tool.prio(x)), pi.sorted(rest))

def pi.below_mono(+ys: List<&2, If.Tool>, +p: Nat, +q: Nat, +b: {pi.below(ys, p) == True{} : Bool}, +le: {Nat.is_le(p, q) == True{} : Bool}) -> {pi.below(ys, q) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case y <> rest:
      +a = Nat.is_le(If.Tool.prio(y), p)
      pi.and_t(Nat.is_le(If.Tool.prio(y), q), pi.below(rest, q), pi.le_trans(If.Tool.prio(y), p, q, pi.and_l(a, pi.below(rest, p), b), le), pi.below_mono(rest, p, q, pi.and_r(a, pi.below(rest, p), b), le))

def pi.below_ins_go(+xs: List<&2, If.Tool>, +t: If.Tool, hit: Bool, +P: Nat, +b: {pi.below(xs, P) == True{} : Bool}, +lt: {Nat.is_le(If.Tool.prio(t), P) == True{} : Bool}) -> {pi.below(If.ins.go(xs, t, hit), P) == True{} : Bool}:
  match xs:
    case Nil{}:
      pi.and_t(Nat.is_le(If.Tool.prio(t), P), True{}, lt, {==})
    case u <> rest:
      match hit:
        case True{}:
          pi.and_t(Nat.is_le(If.Tool.prio(t), P), pi.below(u <> rest, P), lt, b)
        case False{}:
          +a = Nat.is_le(If.Tool.prio(u), P)
          +I = If.ins.go(rest, t, If.low.at(rest, t))
          pi.and_t(a, pi.below(I, P), pi.and_l(a, pi.below(rest, P), b), pi.below_ins_go(rest, t, If.low.at(rest, t), P, pi.and_r(a, pi.below(rest, P), b), lt))

def pi.sorted_ins_go(+xs: List<&2, If.Tool>, +t: If.Tool, hit: Bool, +eh: {If.low.at(xs, t) == hit : Bool}, +s: {pi.sorted(xs) == True{} : Bool}) -> {pi.sorted(If.ins.go(xs, t, hit)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case u <> rest:
      match hit:
        case True{}:
          +pu = If.Tool.prio(u)
          +pt = If.Tool.prio(t)
          +le = eh
          +bu = pi.and_t(Nat.is_le(pu, pt), pi.below(rest, pt), le, pi.below_mono(rest, pu, pt, pi.and_l(pi.below(rest, pu), pi.sorted(rest), s), le))
          pi.and_t(pi.below(u <> rest, pt), pi.sorted(u <> rest), bu, s)
        case False{}:
          +pu = If.Tool.prio(u)
          +pt = If.Tool.prio(t)
          +I = If.ins.go(rest, t, If.low.at(rest, t))
          +bi = pi.below_ins_go(rest, t, If.low.at(rest, t), pu, pi.and_l(pi.below(rest, pu), pi.sorted(rest), s), pi.nle_le(pu, pt, eh))
          pi.and_t(pi.below(I, pu), pi.sorted(I), bi, pi.sorted_ins_go(rest, t, If.low.at(rest, t), {==}, pi.and_r(pi.below(rest, pu), pi.sorted(rest), s)))

# ranking sorts by priority
def pi.sorted_rank(+ts: List<&2, If.Tool>) -> {pi.sorted(If.rank(ts)) == True{} : Bool}:
  match ts:
    case Nil{}:
      {==}
    case t <> rest:
      +R = If.rank(rest)
      pi.sorted_ins_go(R, t, If.low.at(R, t), {==}, pi.sorted_rank(rest))

def pi.dom_nil(+ys: List<&2, If.Tool>) -> {If.dominates(Nil{}, ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case y <> rest:
      pi.dom_nil(rest)

def pi.dom_cons(+h: If.Tool, +X: List<&2, If.Tool>, +Y: List<&2, If.Tool>, +d: {If.dominates(X, Y) == True{} : Bool}, +b: {pi.below(Y, If.Tool.prio(h)) == True{} : Bool}) -> {If.dominates(h <> X, Y) == True{} : Bool}:
  match Y:
    case Nil{}:
      {==}
    case y <> rest:
      +py = If.Tool.prio(y)
      +ph = If.Tool.prio(h)
      +le = pi.and_l(Nat.is_le(py, ph), pi.below(rest, ph), b)
      +ag = pi.and_l(If.all_ge(X, py), If.dominates(X, rest), d)
      pi.and_t(If.all_ge(h <> X, py), If.dominates(h <> X, rest), pi.and_t(Nat.is_le(py, ph), If.all_ge(X, py), le, ag), pi.dom_cons(h, X, rest, pi.and_r(If.all_ge(X, py), If.dominates(X, rest), d), pi.and_r(Nat.is_le(py, ph), pi.below(rest, ph), b)))

def pi.below_drop(+xs: List<&2, If.Tool>, +n: Nat, +p: Nat, +b: {pi.below(xs, p) == True{} : Bool}) -> {pi.below(List.drop(&2, If.Tool, xs, n), p) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      b
    case h <> t 1n+q:
      pi.below_drop(t, q, p, pi.and_r(Nat.is_le(If.Tool.prio(h), p), pi.below(t, p), b))

# a sorted list's take dominates its drop
def pi.dom_split(+xs: List<&2, If.Tool>, +n: Nat, +s: {pi.sorted(xs) == True{} : Bool}) -> {If.dominates(List.take(&2, If.Tool, xs, n), List.drop(&2, If.Tool, xs, n)) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      pi.dom_nil(h <> t)
    case h <> t 1n+q:
      +ph = If.Tool.prio(h)
      pi.dom_cons(h, List.take(&2, If.Tool, t, q), List.drop(&2, If.Tool, t, q), pi.dom_split(t, q, pi.and_r(pi.below(t, ph), pi.sorted(t), s)), pi.below_drop(t, q, ph, pi.and_l(pi.below(t, ph), pi.sorted(t), s)))

def pi.strict_by_priority(+cap: Nat, +ts: List<&2, If.Tool>) -> {If.dominates(Pair.fst(List<&2, If.Tool>, List<&2, If.Tool>, If.strict(cap, ts)), Pair.snd(List<&2, If.Tool>, List<&2, If.Tool>, If.strict(cap, ts))) == True{} : Bool}:
  pi.dom_split(If.rank(ts), cap, pi.sorted_rank(ts))

# More numbers
# ------------

def pi.eq_true(+a: Nat, +b: Nat, +h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      pi.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      pi.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pi.eq_true(p, q, h))

def pi.add_zero(+a: Nat) -> {a == Nat.add(a, 0n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, p, Nat.add(p, 0n), pi.add_zero(p))

def pi.add_succ(+a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 1n+b), 1n+Nat.add(p, b), pi.add_succ(p, b))

def pi.le_refl(+a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      pi.le_refl(p)

def pi.le_succ_r(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      pi.absurdF({Nat.is_le(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pi.le_succ_r(p, q, h)

def pi.le_add(+a: Nat, +s: Nat) -> {Nat.is_le(a, Nat.add(a, s)) == True{} : Bool}:
  match a:
    case 0n:
      pi.le0(s)
    case 1n+p:
      pi.le_add(p, s)

def pi.le_add_r(+r: Nat, +s: Nat) -> {Nat.is_le(s, Nat.add(r, s)) == True{} : Bool}:
  match r:
    case 0n:
      pi.le_refl(s)
    case 1n+p:
      pi.le_succ_r(s, Nat.add(p, s), pi.le_add_r(p, s))

def pi.nle_lt(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      pi.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      pi.absurd({Nat.is_lt(1n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pi.nle_lt(p, q, h)

def pi.lt_nle(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      pi.absurdF({Nat.is_le(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      pi.absurdF({Nat.is_le(0n, 1n+p) == False{} : Bool}, h)
    case 1n+p 1n+q:
      pi.lt_nle(p, q, h)

def pi.lt_zero(+a: Nat, +h: {Nat.is_lt(a, 0n) == True{} : Bool}) -> Empty:
  match a:
    case 0n:
      pi.absurdF(Empty, h)
    case 1n+p:
      pi.absurdF(Empty, h)

def pi.lt_succ(+a: Nat) -> {Nat.is_lt(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      pi.lt_succ(p)

def pi.lt_succ_r(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      pi.absurdF({Nat.is_lt(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pi.lt_succ_r(p, q, h)

def pi.or_r_true(a: Bool, +b: Bool, +h: {Bool.or(a, b) == True{} : Bool}, +ea: {a == False{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      pi.absurd({b == True{} : Bool}, ea)
    case False{}:
      h

# The repetition guard
# --------------------

def pi.or_tl(a: Bool, +b: Bool, h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pi.absurdF({Bool.or(False{}, b) == True{} : Bool}, h)

def pi.or_tr(a: Bool, +b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

# one chunk more: each and the counter take the same step
def pi.each_step(b: Bool, +x: Nat, +rest: List<&2, Nat>, +q: Nat, +n: Nat, +ih: {If.each(rest, q, n) == Nat.is_le(n, If.cycle(rest, q)) : Bool}) -> {Bool.and(b, If.each(rest, q, n)) == Nat.is_le(1n+n, If.cycle.go(x <> rest, q, b)) : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      {==}

# the first m chunks each equal the chunk 1+q before them exactly when the
# counter of period 1+q is at least m
def pi.each_cycle(+s: List<&2, Nat>, +q: Nat, +m: Nat) -> {If.each(s, q, m) == Nat.is_le(m, If.cycle(s, q)) : Bool}:
  match s m:
    case _ 0n:
      Equal.sym(Bool, Nat.is_le(0n, If.cycle(s, q)), True{}, pi.le0(If.cycle(s, q)))
    case Nil{} 1n+n:
      {==}
    case x <> rest 1n+n:
      pi.each_step(If.back(rest, q, x), x, rest, q, n, pi.each_cycle(rest, q, n))

# the counters fire exactly when the window is periodic
def pi.fires_periodic(+s: List<&2, Nat>, +k: Nat, +n: Nat) -> {If.fires.go(s, k, n) == If.periodic.go(s, k, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+q:
      %pi.each_cycle(s, q, Nat.sub(k, 1n+q)) : {Bool.or(_, If.fires.go(s, k, q)) == Bool.or(If.each(s, q, Nat.sub(k, 1n+q)), If.periodic.go(s, k, q)) : Bool}
      %Equal.sym(Bool, If.fires.go(s, k, q), If.periodic.go(s, k, q), pi.fires_periodic(s, k, q)) : {Bool.or(If.each(s, q, Nat.sub(k, 1n+q)), _) == Bool.or(If.each(s, q, Nat.sub(k, 1n+q)), If.periodic.go(s, k, q)) : Bool}
      {==}

# a guard that has not cut yet cuts a stream with a periodic window
def pi.cut_go(+xs: List<&2, Nat>, +k: Nat, +seen: List<&2, Nat>, +n: Nat, hit: Bool, +eh: {If.fire.at(xs, k, seen) == hit : Bool}, +lp: {If.loops.go(xs, k, seen) == True{} : Bool}) -> {If.Cut.cut(If.guard.go(xs, k, seen, n, hit)) == True{} : Bool}:
  match xs:
    case Nil{}:
      pi.absurdF({If.Cut.cut(If.guard.go(Nil{}, k, seen, n, hit)) == True{} : Bool}, lp)
    case x <> rest:
      match hit:
        case True{}:
          {==}
        case False{}:
          +ep = Equal.trans(Bool, If.periodic(x <> seen, k), If.fires(x <> seen, k), False{}, Equal.sym(Bool, If.fires(x <> seen, k), If.periodic(x <> seen, k), pi.fires_periodic(x <> seen, k, If.periods(k))), eh)
          pi.cut_go(rest, k, x <> seen, 1n+n, If.fire.at(rest, k, x <> seen), {==}, pi.or_r_true(If.periodic(x <> seen, k), If.loops.go(rest, k, x <> seen), lp, ep))

# a guard on a stream with no periodic window never cuts
def pi.keep_go(+xs: List<&2, Nat>, +k: Nat, +seen: List<&2, Nat>, +n: Nat, hit: Bool, +eh: {If.fire.at(xs, k, seen) == hit : Bool}, +calm: {If.loops.go(xs, k, seen) == False{} : Bool}) -> {If.guard.go(xs, k, seen, n, hit) == If.Whole{} : If.Cut}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      match hit:
        case True{}:
          +cp = pi.or_l(If.periodic(x <> seen, k), If.loops.go(rest, k, x <> seen), calm)
          +fp = Equal.trans(Bool, If.fires(x <> seen, k), If.periodic(x <> seen, k), False{}, pi.fires_periodic(x <> seen, k, If.periods(k)), cp)
          pi.void({If.CutAt{1n+n} == If.Whole{} : If.Cut}, pi.flip(If.fires(x <> seen, k), eh, fp))
        case False{}:
          pi.keep_go(rest, k, x <> seen, 1n+n, If.fire.at(rest, k, x <> seen), {==}, pi.or_r(If.periodic(x <> seen, k), If.loops.go(rest, k, x <> seen), calm))

# period 1 is always checked
def pi.periodic_ge1(+s: List<&2, Nat>, +k: Nat, +r: Nat, +e: {If.each(s, 0n, Nat.sub(k, 1n)) == True{} : Bool}) -> {If.periodic.go(s, k, 1n+r) == True{} : Bool}:
  match r:
    case 0n:
      pi.or_tl(If.each(s, 0n, Nat.sub(k, 1n)), If.periodic.go(s, k, 0n), e)
    case 1n+t:
      pi.or_tr(If.each(s, 1n+t, Nat.sub(k, 2n+t)), If.periodic.go(s, k, 1n+t), pi.periodic_ge1(s, k, t, e))

def pi.periodic_one(+s: List<&2, Nat>, +k: Nat, q: Nat, +e: {If.each(s, 0n, Nat.sub(k, 1n)) == True{} : Bool}) -> {If.periodic.go(s, k, If.periods.of(q)) == True{} : Bool}:
  match q:
    case 0n:
      pi.periodic_ge1(s, k, 0n, e)
    case 1n+r:
      pi.periodic_ge1(s, k, r, e)

def pi.sub1_le(+k: Nat, +s: Nat, +h: {Nat.is_le(k, 1n+s) == True{} : Bool}) -> {Nat.is_le(Nat.sub(k, 1n), s) == True{} : Bool}:
  match k:
    case 0n:
      pi.le0(s)
    case 1n+j:
      match j:
        case 0n:
          pi.le0(s)
        case 1n+i:
          h

def pi.le_add0(+k: Nat, +run: Nat, +h: {Nat.is_le(k, Nat.add(run, 0n)) == True{} : Bool}) -> {Nat.is_le(k, run) == True{} : Bool}:
  %Equal.sym(Nat, run, Nat.add(run, 0n), pi.add_zero(run)) : {Nat.is_le(k, _) == True{} : Bool}
  h

# a run that reaches k - 1 with what continues it: one chunk more
def pi.run_h(e: Bool, +y: Nat, +r2: List<&2, Nat>, +x: Nat, +s: List<&2, Nat>, +K: Nat, +ee: {Nat.is_eq(y, x) == e : Bool}, +h: {Nat.is_le(K, Nat.add(If.cycle(x <> s, 0n), If.same_run.go(y <> r2, x, e))) == True{} : Bool}, +lt: {Nat.is_le(K, If.cycle(x <> s, 0n)) == False{} : Bool}) -> {Nat.is_le(K, Nat.add(If.cycle.go(y <> x <> s, 0n, e), If.same_run(r2, y))) == True{} : Bool}:
  match e:
    case True{}:
      %Equal.sym(Nat, y, x, pi.eq_true(y, x, ee)) : {Nat.is_le(K, 1n+Nat.add(If.cycle(x <> s, 0n), If.same_run(r2, _))) == True{} : Bool}
      %pi.add_succ(If.cycle(x <> s, 0n), If.same_run(r2, x)) : {Nat.is_le(K, _) == True{} : Bool}
      h
    case False{}:
      pi.void({Nat.is_le(K, Nat.add(If.cycle.go(y <> x <> s, 0n, False{}), If.same_run(r2, y))) == True{} : Bool}, pi.flip(Nat.is_le(K, If.cycle(x <> s, 0n)), pi.le_add0(K, If.cycle(x <> s, 0n), h), lt))

# a run of x whose counter of period 1, with the chunks that continue it,
# reaches k - 1 ends in a periodic window
def pi.run_loops(+rest: List<&2, Nat>, +k: Nat, +x: Nat, +s: List<&2, Nat>, c: Bool, +ec: {Nat.is_le(Nat.sub(k, 1n), If.cycle(x <> s, 0n)) == c : Bool}, +h: {Nat.is_le(Nat.sub(k, 1n), Nat.add(If.cycle(x <> s, 0n), If.same_run(rest, x))) == True{} : Bool}) -> {Bool.or(If.periodic(x <> s, k), If.loops.go(rest, k, x <> s)) == True{} : Bool}:
  match rest:
    case Nil{}:
      match c:
        case True{}:
          +e = Equal.trans(Bool, If.each(x <> s, 0n, Nat.sub(k, 1n)), Nat.is_le(Nat.sub(k, 1n), If.cycle(x <> s, 0n)), True{}, pi.each_cycle(x <> s, 0n, Nat.sub(k, 1n)), ec)
          pi.or_tl(If.periodic(x <> s, k), If.loops.go(Nil{}, k, x <> s), pi.periodic_one(x <> s, k, If.quarter(k), e))
        case False{}:
          pi.void({Bool.or(If.periodic(x <> s, k), If.loops.go(Nil{}, k, x <> s)) == True{} : Bool}, pi.flip(Nat.is_le(Nat.sub(k, 1n), If.cycle(x <> s, 0n)), pi.le_add0(Nat.sub(k, 1n), If.cycle(x <> s, 0n), h), ec))
    case y <> r2:
      match c:
        case True{}:
          +e = Equal.trans(Bool, If.each(x <> s, 0n, Nat.sub(k, 1n)), Nat.is_le(Nat.sub(k, 1n), If.cycle(x <> s, 0n)), True{}, pi.each_cycle(x <> s, 0n, Nat.sub(k, 1n)), ec)
          pi.or_tl(If.periodic(x <> s, k), If.loops.go(y <> r2, k, x <> s), pi.periodic_one(x <> s, k, If.quarter(k), e))
        case False{}:
          +h2 = pi.run_h(Nat.is_eq(y, x), y, r2, x, s, Nat.sub(k, 1n), {==}, h, ec)
          +r = pi.run_loops(r2, k, y, x <> s, Nat.is_le(Nat.sub(k, 1n), If.cycle(y <> x <> s, 0n)), {==}, h2)
          pi.or_tr(If.periodic(x <> s, k), If.loops.go(y <> r2, k, x <> s), r)

# a run that reaches k after its first chunk
def pi.rhead(xs: List<&2, Nat>, +k: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> +rest:
      Nat.is_le(k, 1n+If.same_run(rest, x))

# a stream that repeats a chunk k times in a row has a periodic window
# (period 1)
def pi.rep_go(+xs: List<&2, Nat>, +k: Nat, +seen: List<&2, Nat>, c: Bool, +ec: {pi.rhead(xs, k) == c : Bool}, +rep: {If.repeats(xs, k) == True{} : Bool}) -> {If.loops.go(xs, k, seen) == True{} : Bool}:
  match xs:
    case Nil{}:
      pi.absurdF({If.loops.go(Nil{}, k, seen) == True{} : Bool}, rep)
    case x <> rest:
      match c:
        case True{}:
          +S = If.same_run(rest, x)
          +C = If.cycle(x <> seen, 0n)
          +h = pi.le_trans(Nat.sub(k, 1n), S, Nat.add(C, S), pi.sub1_le(k, S, ec), pi.le_add_r(C, S))
          pi.run_loops(rest, k, x, seen, Nat.is_le(Nat.sub(k, 1n), C), {==}, h)
        case False{}:
          +rr = pi.or_r_true(Nat.is_le(k, 1n+If.same_run(rest, x)), If.repeats(rest, k), rep, ec)
          pi.or_tr(If.periodic(x <> seen, k), If.loops.go(rest, k, x <> seen), pi.rep_go(rest, k, x <> seen, pi.rhead(rest, k), {==}, rr))

def pi.guard_cuts_loops(+xs: List<&2, Nat>, +k: Nat, lp: {If.loops(xs, k) == True{} : Bool}) -> {If.Cut.cut(If.guard(xs, k)) == True{} : Bool}:
  pi.cut_go(xs, k, Nil{}, 0n, If.fire.at(xs, k, Nil{}), {==}, lp)

def pi.guard_cuts_repeats(+xs: List<&2, Nat>, +k: Nat, rep: {If.repeats(xs, k) == True{} : Bool}) -> {If.Cut.cut(If.guard(xs, k)) == True{} : Bool}:
  pi.cut_go(xs, k, Nil{}, 0n, If.fire.at(xs, k, Nil{}), {==}, pi.rep_go(xs, k, Nil{}, pi.rhead(xs, k), {==}, rep))

def pi.guard_keeps_others(+xs: List<&2, Nat>, +k: Nat, calm: {If.loops(xs, k) == False{} : Bool}) -> {If.guard(xs, k) == If.Whole{} : If.Cut}:
  pi.keep_go(xs, k, Nil{}, 0n, If.fire.at(xs, k, Nil{}), {==}, calm)

# Early compaction
# ----------------

def pi.le_succ_false(+x: Nat, +lim: Nat, +h: {Nat.is_le(x, lim) == True{} : Bool}) -> {Nat.is_le(1n+lim, x) == False{} : Bool}:
  match x lim:
    case 0n _:
      {==}
    case 1n+p 0n:
      pi.absurdF({Nat.is_le(1n, 1n+p) == False{} : Bool}, h)
    case 1n+p 1n+q:
      pi.le_succ_false(p, q, h)

def pi.lt_sub(+x: Nat, +lim: Nat, +m: Nat, +h: {Nat.is_lt(x, Nat.sub(lim, m)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(x, m), lim) == True{} : Bool}:
  match lim m:
    case 0n _:
      pi.void({Nat.is_lt(Nat.add(x, m), 0n) == True{} : Bool}, pi.lt_zero(x, h))
    case 1n+a 0n:
      %pi.add_zero(x) : {Nat.is_lt(_, 1n+a) == True{} : Bool}
      h
    case 1n+a 1n+b:
      %Equal.sym(Nat, Nat.add(x, 1n+b), 1n+Nat.add(x, b), pi.add_succ(x, b)) : {Nat.is_lt(_, 1n+a) == True{} : Bool}
      pi.lt_sub(x, a, b, h)

# an index past i: the first reach from j > i
def pi.later(+xs: List<&2, Nat>, +t: Nat, +j: Nat, hit: Bool, +i: Nat, +lt: {Nat.is_lt(i, j) == True{} : Bool}) -> {If.m.lt(Some{i}, If.first_at.go(xs, t, j, hit)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      match hit:
        case True{}:
          lt
        case False{}:
          pi.later(rest, t, 1n+j, If.reach.at(rest, t), i, pi.lt_succ_r(i, j, lt))

# below the threshold, the next size stays within the limit
def pi.compact_go(+xs: List<&2, Nat>, +m: Nat, +lim: Nat, +prev: Nat, +i: Nat, hit: Bool, +eh: {If.reach.at(xs, Nat.sub(lim, m)) == hit : Bool}, +inv: {Nat.is_le(Nat.add(prev, m), lim) == True{} : Bool}, +st: {If.steps_le(xs, m, prev) == True{} : Bool}) -> {If.m.lt(If.first_at.go(xs, Nat.sub(lim, m), i, hit), If.first_at.go(xs, 1n+lim, i, If.reach.at(xs, 1n+lim))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      match hit:
        case True{}:
          +xle = pi.le_trans(x, Nat.add(prev, m), lim, pi.and_l(Nat.is_le(x, Nat.add(prev, m)), If.steps_le(rest, m, x), st), inv)
          %Equal.sym(Bool, Nat.is_le(1n+lim, x), False{}, pi.le_succ_false(x, lim, xle)) : {If.m.lt(Some{i}, If.first_at.go(x <> rest, 1n+lim, i, _)) == True{} : Bool}
          pi.later(rest, 1n+lim, 1n+i, If.reach.at(rest, 1n+lim), i, pi.lt_succ(i))
        case False{}:
          +T = Nat.sub(lim, m)
          +xle = pi.le_trans(x, Nat.add(prev, m), lim, pi.and_l(Nat.is_le(x, Nat.add(prev, m)), If.steps_le(rest, m, x), st), inv)
          %Equal.sym(Bool, Nat.is_le(1n+lim, x), False{}, pi.le_succ_false(x, lim, xle)) : {If.m.lt(If.first_at.go(rest, T, 1n+i, If.reach.at(rest, T)), If.first_at.go(x <> rest, 1n+lim, i, _)) == True{} : Bool}
          +inv2 = pi.lt_le(Nat.add(x, m), lim, pi.lt_sub(x, lim, m, pi.nle_lt(T, x, eh)))
          pi.compact_go(rest, m, lim, x, 1n+i, If.reach.at(rest, T), {==}, inv2, pi.and_r(Nat.is_le(x, Nat.add(prev, m)), If.steps_le(rest, m, x), st))

def pi.compact_starts_early(+xs: List<&2, Nat>, +m: Nat, +lim: Nat, small: {Nat.is_le(m, lim) == True{} : Bool}, steps: {If.steps_le(xs, m, 0n) == True{} : Bool}) -> {If.m.lt(If.first_at(xs, Nat.sub(lim, m), 0n), If.first_at(xs, 1n+lim, 0n)) == True{} : Bool}:
  pi.compact_go(xs, m, lim, 0n, 0n, If.reach.at(xs, Nat.sub(lim, m)), {==}, small, steps)
