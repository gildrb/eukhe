# eukhe: the proof of LAW strict_keeps_every_tool

import Base
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer

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

def pms.add_zero_r(m: Nat) -> {Nat.add(m, 0n) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, 0n), p, pms.add_zero_r(p))

def pms.add_succ_r(m: Nat, -n: Nat) -> {Nat.add(m, 1n+n) == 1n+Nat.add(m, n) : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, 1n+n), 1n+Nat.add(p, n), pms.add_succ_r(p, n))

def pms.add_comm(m: Nat, +n: Nat) -> {Nat.add(m, n) == Nat.add(n, m) : Nat}:
  match m:
    case 0n:
      Equal.sym(Nat, Nat.add(n, 0n), n, pms.add_zero_r(n))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(n, 1n+p), 1n+Nat.add(n, p), pms.add_succ_r(n, p)) : {1n+Nat.add(p, n) == _ : Nat}
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, n), Nat.add(n, p), pms.add_comm(p, n))

def pms.add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), pms.add_assoc(p, b, c))

# (a + b) + c == b + (a + c)
def pms.add_assoc_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(b, Nat.add(a, c)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(b, a), c), Nat.add(b, Nat.add(a, c)),
    Equal.cong(Nat, Nat, k => Nat.add(k, c), Nat.add(a, b), Nat.add(b, a), pms.add_comm(a, b)),
    pms.add_assoc(b, a, c))

# m + cnt(q, n) == cnt(q, m + n)
def pms.add_cnt(q: Bool, m: Nat, -n: Nat) -> {Nat.add(m, pi.cnt(q, n)) == pi.cnt(q, Nat.add(m, n)) : Nat}:
  match q:
    case True{}:
      pms.add_succ_r(m, n)
    case False{}:
      {==}

# a tool counted after s
def pms.last_cnt(+q: Bool, +s: Nat) -> {Nat.add(s, pi.cnt(q, 0n)) == pi.cnt(q, s) : Nat}:
  Equal.trans(Nat, Nat.add(s, pi.cnt(q, 0n)), pi.cnt(q, Nat.add(s, 0n)), pi.cnt(q, s),
    pms.add_cnt(q, s, 0n),
    Equal.cong(Nat, Nat, k => pi.cnt(q, k), Nat.add(s, 0n), s, pms.add_zero_r(s)))

# Counts
# ------

# tool h has id i
def pms.w(+h: If.Tool, +i: Nat) -> Bool:
  Nat.is_eq(If.Tool.id(h), i)

# the copies of id i in xs, counted head-first
def pms.c(xs: List<&2, If.Tool>, +i: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case +h <> t:
      pi.cnt(pms.w(h, i), pms.c(t, i))

def pms.c_count(xs: List<&2, If.Tool>, +i: Nat) -> {pms.c(xs, i) == If.count(xs, i) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      +b = pms.w(h, i)
      Equal.trans(Nat, pi.cnt(b, pms.c(t, i)), pi.cnt(b, If.count(t, i)), If.count(h <> t, i),
        Equal.cong(Nat, Nat, k => pi.cnt(b, k), pms.c(t, i), If.count(t, i), pms.c_count(t, i)),
        pi.count_cons(h, t, i))

# the copies of id i among the leaves of t
def pms.tc(t: If.TTree, +i: Nat) -> Nat:
  match t:
    case If.TTip{}:
      0n
    case If.TLeaf{+v}:
      pi.cnt(pms.w(v, i), 0n)
    case If.TNode{l, r}:
      Nat.add(pms.tc(l, i), pms.tc(r, i))

# the copies of id i in the trees of the counter ds
def pms.dc(ds: If.TDig, +i: Nat) -> Nat:
  match ds:
    case If.TEnd{}:
      0n
    case If.T0{rest}:
      pms.dc(rest, i)
    case If.T1{d, rest}:
      Nat.add(pms.tc(d, i), pms.dc(rest, i))

# tmerge.go(xt, yt, x, y, c) counts x <> xt and y <> yt together,
# whatever the verdict c is
def pms.c_mg(+xt: List<&2, If.Tool>, +yt: List<&2, If.Tool>, +x: If.Tool, +y: If.Tool, c: Bool, +i: Nat) -> {Nat.add(pms.c(x <> xt, i), pms.c(y <> yt, i)) == pms.c(If.tmerge.go(xt, yt, x, y, c), i) : Nat}:
  match xt yt c:
    case Nil{} Nil{} True{}:
      Equal.sym(Nat, pi.cnt(pms.w(x, i), pms.c(y <> Nil{}, i)), Nat.add(pi.cnt(pms.w(x, i), 0n), pms.c(y <> Nil{}, i)),
        pi.cnt_add(pms.w(x, i), 0n, pms.c(y <> Nil{}, i)))
    case Nil{} Nil{} False{}:
      pms.last_cnt(pms.w(y, i), pms.c(x <> Nil{}, i))
    case Nil{} +y2 <> +yt2 True{}:
      Equal.sym(Nat, pi.cnt(pms.w(x, i), pms.c(y <> y2 <> yt2, i)), Nat.add(pi.cnt(pms.w(x, i), 0n), pms.c(y <> y2 <> yt2, i)),
        pi.cnt_add(pms.w(x, i), 0n, pms.c(y <> y2 <> yt2, i)))
    case Nil{} +y2 <> +yt2 False{}:
      %pms.c_mg(Nil{}, yt2, x, y2, Nat.is_le(If.Tool.prio(y2), If.Tool.prio(x)), i) : {Nat.add(pms.c(x <> Nil{}, i), pms.c(y <> y2 <> yt2, i)) == pi.cnt(pms.w(y, i), _) : Nat}
      pms.add_cnt(pms.w(y, i), pms.c(x <> Nil{}, i), pms.c(y2 <> yt2, i))
    case +x2 <> +xt2 Nil{} True{}:
      %pms.c_mg(xt2, Nil{}, x2, y, Nat.is_le(If.Tool.prio(y), If.Tool.prio(x2)), i) : {Nat.add(pms.c(x <> x2 <> xt2, i), pms.c(y <> Nil{}, i)) == pi.cnt(pms.w(x, i), _) : Nat}
      Equal.sym(Nat, pi.cnt(pms.w(x, i), Nat.add(pms.c(x2 <> xt2, i), pms.c(y <> Nil{}, i))), Nat.add(pms.c(x <> x2 <> xt2, i), pms.c(y <> Nil{}, i)),
        pi.cnt_add(pms.w(x, i), pms.c(x2 <> xt2, i), pms.c(y <> Nil{}, i)))
    case +x2 <> +xt2 Nil{} False{}:
      pms.last_cnt(pms.w(y, i), pms.c(x <> x2 <> xt2, i))
    case +x2 <> +xt2 +y2 <> +yt2 True{}:
      %pms.c_mg(xt2, y2 <> yt2, x2, y, Nat.is_le(If.Tool.prio(y), If.Tool.prio(x2)), i) : {Nat.add(pms.c(x <> x2 <> xt2, i), pms.c(y <> y2 <> yt2, i)) == pi.cnt(pms.w(x, i), _) : Nat}
      Equal.sym(Nat, pi.cnt(pms.w(x, i), Nat.add(pms.c(x2 <> xt2, i), pms.c(y <> y2 <> yt2, i))), Nat.add(pms.c(x <> x2 <> xt2, i), pms.c(y <> y2 <> yt2, i)),
        pi.cnt_add(pms.w(x, i), pms.c(x2 <> xt2, i), pms.c(y <> y2 <> yt2, i)))
    case +x2 <> +xt2 +y2 <> +yt2 False{}:
      %pms.c_mg(x2 <> xt2, yt2, x, y2, Nat.is_le(If.Tool.prio(y2), If.Tool.prio(x)), i) : {Nat.add(pms.c(x <> x2 <> xt2, i), pms.c(y <> y2 <> yt2, i)) == pi.cnt(pms.w(y, i), _) : Nat}
      pms.add_cnt(pms.w(y, i), pms.c(x <> x2 <> xt2, i), pms.c(y2 <> yt2, i))

# tmerge(a, b) counts a and b together
def pms.c_merge(+a: List<&2, If.Tool>, +b: List<&2, If.Tool>, +i: Nat) -> {Nat.add(pms.c(a, i), pms.c(b, i)) == pms.c(If.tmerge(a, b), i) : Nat}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} +y <> +yt:
      {==}
    case +x <> +xt Nil{}:
      pms.add_zero_r(pms.c(x <> xt, i))
    case +x <> +xt +y <> +yt:
      pms.c_mg(xt, yt, x, y, Nat.is_le(If.Tool.prio(y), If.Tool.prio(x)), i)

# tsort(t) counts the leaves of t
def pms.c_tsort(+t: If.TTree, +i: Nat) -> {pms.tc(t, i) == pms.c(If.tsort(t), i) : Nat}:
  match t:
    case If.TTip{}:
      {==}
    case If.TLeaf{+v}:
      {==}
    case If.TNode{+l, +r}:
      %pms.c_merge(If.tsort(l), If.tsort(r), i) : {Nat.add(pms.tc(l, i), pms.tc(r, i)) == _ : Nat}
      %pms.c_tsort(l, i) : {Nat.add(pms.tc(l, i), pms.tc(r, i)) == Nat.add(_, pms.c(If.tsort(r), i)) : Nat}
      %pms.c_tsort(r, i) : {Nat.add(pms.tc(l, i), pms.tc(r, i)) == Nat.add(pms.tc(l, i), _) : Nat}
      {==}

# tpush(ds, t) adds the count of t to the counter
def pms.c_push(+ds: If.TDig, +t: If.TTree, +i: Nat) -> {Nat.add(pms.tc(t, i), pms.dc(ds, i)) == pms.dc(If.tpush(ds, t), i) : Nat}:
  match ds:
    case If.TEnd{}:
      {==}
    case If.T0{+rest}:
      {==}
    case If.T1{+t2, +rest}:
      %pms.c_push(rest, If.TNode{t2, t}, i) : {Nat.add(pms.tc(t, i), pms.dc(If.T1{t2, rest}, i)) == _ : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(pms.tc(t2, i), pms.tc(t, i)), pms.dc(rest, i)),
        Nat.add(pms.tc(t, i), Nat.add(pms.tc(t2, i), pms.dc(rest, i))),
        pms.add_assoc_swap(pms.tc(t2, i), pms.tc(t, i), pms.dc(rest, i)))

# tbuild(ts, ds) adds the count of ts to the counter
def pms.c_build(+ts: List<&2, If.Tool>, +ds: If.TDig, +i: Nat) -> {Nat.add(pms.c(ts, i), pms.dc(ds, i)) == pms.dc(If.tbuild(ts, ds), i) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case +h <> +t:
      %pms.c_build(t, If.tpush(ds, If.TLeaf{h}), i) : {Nat.add(pms.c(h <> t, i), pms.dc(ds, i)) == _ : Nat}
      %pms.c_push(ds, If.TLeaf{h}, i) : {Nat.add(pms.c(h <> t, i), pms.dc(ds, i)) == Nat.add(pms.c(t, i), _) : Nat}
      %Equal.sym(Nat, pi.cnt(pms.w(h, i), Nat.add(0n, pms.c(t, i))), Nat.add(pi.cnt(pms.w(h, i), 0n), pms.c(t, i)), pi.cnt_add(pms.w(h, i), 0n, pms.c(t, i))) : {Nat.add(_, pms.dc(ds, i)) == Nat.add(pms.c(t, i), Nat.add(pi.cnt(pms.w(h, i), 0n), pms.dc(ds, i))) : Nat}
      pms.add_assoc_swap(pi.cnt(pms.w(h, i), 0n), pms.c(t, i), pms.dc(ds, i))

# tjoin(ds, acc) counts the counter and acc together
def pms.c_join(+ds: If.TDig, +acc: If.TTree, +i: Nat) -> {Nat.add(pms.dc(ds, i), pms.tc(acc, i)) == pms.tc(If.tjoin(ds, acc), i) : Nat}:
  match ds:
    case If.TEnd{}:
      {==}
    case If.T0{+rest}:
      pms.c_join(rest, acc, i)
    case If.T1{+d, +rest}:
      %pms.c_join(rest, If.TNode{d, acc}, i) : {Nat.add(pms.dc(If.T1{d, rest}, i), pms.tc(acc, i)) == _ : Nat}
      pms.add_assoc_swap(pms.tc(d, i), pms.dc(rest, i), pms.tc(acc, i))

# rank(ts) counts ts
def pms.c_rank(+ts: List<&2, If.Tool>, +i: Nat) -> {pms.c(ts, i) == pms.c(If.rank(ts), i) : Nat}:
  +B = If.tbuild(ts, If.TEnd{})
  %pms.c_tsort(If.tjoin(B, If.TTip{}), i) : {pms.c(ts, i) == _ : Nat}
  %pms.c_join(B, If.TTip{}, i) : {pms.c(ts, i) == _ : Nat}
  %Equal.sym(Nat, Nat.add(pms.dc(B, i), 0n), pms.dc(B, i), pms.add_zero_r(pms.dc(B, i))) : {pms.c(ts, i) == _ : Nat}
  %pms.c_build(ts, If.TEnd{}, i) : {pms.c(ts, i) == _ : Nat}
  Equal.sym(Nat, Nat.add(pms.c(ts, i), 0n), pms.c(ts, i), pms.add_zero_r(pms.c(ts, i)))

# ranking keeps every count
def pi.count_rank(+ts: List<&2, If.Tool>, +i: Nat) -> {If.count(ts, i) == If.count(If.rank(ts), i) : Nat}:
  Equal.trans(Nat, If.count(ts, i), pms.c(ts, i), If.count(If.rank(ts), i),
    Equal.sym(Nat, pms.c(ts, i), If.count(ts, i), pms.c_count(ts, i)),
    Equal.trans(Nat, pms.c(ts, i), pms.c(If.rank(ts), i), If.count(If.rank(ts), i),
      pms.c_rank(ts, i), pms.c_count(If.rank(ts), i)))

# Sortedness
# ----------

def pi.strict_keeps_every_tool(+cap: Nat, +ts: List<&2, If.Tool>, +i: Nat) -> {Nat.add(If.count(Pair.fst(List<&2, If.Tool>, List<&2, If.Tool>, If.strict(cap, ts)), i), If.count(Pair.snd(List<&2, If.Tool>, List<&2, If.Tool>, If.strict(cap, ts)), i)) == If.count(ts, i) : Nat}:
  +R = If.rank(ts)
  Equal.trans(Nat, Nat.add(If.count(List.take(&2, If.Tool, R, cap), i), If.count(List.drop(&2, If.Tool, R, cap), i)), If.count(R, i), If.count(ts, i), pi.count_split(R, cap, i), Equal.sym(Nat, If.count(ts, i), If.count(R, i), pi.count_rank(ts, i)))

def Infer.strict_keeps_every_tool(cap, ts, i):
  pi.strict_keeps_every_tool(cap, ts, i)
