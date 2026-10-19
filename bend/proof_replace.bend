# proof_replace: the replacement laws of laws/supervisor.bend (D1), on the
# model bend/replace.bend.
#
# - replace_never_downgrades: a start replaces the daemon only with a build
#   of a higher rank (`pr.replace_older`), and the rank order is transitive
#   (`pr.lt_trans`), so the daemon after a start is below no daemon before
#   it (`pr.rising`).
# - replacement_terminates: each replacement moves the daemon to a build of
#   bs of a higher rank, so the count of the builds of bs above the daemon
#   falls by one at least (`pr.above_strict`); the first daemon has at most
#   |bs| - 1 builds of bs above it (`pr.above_member`).
# - background_never_replaces: the verdict of a background start is always
#   a keep.

import Base
import ./replace.bend as Rp
import ./proof_supervisor.bend as Ps

# Logic
# -----

def pr.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def pr.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Ps.ps.absurdF({b == True{} : Bool}, e)

# x cannot be True and False
def pr.clash(-A: Type, -x: Bool, t: {x == True{} : Bool}, f: {x == False{} : Bool}) -> A:
  Ps.ps.absurdF(A, Equal.trans(Bool, False{}, x, True{}, Equal.sym(Bool, x, False{}, f), t))

def pr.VD(v: Rp.Verdict, A: Type) -> Type:
  match v:
    case Rp.Replace{}:
      A
    case Rp.Keep{r}:
      Unit

def pr.not_replace(-A: Type, -v: Rp.Verdict, e: {v == Rp.Replace{} : Rp.Verdict}, u: pr.VD(v, A)) -> A:
  %e : pr.VD(_, A)
  u

def pr.RD(r: Rp.Rel, A: Type) -> Type:
  match r:
    case Rp.Same{}:
      Unit
    case Rp.Older{}:
      A
    case Rp.Newer{}:
      Unit
    case Rp.Other{}:
      Unit

def pr.not_older(-A: Type, -r: Rp.Rel, e: {r == Rp.Older{} : Rp.Rel}, u: pr.RD(r, A)) -> A:
  %e : pr.RD(_, A)
  u

# The order
# ---------

def pr.lex_same(x: Nat, -t: Bool) -> {Rp.lex(x, x, t) == t : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      pr.lex_same(p, t)

def pr.lt_irrefl(xs: List<&2, Nat>) -> {Rp.lt(xs, xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +xr:
      Equal.trans(Bool, Rp.lex(x, x, Rp.lt(xr, xr)), Rp.lt(xr, xr), False{}, pr.lex_same(x, Rp.lt(xr, xr)), pr.lt_irrefl(xr))

def pr.lex_trans(x: Nat, y: Nat, z: Nat, -t1: Bool, -t2: Bool, -t3: Bool, h1: {Rp.lex(x, y, t1) == True{} : Bool}, h2: {Rp.lex(y, z, t2) == True{} : Bool}, k: {t1 == True{} : Bool} -> {t2 == True{} : Bool} -> {t3 == True{} : Bool}) -> {Rp.lex(x, z, t3) == True{} : Bool}:
  match x y z:
    case 0n 0n 0n:
      k(h1, h2)
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      Ps.ps.absurdF({Rp.lex(0n, 0n, t3) == True{} : Bool}, h2)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      Ps.ps.absurdF({Rp.lex(1n+p, z, t3) == True{} : Bool}, h1)
    case 1n+p 1n+q 0n:
      Ps.ps.absurdF({Rp.lex(1n+p, 0n, t3) == True{} : Bool}, h2)
    case 1n+p 1n+q 1n+r:
      pr.lex_trans(p, q, r, t1, t2, t3, h1, h2, k)

def pr.lt_trans(xs: List<&2, Nat>, ys: List<&2, Nat>, zs: List<&2, Nat>, h1: {Rp.lt(xs, ys) == True{} : Bool}, h2: {Rp.lt(ys, zs) == True{} : Bool}) -> {Rp.lt(xs, zs) == True{} : Bool}:
  match xs ys zs:
    case Nil{} Nil{} _:
      Ps.ps.absurdF({Rp.lt(Nil{}, zs) == True{} : Bool}, h1)
    case Nil{} y <> yr Nil{}:
      Ps.ps.absurdF({Rp.lt(Nil{}, Nil{}) == True{} : Bool}, h2)
    case Nil{} y <> yr z <> zr:
      {==}
    case x <> xr Nil{} _:
      Ps.ps.absurdF({Rp.lt(x <> xr, zs) == True{} : Bool}, h1)
    case x <> xr y <> yr Nil{}:
      Ps.ps.absurdF({Rp.lt(x <> xr, Nil{}) == True{} : Bool}, h2)
    case x <> +xr y <> +yr z <> +zr:
      pr.lex_trans(x, y, z, Rp.lt(xr, yr), Rp.lt(yr, zr), Rp.lt(xr, zr), h1, h2, a => b => pr.lt_trans(xr, yr, zr, a, b))

def pr.ranks_eq_sound(xs: List<&2, Nat>, ys: List<&2, Nat>, +e: {Rp.ranks_eq(xs, ys) == True{} : Bool}) -> {xs == ys : List<&2, Nat>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yr:
      Ps.ps.absurdF({Nil{} == y <> yr : List<&2, Nat>}, e)
    case x <> xr Nil{}:
      Ps.ps.absurdF({x <> xr == Nil{} : List<&2, Nat>}, e)
    case +x <> +xr +y <> +yr:
      %Ps.ps.eq_of_is_eq(x, y, pr.and_l(Nat.is_eq(x, y), Rp.ranks_eq(xr, yr), e)) : {x <> xr == _ <> yr : List<&2, Nat>}
      %pr.ranks_eq_sound(xr, yr, pr.and_r(Nat.is_eq(x, y), Rp.ranks_eq(xr, yr), e)) : {x <> xr == x <> _ : List<&2, Nat>}
      {==}

def pr.build_eq_rank(a: Rp.Build, b: Rp.Build, e: {Rp.build_eq(a, b) == True{} : Bool}) -> {Rp.Build.rank(a) == Rp.Build.rank(b) : List<&2, Nat>}:
  match a b:
    case Rp.Build{+ra, +ia} Rp.Build{+rb, +ib}:
      pr.ranks_eq_sound(ra, rb, pr.and_r(Nat.is_eq(ia, ib), Rp.ranks_eq(ra, rb), e))

# The verdict
# -----------

def pr.put_replace(r: Rp.Rel, -k: Rp.Caller, e: {Rp.verdict.put(r, k) == Rp.Replace{} : Rp.Verdict}) -> {r == Rp.Older{} : Rp.Rel}:
  match r:
    case Rp.Same{}:
      pr.not_replace({Rp.Same{} == Rp.Older{} : Rp.Rel}, Rp.Keep{Rp.Same{}}, e, Unit{})
    case Rp.Older{}:
      {==}
    case Rp.Newer{}:
      pr.not_replace({Rp.Newer{} == Rp.Older{} : Rp.Rel}, Rp.Keep{Rp.Newer{}}, e, Unit{})
    case Rp.Other{}:
      pr.not_replace({Rp.Other{} == Rp.Older{} : Rp.Rel}, Rp.Keep{Rp.Other{}}, e, Unit{})

def pr.rel_older(same: Bool, older: Bool, newer: Bool, e: {Rp.rel.put(same, older, newer) == Rp.Older{} : Rp.Rel}) -> {older == True{} : Bool}:
  match same:
    case True{}:
      pr.not_older({older == True{} : Bool}, Rp.Same{}, e, Unit{})
    case False{}:
      match older:
        case True{}:
          {==}
        case False{}:
          match newer:
            case True{}:
              pr.not_older({False{} == True{} : Bool}, Rp.Newer{}, e, Unit{})
            case False{}:
              pr.not_older({False{} == True{} : Bool}, Rp.Other{}, e, Unit{})

# a replacement moves the daemon b to a client c of a higher rank
def pr.replace_older(c: Rp.Build, b: Rp.Build, -k: Rp.Caller, e: {Rp.verdict(c, b, k) == Rp.Replace{} : Rp.Verdict}) -> {Rp.lt(Rp.Build.rank(b), Rp.Build.rank(c)) == True{} : Bool}:
  match c b:
    case Rp.Build{+rc, +ic} Rp.Build{+rb, +ib}:
      pr.rel_older(Nat.is_eq(ic, ib), Rp.lt(rb, rc), Rp.lt(rc, rb), pr.put_replace(Rp.rel.put(Nat.is_eq(ic, ib), Rp.lt(rb, rc), Rp.lt(rc, rb)), k, e))

# (D1) replace_never_downgrades
# -----------------------------

def pr.nb_self(-S: List<&2, Rp.Build>, +b: Rp.Build, inv: {Rp.not_below(S, b) == True{} : Bool}) -> {Rp.not_below(b <> S, b) == True{} : Bool}:
  %Equal.sym(Bool, Rp.lt(Rp.Build.rank(b), Rp.Build.rank(b)), False{}, pr.lt_irrefl(Rp.Build.rank(b))) : {Bool.and(Bool.not(_), Rp.not_below(S, b)) == True{} : Bool}
  inv

def pr.lift.put(p: Bool, q: Bool, rb: List<&2, Nat>, rc: List<&2, Nat>, re: List<&2, Nat>, -t1: Bool, -t2: Bool, ep: {Rp.lt(rb, re) == p : Bool}, eq: {Rp.lt(rc, re) == q : Bool}, h: {Rp.lt(rb, rc) == True{} : Bool}, inv: {Bool.and(Bool.not(p), t1) == True{} : Bool}, ih: {t1 == True{} : Bool} -> {t2 == True{} : Bool}) -> {Bool.and(Bool.not(q), t2) == True{} : Bool}:
  match p q:
    case True{} True{}:
      Ps.ps.absurdF({Bool.and(Bool.not(True{}), t2) == True{} : Bool}, inv)
    case True{} False{}:
      Ps.ps.absurdF({Bool.and(Bool.not(False{}), t2) == True{} : Bool}, inv)
    case False{} True{}:
      pr.clash({Bool.and(Bool.not(True{}), t2) == True{} : Bool}, Rp.lt(rb, re), pr.lt_trans(rb, rc, re, h, eq), ep)
    case False{} False{}:
      ih(inv)

# b below none of S and c above b: c below none of S
def pr.lift(S: List<&2, Rp.Build>, +b: Rp.Build, +c: Rp.Build, +h: {Rp.lt(Rp.Build.rank(b), Rp.Build.rank(c)) == True{} : Bool}, inv: {Rp.not_below(S, b) == True{} : Bool}) -> {Rp.not_below(S, c) == True{} : Bool}:
  match S:
    case Nil{}:
      {==}
    case +e <> +t:
      pr.lift.put(Rp.lt(Rp.Build.rank(b), Rp.Build.rank(e)), Rp.lt(Rp.Build.rank(c), Rp.Build.rank(e)), Rp.Build.rank(b), Rp.Build.rank(c), Rp.Build.rank(e), Rp.not_below(t, b), Rp.not_below(t, c), {==}, {==}, h, inv, i => pr.lift(t, b, c, h, i))

def pr.next.put(v: Rp.Verdict, +c: Rp.Build, +b: Rp.Build, -k: Rp.Caller, +S: List<&2, Rp.Build>, ev: {Rp.verdict(c, b, k) == v : Rp.Verdict}, inv: {Rp.not_below(S, b) == True{} : Bool}) -> {Rp.not_below(b <> S, Rp.after.put(v, c, b)) == True{} : Bool}:
  match v:
    case Rp.Replace{}:
      pr.lift(b <> S, b, c, pr.replace_older(c, b, k, ev), pr.nb_self(S, b, inv))
    case Rp.Keep{r}:
      pr.nb_self(S, b, inv)

# from the daemon b, below none of S, no daemon goes back
def pr.rising(ss: List<&2, Rp.Start>, +b: Rp.Build, +S: List<&2, Rp.Build>, +inv: {Rp.not_below(S, b) == True{} : Bool}) -> {Rp.never_back.go(Rp.trace.go(ss, Some{b}), b <> S) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case s <> +rest:
      match s:
        case Rp.Start{+c, +k}:
          Ps.ps.and_t(Rp.not_below(b <> S, Rp.after.put(Rp.verdict(c, b, k), c, b)), Rp.never_back.go(Rp.trace.go(rest, Some{Rp.after.put(Rp.verdict(c, b, k), c, b)}), Rp.after.put(Rp.verdict(c, b, k), c, b) <> (b <> S)), pr.next.put(Rp.verdict(c, b, k), c, b, k, S, {==}, inv), pr.rising(rest, Rp.after.put(Rp.verdict(c, b, k), c, b), b <> S, pr.next.put(Rp.verdict(c, b, k), c, b, k, S, {==}, inv)))

def pr.replace_never_downgrades(ss: List<&2, Rp.Start>) -> {Rp.never_back(Rp.daemons(ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Rp.Start{+c, k}:
          pr.rising(rest, c, Nil{}, {==})

# (D1) replacement_terminates
# ---------------------------

def pr.one(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# the builds of bs above rank r
def pr.above(bs: List<&2, Rp.Build>, +r: List<&2, Nat>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case e <> t:
      Nat.add(pr.one(Rp.lt(r, Rp.Build.rank(e))), pr.above(t, r))

def pr.weak.put(p: Bool, q: Bool, +x: Nat, +y: Nat, rb: List<&2, Nat>, rc: List<&2, Nat>, re: List<&2, Nat>, ep: {Rp.lt(rc, re) == p : Bool}, eq: {Rp.lt(rb, re) == q : Bool}, h: {Rp.lt(rb, rc) == True{} : Bool}, ih: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.add(pr.one(p), x), Nat.add(pr.one(q), y)) == True{} : Bool}:
  match p q:
    case True{} True{}:
      ih
    case True{} False{}:
      pr.clash({Nat.is_le(Nat.add(1n, x), Nat.add(0n, y)) == True{} : Bool}, Rp.lt(rb, re), pr.lt_trans(rb, rc, re, h, ep), eq)
    case False{} True{}:
      Ps.ps.le_trans(x, y, 1n+y, ih, Ps.ps.le_succ(y))
    case False{} False{}:
      ih

# rank rc above rank rb: fewer builds above rc than above rb
def pr.above_weak(bs: List<&2, Rp.Build>, +rb: List<&2, Nat>, +rc: List<&2, Nat>, +h: {Rp.lt(rb, rc) == True{} : Bool}) -> {Nat.is_le(pr.above(bs, rc), pr.above(bs, rb)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +e <> +t:
      pr.weak.put(Rp.lt(rc, Rp.Build.rank(e)), Rp.lt(rb, Rp.Build.rank(e)), pr.above(t, rc), pr.above(t, rb), rb, rc, Rp.Build.rank(e), {==}, {==}, h, pr.above_weak(t, rb, rc, h))

def pr.strict.put(p: Bool, q: Bool, +x: Nat, +y: Nat, rb: List<&2, Nat>, rc: List<&2, Nat>, re: List<&2, Nat>, ep: {Rp.lt(rc, re) == p : Bool}, eq: {Rp.lt(rb, re) == q : Bool}, h: {Rp.lt(rb, rc) == True{} : Bool}, ih: {Nat.is_le(1n+x, y) == True{} : Bool}) -> {Nat.is_le(1n+Nat.add(pr.one(p), x), Nat.add(pr.one(q), y)) == True{} : Bool}:
  match p q:
    case True{} True{}:
      ih
    case True{} False{}:
      pr.clash({Nat.is_le(1n+Nat.add(1n, x), Nat.add(0n, y)) == True{} : Bool}, Rp.lt(rb, re), pr.lt_trans(rb, rc, re, h, ep), eq)
    case False{} True{}:
      Ps.ps.le_trans(x, 1n+x, y, Ps.ps.le_succ(x), ih)
    case False{} False{}:
      ih

def pr.member.put(be: Bool, +e: Rp.Build, +t: List<&2, Rp.Build>, +c: Rp.Build, +rb: List<&2, Nat>, ebe: {Rp.build_eq(e, c) == be : Bool}, m: {Bool.or(be, Rp.has(t, c)) == True{} : Bool}, +h: {Rp.lt(rb, Rp.Build.rank(c)) == True{} : Bool}, ih: {Rp.has(t, c) == True{} : Bool} -> {Nat.is_le(1n+pr.above(t, Rp.Build.rank(c)), pr.above(t, rb)) == True{} : Bool}) -> {Nat.is_le(1n+Nat.add(pr.one(Rp.lt(Rp.Build.rank(c), Rp.Build.rank(e))), pr.above(t, Rp.Build.rank(c))), Nat.add(pr.one(Rp.lt(rb, Rp.Build.rank(e))), pr.above(t, rb))) == True{} : Bool}:
  match be:
    case True{}:
      %Equal.sym(List<&2, Nat>, Rp.Build.rank(e), Rp.Build.rank(c), pr.build_eq_rank(e, c, ebe)) : {Nat.is_le(1n+Nat.add(pr.one(Rp.lt(Rp.Build.rank(c), _)), pr.above(t, Rp.Build.rank(c))), Nat.add(pr.one(Rp.lt(rb, _)), pr.above(t, rb))) == True{} : Bool}
      %Equal.sym(Bool, Rp.lt(Rp.Build.rank(c), Rp.Build.rank(c)), False{}, pr.lt_irrefl(Rp.Build.rank(c))) : {Nat.is_le(1n+Nat.add(pr.one(_), pr.above(t, Rp.Build.rank(c))), Nat.add(pr.one(Rp.lt(rb, Rp.Build.rank(c))), pr.above(t, rb))) == True{} : Bool}
      %Equal.sym(Bool, Rp.lt(rb, Rp.Build.rank(c)), True{}, h) : {Nat.is_le(1n+Nat.add(pr.one(False{}), pr.above(t, Rp.Build.rank(c))), Nat.add(pr.one(_), pr.above(t, rb))) == True{} : Bool}
      pr.above_weak(t, rb, Rp.Build.rank(c), h)
    case False{}:
      pr.strict.put(Rp.lt(Rp.Build.rank(c), Rp.Build.rank(e)), Rp.lt(rb, Rp.Build.rank(e)), pr.above(t, Rp.Build.rank(c)), pr.above(t, rb), rb, Rp.Build.rank(c), Rp.Build.rank(e), {==}, {==}, h, ih(m))

# a build c of bs above rank rb: c and the builds above it are above rb
def pr.above_strict(bs: List<&2, Rp.Build>, +rb: List<&2, Nat>, +c: Rp.Build, +h: {Rp.lt(rb, Rp.Build.rank(c)) == True{} : Bool}, m: {Rp.has(bs, c) == True{} : Bool}) -> {Nat.is_le(1n+pr.above(bs, Rp.Build.rank(c)), pr.above(bs, rb)) == True{} : Bool}:
  match bs:
    case Nil{}:
      Ps.ps.absurdF({Nat.is_le(1n+pr.above(Nil{}, Rp.Build.rank(c)), pr.above(Nil{}, rb)) == True{} : Bool}, m)
    case +e <> +t:
      pr.member.put(Rp.build_eq(e, c), e, t, c, rb, {==}, m, h, i => pr.above_strict(t, rb, c, h, i))

def pr.len.put(p: Bool, +x: Nat, +n: Nat, ih: {Nat.is_le(x, n) == True{} : Bool}) -> {Nat.is_le(Nat.add(pr.one(p), x), 1n+n) == True{} : Bool}:
  match p:
    case True{}:
      ih
    case False{}:
      Ps.ps.le_trans(x, n, 1n+n, ih, Ps.ps.le_succ(n))

def pr.above_le_len(bs: List<&2, Rp.Build>, +r: List<&2, Nat>) -> {Nat.is_le(pr.above(bs, r), List.length(&2, Rp.Build, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +e <> +t:
      pr.len.put(Rp.lt(r, Rp.Build.rank(e)), pr.above(t, r), List.length(&2, Rp.Build, t), pr.above_le_len(t, r))

def pr.mlen.put(p: Bool, +x: Nat, +n: Nat, ih: {Nat.is_le(1n+x, n) == True{} : Bool}) -> {Nat.is_le(1n+Nat.add(pr.one(p), x), 1n+n) == True{} : Bool}:
  match p:
    case True{}:
      ih
    case False{}:
      Ps.ps.le_trans(x, 1n+x, n, Ps.ps.le_succ(x), ih)

def pr.member_len.put(be: Bool, +e: Rp.Build, +t: List<&2, Rp.Build>, +c: Rp.Build, ebe: {Rp.build_eq(e, c) == be : Bool}, m: {Bool.or(be, Rp.has(t, c)) == True{} : Bool}, ih: {Rp.has(t, c) == True{} : Bool} -> {Nat.is_le(1n+pr.above(t, Rp.Build.rank(c)), List.length(&2, Rp.Build, t)) == True{} : Bool}) -> {Nat.is_le(1n+Nat.add(pr.one(Rp.lt(Rp.Build.rank(c), Rp.Build.rank(e))), pr.above(t, Rp.Build.rank(c))), 1n+List.length(&2, Rp.Build, t)) == True{} : Bool}:
  match be:
    case True{}:
      %Equal.sym(List<&2, Nat>, Rp.Build.rank(e), Rp.Build.rank(c), pr.build_eq_rank(e, c, ebe)) : {Nat.is_le(1n+Nat.add(pr.one(Rp.lt(Rp.Build.rank(c), _)), pr.above(t, Rp.Build.rank(c))), 1n+List.length(&2, Rp.Build, t)) == True{} : Bool}
      %Equal.sym(Bool, Rp.lt(Rp.Build.rank(c), Rp.Build.rank(c)), False{}, pr.lt_irrefl(Rp.Build.rank(c))) : {Nat.is_le(1n+Nat.add(pr.one(_), pr.above(t, Rp.Build.rank(c))), 1n+List.length(&2, Rp.Build, t)) == True{} : Bool}
      pr.above_le_len(t, Rp.Build.rank(c))
    case False{}:
      pr.mlen.put(Rp.lt(Rp.Build.rank(c), Rp.Build.rank(e)), pr.above(t, Rp.Build.rank(c)), List.length(&2, Rp.Build, t), ih(m))

# a build c of bs: at most |bs| - 1 builds of bs above it
def pr.above_member(bs: List<&2, Rp.Build>, +c: Rp.Build, m: {Rp.has(bs, c) == True{} : Bool}) -> {Nat.is_le(1n+pr.above(bs, Rp.Build.rank(c)), List.length(&2, Rp.Build, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      Ps.ps.absurdF({Nat.is_le(1n+pr.above(Nil{}, Rp.Build.rank(c)), 0n) == True{} : Bool}, m)
    case +e <> +t:
      pr.member_len.put(Rp.build_eq(e, c), e, t, c, {==}, m, i => pr.above_member(t, c, i))

def pr.count.put(v: Rp.Verdict, +c: Rp.Build, +b: Rp.Build, -k: Rp.Caller, +rest: List<&2, Rp.Start>, +bs: List<&2, Rp.Build>, ev: {Rp.verdict(c, b, k) == v : Rp.Verdict}, mc: {Rp.has(bs, c) == True{} : Bool}, ih: @d: Rp.Build -> {Nat.is_le(Rp.replaced.go(rest, Some{d}), pr.above(bs, Rp.Build.rank(d))) == True{} : Bool}) -> {Nat.is_le(Nat.add(Rp.replaces.put(v), Rp.replaced.go(rest, Some{Rp.after.put(v, c, b)})), pr.above(bs, Rp.Build.rank(b))) == True{} : Bool}:
  match v:
    case Rp.Replace{}:
      Ps.ps.le_trans(1n+Rp.replaced.go(rest, Some{c}), 1n+pr.above(bs, Rp.Build.rank(c)), pr.above(bs, Rp.Build.rank(b)), ih(c), pr.above_strict(bs, Rp.Build.rank(b), c, pr.replace_older(c, b, k, ev), mc))
    case Rp.Keep{r}:
      ih(b)

# from the daemon b, the replacements are at most the builds of bs above b
def pr.count_le(ss: List<&2, Rp.Start>, +bs: List<&2, Rp.Build>, +b: Rp.Build, +cov: {Rp.covers(bs, ss) == True{} : Bool}) -> {Nat.is_le(Rp.replaced.go(ss, Some{b}), pr.above(bs, Rp.Build.rank(b))) == True{} : Bool}:
  match ss:
    case Nil{}:
      Ps.ps.le_zero(pr.above(bs, Rp.Build.rank(b)))
    case s <> +rest:
      match s:
        case Rp.Start{+c, +k}:
          pr.count.put(Rp.verdict(c, b, k), c, b, k, rest, bs, {==}, pr.and_l(Rp.has(bs, c), Rp.covers(bs, rest), cov), d => pr.count_le(rest, bs, d, pr.and_r(Rp.has(bs, c), Rp.covers(bs, rest), cov)))

def pr.le_pred(+a: Nat, n: Nat, h: {Nat.is_le(1n+a, n) == True{} : Bool}) -> {Nat.is_le(a, Nat.sub(n, 1n)) == True{} : Bool}:
  match n:
    case 0n:
      Ps.ps.absurdF({Nat.is_le(a, Nat.sub(0n, 1n)) == True{} : Bool}, h)
    case 1n+m:
      match m:
        case 0n:
          h
        case 1n+j:
          h

def pr.replacement_terminates(+bs: List<&2, Rp.Build>, ss: List<&2, Rp.Start>, +cover: {Rp.covers(bs, ss) == True{} : Bool}) -> {Nat.is_le(Rp.replaced(ss), Nat.sub(List.length(&2, Rp.Build, bs), 1n)) == True{} : Bool}:
  match ss:
    case Nil{}:
      Ps.ps.le_zero(Nat.sub(List.length(&2, Rp.Build, bs), 1n))
    case s <> +rest:
      match s:
        case Rp.Start{+c, k}:
          pr.le_pred(Rp.replaced.go(rest, Some{c}), List.length(&2, Rp.Build, bs), Ps.ps.le_trans(1n+Rp.replaced.go(rest, Some{c}), 1n+pr.above(bs, Rp.Build.rank(c)), List.length(&2, Rp.Build, bs), pr.count_le(rest, bs, c, pr.and_r(Rp.has(bs, c), Rp.covers(bs, rest), cover)), pr.above_member(bs, c, pr.and_l(Rp.has(bs, c), Rp.covers(bs, rest), cover))))

# (D1) background_never_replaces
# ------------------------------

def pr.bg(r: Rp.Rel, -c: Rp.Build, -d: Rp.Build) -> {Rp.after.put(Rp.verdict.put(r, Rp.Background{}), c, d) == d : Rp.Build}:
  match r:
    case Rp.Same{}:
      {==}
    case Rp.Older{}:
      {==}
    case Rp.Newer{}:
      {==}
    case Rp.Other{}:
      {==}

def pr.background_never_replaces(+c: Rp.Build, +d: Rp.Build) -> {Rp.after(Rp.Start{c, Rp.Background{}}, Some{d}) == d : Rp.Build}:
  pr.bg(Rp.relation(c, d), c, d)
