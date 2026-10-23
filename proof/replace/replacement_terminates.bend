# eukhe: the proof of LAW replacement_terminates

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ../base/logic/logic.bend as LLogicLogic
import ../base/logic/nat.bend as LLogicNat
import ../base/nat.bend as LNat
import ./base.bend as LA

# ---- replace ----

# proof_replace: the replacement laws of LAWS.bend section supervisor (D1), on the
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

# Logic
# -----

def replace.pr.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def replace.pr.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      LLogicLogic.supervisor.ps.absurdF({b == True{} : Bool}, e)

def pr.ranks_eq_sound(xs: List<&2, Nat>, ys: List<&2, Nat>, +e: {Rp.ranks_eq(xs, ys) == True{} : Bool}) -> {xs == ys : List<&2, Nat>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yr:
      LLogicLogic.supervisor.ps.absurdF({Nil{} == y <> yr : List<&2, Nat>}, e)
    case x <> xr Nil{}:
      LLogicLogic.supervisor.ps.absurdF({x <> xr == Nil{} : List<&2, Nat>}, e)
    case +x <> +xr +y <> +yr:
      %LLogicNat.supervisor.ps.eq_of_is_eq(x, y, replace.pr.and_l(Nat.is_eq(x, y), Rp.ranks_eq(xr, yr), e)) : {x <> xr == _ <> yr : List<&2, Nat>}
      %pr.ranks_eq_sound(xr, yr, replace.pr.and_r(Nat.is_eq(x, y), Rp.ranks_eq(xr, yr), e)) : {x <> xr == x <> _ : List<&2, Nat>}
      {==}

def pr.build_eq_rank(a: Rp.Build, b: Rp.Build, e: {Rp.build_eq(a, b) == True{} : Bool}) -> {Rp.Build.rank(a) == Rp.Build.rank(b) : List<&2, Nat>}:
  match a b:
    case Rp.Build{+ra, +ia} Rp.Build{+rb, +ib}:
      pr.ranks_eq_sound(ra, rb, replace.pr.and_r(String.eq(ia, ib), Rp.ranks_eq(ra, rb), e))

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
      LA.pr.clash({Nat.is_le(Nat.add(1n, x), Nat.add(0n, y)) == True{} : Bool}, Rp.lt(rb, re), LA.pr.lt_trans(rb, rc, re, h, ep), eq)
    case False{} True{}:
      LNat.supervisor.ps.le_trans(x, y, 1n+y, ih, LNat.supervisor.ps.le_succ(y))
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
      LA.pr.clash({Nat.is_le(1n+Nat.add(1n, x), Nat.add(0n, y)) == True{} : Bool}, Rp.lt(rb, re), LA.pr.lt_trans(rb, rc, re, h, ep), eq)
    case False{} True{}:
      LNat.supervisor.ps.le_trans(x, 1n+x, y, LNat.supervisor.ps.le_succ(x), ih)
    case False{} False{}:
      ih

def pr.member.put(be: Bool, +e: Rp.Build, +t: List<&2, Rp.Build>, +c: Rp.Build, +rb: List<&2, Nat>, ebe: {Rp.build_eq(e, c) == be : Bool}, m: {Bool.or(be, Rp.has(t, c)) == True{} : Bool}, +h: {Rp.lt(rb, Rp.Build.rank(c)) == True{} : Bool}, ih: {Rp.has(t, c) == True{} : Bool} -> {Nat.is_le(1n+pr.above(t, Rp.Build.rank(c)), pr.above(t, rb)) == True{} : Bool}) -> {Nat.is_le(1n+Nat.add(pr.one(Rp.lt(Rp.Build.rank(c), Rp.Build.rank(e))), pr.above(t, Rp.Build.rank(c))), Nat.add(pr.one(Rp.lt(rb, Rp.Build.rank(e))), pr.above(t, rb))) == True{} : Bool}:
  match be:
    case True{}:
      %Equal.sym(List<&2, Nat>, Rp.Build.rank(e), Rp.Build.rank(c), pr.build_eq_rank(e, c, ebe)) : {Nat.is_le(1n+Nat.add(pr.one(Rp.lt(Rp.Build.rank(c), _)), pr.above(t, Rp.Build.rank(c))), Nat.add(pr.one(Rp.lt(rb, _)), pr.above(t, rb))) == True{} : Bool}
      %Equal.sym(Bool, Rp.lt(Rp.Build.rank(c), Rp.Build.rank(c)), False{}, LA.pr.lt_irrefl(Rp.Build.rank(c))) : {Nat.is_le(1n+Nat.add(pr.one(_), pr.above(t, Rp.Build.rank(c))), Nat.add(pr.one(Rp.lt(rb, Rp.Build.rank(c))), pr.above(t, rb))) == True{} : Bool}
      %Equal.sym(Bool, Rp.lt(rb, Rp.Build.rank(c)), True{}, h) : {Nat.is_le(1n+Nat.add(pr.one(False{}), pr.above(t, Rp.Build.rank(c))), Nat.add(pr.one(_), pr.above(t, rb))) == True{} : Bool}
      pr.above_weak(t, rb, Rp.Build.rank(c), h)
    case False{}:
      pr.strict.put(Rp.lt(Rp.Build.rank(c), Rp.Build.rank(e)), Rp.lt(rb, Rp.Build.rank(e)), pr.above(t, Rp.Build.rank(c)), pr.above(t, rb), rb, Rp.Build.rank(c), Rp.Build.rank(e), {==}, {==}, h, ih(m))

# a build c of bs above rank rb: c and the builds above it are above rb
def pr.above_strict(bs: List<&2, Rp.Build>, +rb: List<&2, Nat>, +c: Rp.Build, +h: {Rp.lt(rb, Rp.Build.rank(c)) == True{} : Bool}, m: {Rp.has(bs, c) == True{} : Bool}) -> {Nat.is_le(1n+pr.above(bs, Rp.Build.rank(c)), pr.above(bs, rb)) == True{} : Bool}:
  match bs:
    case Nil{}:
      LLogicLogic.supervisor.ps.absurdF({Nat.is_le(1n+pr.above(Nil{}, Rp.Build.rank(c)), pr.above(Nil{}, rb)) == True{} : Bool}, m)
    case +e <> +t:
      pr.member.put(Rp.build_eq(e, c), e, t, c, rb, {==}, m, h, i => pr.above_strict(t, rb, c, h, i))

def pr.len.put(p: Bool, +x: Nat, +n: Nat, ih: {Nat.is_le(x, n) == True{} : Bool}) -> {Nat.is_le(Nat.add(pr.one(p), x), 1n+n) == True{} : Bool}:
  match p:
    case True{}:
      ih
    case False{}:
      LNat.supervisor.ps.le_trans(x, n, 1n+n, ih, LNat.supervisor.ps.le_succ(n))

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
      LNat.supervisor.ps.le_trans(x, 1n+x, n, LNat.supervisor.ps.le_succ(x), ih)

def pr.member_len.put(be: Bool, +e: Rp.Build, +t: List<&2, Rp.Build>, +c: Rp.Build, ebe: {Rp.build_eq(e, c) == be : Bool}, m: {Bool.or(be, Rp.has(t, c)) == True{} : Bool}, ih: {Rp.has(t, c) == True{} : Bool} -> {Nat.is_le(1n+pr.above(t, Rp.Build.rank(c)), List.length(&2, Rp.Build, t)) == True{} : Bool}) -> {Nat.is_le(1n+Nat.add(pr.one(Rp.lt(Rp.Build.rank(c), Rp.Build.rank(e))), pr.above(t, Rp.Build.rank(c))), 1n+List.length(&2, Rp.Build, t)) == True{} : Bool}:
  match be:
    case True{}:
      %Equal.sym(List<&2, Nat>, Rp.Build.rank(e), Rp.Build.rank(c), pr.build_eq_rank(e, c, ebe)) : {Nat.is_le(1n+Nat.add(pr.one(Rp.lt(Rp.Build.rank(c), _)), pr.above(t, Rp.Build.rank(c))), 1n+List.length(&2, Rp.Build, t)) == True{} : Bool}
      %Equal.sym(Bool, Rp.lt(Rp.Build.rank(c), Rp.Build.rank(c)), False{}, LA.pr.lt_irrefl(Rp.Build.rank(c))) : {Nat.is_le(1n+Nat.add(pr.one(_), pr.above(t, Rp.Build.rank(c))), 1n+List.length(&2, Rp.Build, t)) == True{} : Bool}
      pr.above_le_len(t, Rp.Build.rank(c))
    case False{}:
      pr.mlen.put(Rp.lt(Rp.Build.rank(c), Rp.Build.rank(e)), pr.above(t, Rp.Build.rank(c)), List.length(&2, Rp.Build, t), ih(m))

# a build c of bs: at most |bs| - 1 builds of bs above it
def pr.above_member(bs: List<&2, Rp.Build>, +c: Rp.Build, m: {Rp.has(bs, c) == True{} : Bool}) -> {Nat.is_le(1n+pr.above(bs, Rp.Build.rank(c)), List.length(&2, Rp.Build, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      LLogicLogic.supervisor.ps.absurdF({Nat.is_le(1n+pr.above(Nil{}, Rp.Build.rank(c)), 0n) == True{} : Bool}, m)
    case +e <> +t:
      pr.member_len.put(Rp.build_eq(e, c), e, t, c, {==}, m, i => pr.above_member(t, c, i))

def pr.count.put(v: Rp.Verdict, +c: Rp.Build, +b: Rp.Build, -k: Rp.Caller, +rest: List<&2, Rp.Start>, +bs: List<&2, Rp.Build>, ev: {Rp.verdict(c, b, k) == v : Rp.Verdict}, mc: {Rp.has(bs, c) == True{} : Bool}, ih: @d: Rp.Build -> {Nat.is_le(Rp.replaced.go(rest, Some{d}), pr.above(bs, Rp.Build.rank(d))) == True{} : Bool}) -> {Nat.is_le(Nat.add(Rp.replaces.put(v), Rp.replaced.go(rest, Some{Rp.after.put(v, c, b)})), pr.above(bs, Rp.Build.rank(b))) == True{} : Bool}:
  match v:
    case Rp.Replace{}:
      LNat.supervisor.ps.le_trans(1n+Rp.replaced.go(rest, Some{c}), 1n+pr.above(bs, Rp.Build.rank(c)), pr.above(bs, Rp.Build.rank(b)), ih(c), pr.above_strict(bs, Rp.Build.rank(b), c, LA.pr.replace_older(c, b, k, ev), mc))
    case Rp.Keep{r}:
      ih(b)

# from the daemon b, the replacements are at most the builds of bs above b
def pr.count_le(ss: List<&2, Rp.Start>, +bs: List<&2, Rp.Build>, +b: Rp.Build, +cov: {Rp.covers(bs, ss) == True{} : Bool}) -> {Nat.is_le(Rp.replaced.go(ss, Some{b}), pr.above(bs, Rp.Build.rank(b))) == True{} : Bool}:
  match ss:
    case Nil{}:
      LNat.ps.le_zero(pr.above(bs, Rp.Build.rank(b)))
    case s <> +rest:
      match s:
        case Rp.Start{+c, +k}:
          pr.count.put(Rp.verdict(c, b, k), c, b, k, rest, bs, {==}, replace.pr.and_l(Rp.has(bs, c), Rp.covers(bs, rest), cov), d => pr.count_le(rest, bs, d, replace.pr.and_r(Rp.has(bs, c), Rp.covers(bs, rest), cov)))

def pr.le_pred(+a: Nat, n: Nat, h: {Nat.is_le(1n+a, n) == True{} : Bool}) -> {Nat.is_le(a, Nat.sub(n, 1n)) == True{} : Bool}:
  match n:
    case 0n:
      LLogicLogic.supervisor.ps.absurdF({Nat.is_le(a, Nat.sub(0n, 1n)) == True{} : Bool}, h)
    case 1n+m:
      match m:
        case 0n:
          h
        case 1n+j:
          h

def pr.replacement_terminates(+bs: List<&2, Rp.Build>, ss: List<&2, Rp.Start>, +cover: {Rp.covers(bs, ss) == True{} : Bool}) -> {Nat.is_le(Rp.replaced(ss), Nat.sub(List.length(&2, Rp.Build, bs), 1n)) == True{} : Bool}:
  match ss:
    case Nil{}:
      LNat.ps.le_zero(Nat.sub(List.length(&2, Rp.Build, bs), 1n))
    case s <> +rest:
      match s:
        case Rp.Start{+c, k}:
          pr.le_pred(Rp.replaced.go(rest, Some{c}), List.length(&2, Rp.Build, bs), LNat.supervisor.ps.le_trans(1n+Rp.replaced.go(rest, Some{c}), 1n+pr.above(bs, Rp.Build.rank(c)), List.length(&2, Rp.Build, bs), pr.count_le(rest, bs, c, replace.pr.and_r(Rp.has(bs, c), Rp.covers(bs, rest), cover)), pr.above_member(bs, c, replace.pr.and_l(Rp.has(bs, c), Rp.covers(bs, rest), cover))))

def Replace.replacement_terminates(bs, ss, cover):
  pr.replacement_terminates(bs, ss, cover)
