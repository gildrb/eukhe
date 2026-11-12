# eukhe: lemmas shared by the proofs of area slash_suggest: the code's row
# of distances is the spec's Levenshtein distance to each suffix (by
# induction on the first name, then on the second), and each choice of
# bend/slash_suggest.bend is the spec's (case by case)

import Base
import ../../bend/slash_suggest.bend as Ss
import ../../bend/skill_load.bend as Sl
import ../../laws/slash_suggest.bend as SlashSuggest
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/base.bend as LawsBase
import ../base/staging.bend as LStg

# The spec's row: the distances from a to each suffix of b, longest first
def ssb.srow(+a: String, b: String) -> List<&2, Nat>:
  match b:
    case SNil{}:
      [SlashSuggest.sp_lev(a, SNil{})]
    case SCon{+x, +u}:
      SlashSuggest.sp_lev(a, SCon{x, u}) <> ssb.srow(a, u)

# the head of a row is the distance to the whole name
def ssb.head(+a: String, b: String) -> {Ss.head(ssb.srow(a, b)) == SlashSuggest.sp_lev(a, b) : Nat}:
  match b:
    case SNil{}:
      {==}
    case SCon{+x, +u}:
      {==}

# the distance to the empty name is the length
def ssb.empty(t: String) -> {SlashSuggest.sp_lev(t, SNil{}) == String.length(t) : Nat}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      {==}

def ssb.min.at(b: Bool, x: Nat, y: Nat) -> {Ss.min.of(b, x, y) == SlashSuggest.sp_pick(b, x, y) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ssb.min(+x: Nat, +y: Nat) -> {Ss.min(x, y) == SlashSuggest.sp_min(x, y) : Nat}:
  ssb.min.at(Nat.is_le(x, y), x, y)

def ssb.ne.at(b: Bool) -> {Ss.ne.of(b) == SlashSuggest.sp_cost(b) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ssb.ne(+c: Char, +x: Char) -> {Ss.ne(c, x) == SlashSuggest.sp_cost(Char.is_eq(c, x)) : Nat}:
  ssb.ne.at(Char.is_eq(c, x))

# the row of the empty name: the suffix lengths
def ssb.lens(b: String) -> {Ss.lens(b) == ssb.srow(SNil{}, b) : List<&2, Nat>}:
  match b:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      %Equal.sym(List<&2, Nat>, Ss.lens(t), ssb.srow(SNil{}, t), ssb.lens(t)) : {Nat.add(1n, Ss.head(_)) <> _ == ssb.srow(SNil{}, SCon{x, t}) : List<&2, Nat>}
      %Equal.sym(Nat, Ss.head(ssb.srow(SNil{}, t)), SlashSuggest.sp_lev(SNil{}, t), ssb.head(SNil{}, t)) : {Nat.add(1n, _) <> ssb.srow(SNil{}, t) == ssb.srow(SNil{}, SCon{x, t}) : List<&2, Nat>}
      {==}

# one cell of the row of c before t, from the row of t
def ssb.cell(+c: Char, +t: String, +x: Char, +u: String, r: List<&2, Nat>, e: {r == ssb.srow(SCon{c, t}, u) : List<&2, Nat>}) -> {Ss.min(Ss.min(Nat.add(1n, SlashSuggest.sp_lev(t, SCon{x, u})), Nat.add(1n, Ss.head(r))), Nat.add(Ss.head(ssb.srow(t, u)), Ss.ne(c, x))) <> r == ssb.srow(SCon{c, t}, SCon{x, u}) : List<&2, Nat>}:
  %Equal.sym(List<&2, Nat>, r, ssb.srow(SCon{c, t}, u), e) : {Ss.min(Ss.min(Nat.add(1n, SlashSuggest.sp_lev(t, SCon{x, u})), Nat.add(1n, Ss.head(_))), Nat.add(Ss.head(ssb.srow(t, u)), Ss.ne(c, x))) <> _ == ssb.srow(SCon{c, t}, SCon{x, u}) : List<&2, Nat>}
  %Equal.sym(Nat, Ss.head(ssb.srow(SCon{c, t}, u)), SlashSuggest.sp_lev(SCon{c, t}, u), ssb.head(SCon{c, t}, u)) : {Ss.min(Ss.min(Nat.add(1n, SlashSuggest.sp_lev(t, SCon{x, u})), Nat.add(1n, _)), Nat.add(Ss.head(ssb.srow(t, u)), Ss.ne(c, x))) <> ssb.srow(SCon{c, t}, u) == ssb.srow(SCon{c, t}, SCon{x, u}) : List<&2, Nat>}
  %Equal.sym(Nat, Ss.head(ssb.srow(t, u)), SlashSuggest.sp_lev(t, u), ssb.head(t, u)) : {Ss.min(Ss.min(Nat.add(1n, SlashSuggest.sp_lev(t, SCon{x, u})), Nat.add(1n, SlashSuggest.sp_lev(SCon{c, t}, u))), Nat.add(_, Ss.ne(c, x))) <> ssb.srow(SCon{c, t}, u) == ssb.srow(SCon{c, t}, SCon{x, u}) : List<&2, Nat>}
  %Equal.sym(Nat, Ss.ne(c, x), SlashSuggest.sp_cost(Char.is_eq(c, x)), ssb.ne(c, x)) : {Ss.min(Ss.min(Nat.add(1n, SlashSuggest.sp_lev(t, SCon{x, u})), Nat.add(1n, SlashSuggest.sp_lev(SCon{c, t}, u))), Nat.add(SlashSuggest.sp_lev(t, u), _)) <> ssb.srow(SCon{c, t}, u) == ssb.srow(SCon{c, t}, SCon{x, u}) : List<&2, Nat>}
  %Equal.sym(Nat, Ss.min(Nat.add(1n, SlashSuggest.sp_lev(t, SCon{x, u})), Nat.add(1n, SlashSuggest.sp_lev(SCon{c, t}, u))), SlashSuggest.sp_min(Nat.add(1n, SlashSuggest.sp_lev(t, SCon{x, u})), Nat.add(1n, SlashSuggest.sp_lev(SCon{c, t}, u))), ssb.min(Nat.add(1n, SlashSuggest.sp_lev(t, SCon{x, u})), Nat.add(1n, SlashSuggest.sp_lev(SCon{c, t}, u)))) : {Ss.min(_, Nat.add(SlashSuggest.sp_lev(t, u), SlashSuggest.sp_cost(Char.is_eq(c, x)))) <> ssb.srow(SCon{c, t}, u) == ssb.srow(SCon{c, t}, SCon{x, u}) : List<&2, Nat>}
  %Equal.sym(Nat, Ss.min(SlashSuggest.sp_min(Nat.add(1n, SlashSuggest.sp_lev(t, SCon{x, u})), Nat.add(1n, SlashSuggest.sp_lev(SCon{c, t}, u))), Nat.add(SlashSuggest.sp_lev(t, u), SlashSuggest.sp_cost(Char.is_eq(c, x)))), SlashSuggest.sp_min(SlashSuggest.sp_min(Nat.add(1n, SlashSuggest.sp_lev(t, SCon{x, u})), Nat.add(1n, SlashSuggest.sp_lev(SCon{c, t}, u))), Nat.add(SlashSuggest.sp_lev(t, u), SlashSuggest.sp_cost(Char.is_eq(c, x)))), ssb.min(SlashSuggest.sp_min(Nat.add(1n, SlashSuggest.sp_lev(t, SCon{x, u})), Nat.add(1n, SlashSuggest.sp_lev(SCon{c, t}, u))), Nat.add(SlashSuggest.sp_lev(t, u), SlashSuggest.sp_cost(Char.is_eq(c, x))))) : {_ <> ssb.srow(SCon{c, t}, u) == ssb.srow(SCon{c, t}, SCon{x, u}) : List<&2, Nat>}
  {==}

# the code's step makes the row of c before t from the row of t
def ssb.step(+c: Char, +t: String, b: String) -> {Ss.step(c, b, ssb.srow(t, b)) == ssb.srow(SCon{c, t}, b) : List<&2, Nat>}:
  match b:
    case SNil{}:
      %Equal.sym(Nat, SlashSuggest.sp_lev(t, SNil{}), String.length(t), ssb.empty(t)) : {[Nat.add(1n, _)] == ssb.srow(SCon{c, t}, SNil{}) : List<&2, Nat>}
      {==}
    case SCon{+x, +u}:
      ssb.cell(c, t, x, u, Ss.step(c, u, ssb.srow(t, u)), ssb.step(c, t, u))

# the code's row is the spec's
def ssb.row(a: String, +b: String) -> {Ss.row(a, b) == ssb.srow(a, b) : List<&2, Nat>}:
  match a:
    case SNil{}:
      ssb.lens(b)
    case SCon{+c, +t}:
      %Equal.sym(List<&2, Nat>, Ss.row(t, b), ssb.srow(t, b), ssb.row(t, b)) : {Ss.step(c, b, _) == ssb.srow(SCon{c, t}, b) : List<&2, Nat>}
      ssb.step(c, t, b)

# the code's distance is the spec's
def ssb.dist(+a: String, +b: String) -> {Ss.dist(a, b) == SlashSuggest.sp_lev(a, b) : Nat}:
  %Equal.sym(List<&2, Nat>, Ss.row(a, b), ssb.srow(a, b), ssb.row(a, b)) : {Ss.head(_) == SlashSuggest.sp_lev(a, b) : Nat}
  ssb.head(a, b)

# Nat comparisons
# ---------------

def ssb.eq_refl(a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      ssb.eq_refl(p)

# b < a: a is not at most b
def ssb.lt_nle(a: Nat, b: Nat, h: {Nat.is_lt(b, a) == True{} : Bool}) -> {Nat.is_le(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      LStg.stg.absurdF({Nat.is_le(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      LStg.stg.absurdF({Nat.is_le(0n, 1n+q) == False{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ssb.lt_nle(p, q, h)

# b < a: a is not b
def ssb.lt_ne(a: Nat, b: Nat, h: {Nat.is_lt(b, a) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      LStg.stg.absurdF({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ssb.lt_ne(p, q, h)

# b is not below a: a is at most b
def ssb.nlt_le(a: Nat, b: Nat, h: {Nat.is_lt(b, a) == False{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LStg.stg.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      ssb.nlt_le(p, q, h)

# e <= 2 <= q: e <= q
def ssb.trans2(e: Nat, q: Nat, h1: {Nat.is_le(e, 2n) == True{} : Bool}, h2: {Nat.is_le(2n, q) == True{} : Bool}) -> {Nat.is_le(e, q) == True{} : Bool}:
  match e q:
    case 0n 0n:
      {==}
    case 0n 1n+r:
      {==}
    case 1n 0n:
      LStg.stg.absurdF({Nat.is_le(1n, 0n) == True{} : Bool}, h2)
    case 1n 1n:
      LStg.stg.absurdF({Nat.is_le(1n, 1n) == True{} : Bool}, h2)
    case 1n 2n+r:
      {==}
    case 2n r:
      h2
    case 3n+p r:
      LStg.stg.absurdF({Nat.is_le(3n+p, r) == True{} : Bool}, h1)

# q < 2 < e: e is not at most q
def ssb.over2(q: Nat, e: Nat, h1: {Nat.is_le(e, 2n) == False{} : Bool}, h2: {Nat.is_le(2n, q) == False{} : Bool}) -> {False{} == Nat.is_le(e, q) : Bool}:
  match q e:
    case 0n 0n:
      LStg.stg.absurd({False{} == Nat.is_le(0n, 0n) : Bool}, h1)
    case 0n 1n+p:
      {==}
    case 1n 0n:
      LStg.stg.absurd({False{} == Nat.is_le(0n, 1n) : Bool}, h1)
    case 1n 1n:
      LStg.stg.absurd({False{} == Nat.is_le(1n, 1n) : Bool}, h1)
    case 1n 2n:
      LStg.stg.absurd({False{} == Nat.is_le(2n, 1n) : Bool}, h1)
    case 1n 3n+p:
      {==}
    case 2n f:
      LStg.stg.absurd({False{} == Nat.is_le(f, 2n) : Bool}, h2)
    case 3n+r f:
      LStg.stg.absurd({False{} == Nat.is_le(f, 3n+r) : Bool}, h2)

# The limit
# ---------

def ssb.or_f(x: Bool) -> {x == Bool.or(x, False{}) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def ssb.ok.both(+e: Nat, +q: Nat, d: Bool, ed: {Nat.is_le(e, 2n) == d : Bool}, h2: {Nat.is_le(2n, q) == True{} : Bool}) -> {Nat.is_le(e, q) == Bool.or(d, Nat.is_le(e, q)) : Bool}:
  match d:
    case True{}:
      ssb.trans2(e, q, ed, h2)
    case False{}:
      {==}

def ssb.ok.two(+e: Nat, +q: Nat, d: Bool, ed: {Nat.is_le(e, 2n) == d : Bool}, h2: {Nat.is_le(2n, q) == False{} : Bool}) -> {d == Bool.or(d, Nat.is_le(e, q)) : Bool}:
  match d:
    case True{}:
      {==}
    case False{}:
      ssb.over2(q, e, ed, h2)

def ssb.ok.big(+e: Nat, +q: Nat, c: Bool, ec: {Nat.is_le(2n, q) == c : Bool}) -> {Nat.is_le(e, Ss.min.of(c, q, 2n)) == Bool.or(Nat.is_le(e, 2n), Nat.is_le(e, q)) : Bool}:
  match c:
    case True{}:
      ssb.ok.both(e, q, Nat.is_le(e, 2n), {==}, ec)
    case False{}:
      ssb.ok.two(e, q, Nat.is_le(e, 2n), {==}, ec)

def ssb.ok.at(s: Bool, +e: Nat, +q: Nat) -> {Nat.is_le(e, Ss.limit.of(s, q)) == Bool.or(Bool.and(s, Nat.is_le(e, 1n)), Bool.and(Bool.not(s), Bool.or(Nat.is_le(e, 2n), Nat.is_le(e, q)))) : Bool}:
  match s:
    case True{}:
      ssb.or_f(Nat.is_le(e, 1n))
    case False{}:
      ssb.ok.big(e, q, Nat.is_le(2n, q), {==})

# R3: e edits are within the code's limit exactly when the laws' sp_ok says so
def ssb.ok(+e: Nat, +n: Nat) -> {Nat.is_le(e, Ss.limit(n)) == SlashSuggest.sp_ok(e, n) : Bool}:
  ssb.ok.at(Nat.is_le(n, 3n), e, Nat.div(n, 3n))

# the code's fit test of names is the doc_commit spec's
def ssb.fits(xs: List<&2, String>) -> {SlashSuggest.sp_fit_strs(xs) == DocCommit.sp_fit_strs(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %ssb.fits(t) : {Bool.and(LawsBase.wire_fits(String.length(x)), SlashSuggest.sp_fit_strs(t)) == Bool.and(LawsBase.wire_fits(String.length(x)), _) : Bool}
      {==}
