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

# Choices
# -------

def ssb.keep(b: Bool, +d: Nat, j: Nat, e: Nat) -> {Ss.near.keep(b, d, Ss.Near{j, e}) == SlashSuggest.sp_first.won(b, j, e, d) : Ss.Near}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ssb.near(+d: Nat, m: Maybe<&2, Ss.Near>) -> {Ss.near.of(d, m) == SlashSuggest.sp_first.of(d, m) : Ss.Near}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      match n:
        case Ss.Near{j, +e}:
          ssb.keep(Nat.is_lt(e, d), d, j, e)

# the code's nearest candidate is the spec's
def ssb.nearest(+w: String, cs: List<&2, String>) -> {Ss.nearest(w, cs) == SlashSuggest.sp_first(w, cs) : Maybe<&2, Ss.Near>}:
  match cs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(Maybe<&2, Ss.Near>, Ss.nearest(w, t), SlashSuggest.sp_first(w, t), ssb.nearest(w, t)) : {Some{Ss.near.of(Ss.dist(w, x), _)} == Some{SlashSuggest.sp_first.of(SlashSuggest.sp_lev(w, x), SlashSuggest.sp_first(w, t))} : Maybe<&2, Ss.Near>}
      %Equal.sym(Nat, Ss.dist(w, x), SlashSuggest.sp_lev(w, x), ssb.dist(w, x)) : {Some{Ss.near.of(_, SlashSuggest.sp_first(w, t))} == Some{SlashSuggest.sp_first.of(SlashSuggest.sp_lev(w, x), SlashSuggest.sp_first(w, t))} : Maybe<&2, Ss.Near>}
      %Equal.sym(Ss.Near, Ss.near.of(SlashSuggest.sp_lev(w, x), SlashSuggest.sp_first(w, t)), SlashSuggest.sp_first.of(SlashSuggest.sp_lev(w, x), SlashSuggest.sp_first(w, t)), ssb.near(SlashSuggest.sp_lev(w, x), SlashSuggest.sp_first(w, t))) : {Some{_} == Some{SlashSuggest.sp_first.of(SlashSuggest.sp_lev(w, x), SlashSuggest.sp_first(w, t))} : Maybe<&2, Ss.Near>}
      {==}

def ssb.utf8.at(a: Bool, b: Bool, c: Bool) -> {Sl.utf8.code(a, b, c) == SlashSuggest.sp_pick(a, 1n, SlashSuggest.sp_pick(b, 2n, SlashSuggest.sp_pick(c, 3n, 4n))) : Nat}:
  match a b c:
    case True{} _ _:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def ssb.utf8(c: Char) -> {Sl.utf8(c) == SlashSuggest.sp_utf8(c) : Nat}:
  match c:
    case Chr{+x}:
      ssb.utf8.at(U32.is_lt(x, 128), U32.is_lt(x, 2048), U32.is_lt(x, 65536))

def ssb.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.add(p, 0n), p, ssb.add_zero(p)) : {1n+_ == 1n+p : Nat}
      {==}

def ssb.add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.add(p, 1n+b), 1n+Nat.add(p, b), ssb.add_succ(p, b)) : {1n+_ == 1n+1n+Nat.add(p, b) : Nat}
      {==}

# b + (u + n) == (u + b) + n
def ssb.swap(b: Nat, +u: Nat, +n: Nat) -> {Nat.add(b, Nat.add(u, n)) == Nat.add(Nat.add(u, b), n) : Nat}:
  match b:
    case 0n:
      %Equal.sym(Nat, Nat.add(u, 0n), u, ssb.add_zero(u)) : {Nat.add(u, n) == Nat.add(_, n) : Nat}
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.add(u, 1n+p), 1n+Nat.add(u, p), ssb.add_succ(u, p)) : {1n+Nat.add(p, Nat.add(u, n)) == Nat.add(_, n) : Nat}
      %Equal.sym(Nat, Nat.add(p, Nat.add(u, n)), Nat.add(Nat.add(u, p), n), ssb.swap(p, u, n)) : {1n+_ == 1n+Nat.add(Nat.add(u, p), n) : Nat}
      {==}

# the code's byte count after n is n plus the spec's
def ssb.bytes(s: String, +n: Nat) -> {Sl.bytes(s, n) == Nat.add(SlashSuggest.sp_bytes(s), n) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Nat, Sl.bytes(t, Nat.add(Sl.utf8(c), n)), Nat.add(SlashSuggest.sp_bytes(t), Nat.add(Sl.utf8(c), n)), ssb.bytes(t, Nat.add(Sl.utf8(c), n))) : {_ == Nat.add(Nat.add(SlashSuggest.sp_utf8(c), SlashSuggest.sp_bytes(t)), n) : Nat}
      %Equal.sym(Nat, Sl.utf8(c), SlashSuggest.sp_utf8(c), ssb.utf8(c)) : {Nat.add(SlashSuggest.sp_bytes(t), Nat.add(_, n)) == Nat.add(Nat.add(SlashSuggest.sp_utf8(c), SlashSuggest.sp_bytes(t)), n) : Nat}
      ssb.swap(SlashSuggest.sp_bytes(t), SlashSuggest.sp_utf8(c), n)

def ssb.limit.inner(b: Bool, +q: Nat) -> {Ss.min.of(b, q, 2n) == SlashSuggest.sp_pick(b, q, 2n) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ssb.limit.at(s: Bool, +q: Nat) -> {Ss.limit.of(s, q) == SlashSuggest.sp_pick(s, 1n, SlashSuggest.sp_pick(Nat.is_le(2n, q), q, 2n)) : Nat}:
  match s:
    case True{}:
      {==}
    case False{}:
      ssb.limit.inner(Nat.is_le(2n, q), q)

# the code's limit is the spec's
def ssb.limit(+n: Nat) -> {Ss.limit(n) == SlashSuggest.sp_limit(n) : Nat}:
  ssb.limit.at(Nat.is_le(n, 3n), Nat.div(n, 3n))

# the code's fit test of names is the doc_commit spec's
def ssb.fits(xs: List<&2, String>) -> {SlashSuggest.sp_fit_strs(xs) == DocCommit.sp_fit_strs(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %ssb.fits(t) : {Bool.and(LawsBase.wire_fits(String.length(x)), SlashSuggest.sp_fit_strs(t)) == Bool.and(LawsBase.wire_fits(String.length(x)), _) : Bool}
      {==}
