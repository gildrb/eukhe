# eukhe: lemmas about the text helpers of bend/staging.bend (`same`,
# `has_name`, `unsuffix`) and their specs (laws/base.bend, section staging
# and listing), shared by proof/staging/ and proof/listing/

import Base
import ../../bend/staging.bend as Sg
import ../../laws/base.bend as LawsBase
import ../wire/wire_bool_exact.bend as PWireBoolExact

# Logic
# -----

def stg.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

# True is not False
def stg.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : stg.BD(_, Unit, A)
  Unit{}

def stg.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  stg.absurd(A, Equal.sym(Bool, False{}, True{}, e))

def stg.and_false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def stg.or_false(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def stg.and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def stg.and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      stg.absurdF({b == True{} : Bool}, e)

def stg.and_true(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# a Bool and its value
def stg.which(b: Bool) -> (&v: Bool -> {b == v : Bool}):
  match b:
    case True{}:
      (True{}, {==})
    case False{}:
      (False{}, {==})

# Chars
# -----

def stg.bool_cmp_refl(b: Bool) -> {Bool.cmp(b, b) == EQ{} : Cmp}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def stg.word_cmp_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, stg.word_cmp_refl(p, t)) : {Word.cmp.fin(b, b, _) == EQ{} : Cmp}
          stg.bool_cmp_refl(b)

# a char is the char it is
def stg.char_refl(c: Char) -> {Char.is_eq(c, c) == True{} : Bool}:
  match c:
    case Chr{x}:
      match x:
        case U32{+w}:
          %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, stg.word_cmp_refl(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
          {==}

# Char.is_eq is equality
def stg.char_sound(+c: Char, +d: Char, e: {Char.is_eq(c, d) == True{} : Bool}) -> {c == d : Char}:
  match c d:
    case Chr{+x} Chr{+y}:
      Equal.cong(U32, Char, u => Chr{u}, x, y, PWireBoolExact.wr_eq_sound(x, y, e))

# Texts: the code is its spec
# ---------------------------

def stg.same(a: String, b: String) -> {Sg.same(a, b) == LawsBase.text_same(a, b) : Bool}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, v}:
      {==}
    case SCon{x, u} SNil{}:
      {==}
    case SCon{+x, u} SCon{+y, v}:
      %stg.same(u, v) : {Bool.and(Char.is_eq(x, y), Sg.same(u, v)) == Bool.and(Char.is_eq(x, y), _) : Bool}
      {==}

def stg.named(+s: String, n: Sg.Name) -> {Sg.named(s, n) == LawsBase.text_named(s, n) : Bool}:
  match n:
    case Sg.Utf{t}:
      stg.same(t, s)
    case Sg.Raw{}:
      {==}

def stg.has_name(+s: String, es: List<&2, Sg.Seen>) -> {Sg.has_name(s, es) == LawsBase.text_has_name(s, es) : Bool}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case Sg.Seen{+n, k}:
          %stg.named(s, n) : {Bool.or(Sg.named(s, n), Sg.has_name(s, rest)) == Bool.or(_, LawsBase.text_has_name(s, rest)) : Bool}
          %stg.has_name(s, rest) : {Bool.or(Sg.named(s, n), Sg.has_name(s, rest)) == Bool.or(Sg.named(s, n), _) : Bool}
          {==}

def stg.here(b: Bool, m: Maybe<&2, String>) -> {Sg.unsuffix.here(b, m) == LawsBase.text_found(b, m) : Maybe<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def stg.cons(c: Char, m: Maybe<&2, String>) -> {Sg.unsuffix.cons(c, m) == LawsBase.text_cons(c, m) : Maybe<&2, String>}:
  match m:
    case None{}:
      {==}
    case Some{r}:
      {==}

def stg.unsuffix(+p: String, +s: String) -> {Sg.unsuffix(p, s) == LawsBase.text_unsuffix(p, s) : Maybe<&2, String>}:
  match s:
    case SNil{}:
      stg.here(String.is_empty(p), None{})
    case SCon{+c, +t}:
      +m = LawsBase.text_cons(c, LawsBase.text_unsuffix(p, t))
      %stg.same(SCon{c, t}, p) : {Sg.unsuffix.here(Sg.same(SCon{c, t}, p), Sg.unsuffix.cons(c, Sg.unsuffix(p, t))) == LawsBase.text_found(_, m) : Maybe<&2, String>}
      %stg.unsuffix(p, t) : {Sg.unsuffix.here(Sg.same(SCon{c, t}, p), Sg.unsuffix.cons(c, Sg.unsuffix(p, t))) == LawsBase.text_found(Sg.same(SCon{c, t}, p), LawsBase.text_cons(c, _)) : Maybe<&2, String>}
      %stg.cons(c, Sg.unsuffix(p, t)) : {Sg.unsuffix.here(Sg.same(SCon{c, t}, p), Sg.unsuffix.cons(c, Sg.unsuffix(p, t))) == LawsBase.text_found(Sg.same(SCon{c, t}, p), _) : Maybe<&2, String>}
      stg.here(Sg.same(SCon{c, t}, p), Sg.unsuffix.cons(c, Sg.unsuffix(p, t)))

# Texts: what the specs say
# -------------------------

# text_same is equality
def stg.same_eq(+a: String, +b: String, +e: {LawsBase.text_same(a, b) == True{} : Bool}) -> {a == b : String}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, v}:
      stg.absurdF({SNil{} == SCon{y, v} : String}, e)
    case SCon{x, u} SNil{}:
      stg.absurdF({SCon{x, u} == SNil{} : String}, e)
    case SCon{+x, +u} SCon{+y, +v}:
      +ex = stg.char_sound(x, y, stg.and_l(Char.is_eq(x, y), LawsBase.text_same(u, v), e))
      +eu = stg.same_eq(u, v, stg.and_r(Char.is_eq(x, y), LawsBase.text_same(u, v), e))
      %ex : {SCon{x, u} == SCon{_, v} : String}
      %eu : {SCon{x, u} == SCon{x, _} : String}
      {==}

# a text is the same as itself
def stg.same_refl(a: String) -> {LawsBase.text_same(a, a) == True{} : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{+x, +u}:
      %Equal.sym(Bool, Char.is_eq(x, x), True{}, stg.char_refl(x)) : {Bool.and(_, LawsBase.text_same(u, u)) == True{} : Bool}
      stg.same_refl(u)

# texts of other lengths are not the same
def stg.same_len(a: String, b: String, e: {Nat.is_eq(String.length(a), String.length(b)) == False{} : Bool}) -> {LawsBase.text_same(a, b) == False{} : Bool}:
  match a b:
    case SNil{} SNil{}:
      stg.absurd({LawsBase.text_same(SNil{}, SNil{}) == False{} : Bool}, e)
    case SNil{} SCon{y, v}:
      {==}
    case SCon{x, u} SNil{}:
      {==}
    case SCon{+x, u} SCon{y, v}:
      %Equal.sym(Bool, LawsBase.text_same(u, v), False{}, stg.same_len(u, v, e)) : {Bool.and(Char.is_eq(x, y), _) == False{} : Bool}
      stg.and_false(Char.is_eq(x, y))

def stg.add_succ_r(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %stg.add_succ_r(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

# n + k + 1 is not n
def stg.ne_grow(+k: Nat, n: Nat) -> {Nat.is_eq(1n+Nat.add(k, n), n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      %Equal.sym(Nat, Nat.add(k, 1n+m), 1n+Nat.add(k, m), stg.add_succ_r(k, m)) : {Nat.is_eq(1n+_, 1n+m) == False{} : Bool}
      stg.ne_grow(k, m)

def stg.len_app(a: String, +b: String) -> {String.length(String.append(a, b)) == Nat.add(String.length(a), String.length(b)) : Nat}:
  match a:
    case SNil{}:
      {==}
    case SCon{x, u}:
      %stg.len_app(u, b) : {1n+String.length(String.append(u, b)) == 1n+_ : Nat}
      {==}

# p ends with itself: nothing is before it
def stg.unsuffix_self(+p: String) -> {LawsBase.text_unsuffix(p, p) == Some{SNil{}} : Maybe<&2, String>}:
  match p:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, LawsBase.text_same(SCon{c, t}, SCon{c, t}), True{}, stg.same_refl(SCon{c, t})) : {LawsBase.text_found(_, LawsBase.text_cons(c, LawsBase.text_unsuffix(SCon{c, t}, t))) == Some{SNil{}} : Maybe<&2, String>}
      {==}

# s, then p, ends with p, and s is before it
def stg.unsuffix_app(+s: String, +p: String) -> {LawsBase.text_unsuffix(p, String.append(s, p)) == Some{s} : Maybe<&2, String>}:
  match s:
    case SNil{}:
      stg.unsuffix_self(p)
    case SCon{+c, +t}:
      +a = String.append(t, p)
      +lp = String.length(p)
      +el = Equal.trans(Bool, Nat.is_eq(1n+String.length(a), lp), Nat.is_eq(1n+Nat.add(String.length(t), lp), lp), False{},
        Equal.cong(Nat, Bool, z => Nat.is_eq(1n+z, lp), String.length(a), Nat.add(String.length(t), lp), stg.len_app(t, p)),
        stg.ne_grow(String.length(t), lp))
      %Equal.sym(Bool, LawsBase.text_same(SCon{c, a}, p), False{}, stg.same_len(SCon{c, a}, p, el)) : {LawsBase.text_found(_, LawsBase.text_cons(c, LawsBase.text_unsuffix(p, a))) == Some{SCon{c, t}} : Maybe<&2, String>}
      %Equal.sym(Maybe<&2, String>, LawsBase.text_unsuffix(p, a), Some{t}, stg.unsuffix_app(t, p)) : {LawsBase.text_found(False{}, LawsBase.text_cons(c, _)) == Some{SCon{c, t}} : Maybe<&2, String>}
      {==}
