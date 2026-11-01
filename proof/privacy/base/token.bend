# eukhe: lemmas shared by the proofs of area privacy, section token: the
# logic of Bool, Nat and Maybe they use, the facts of the map (a value's
# index is found where it was put, later values never move an index), and
# a text scrubbed or restored one piece at a time

import Base
import ../../../bend/privacy/token.bend as Tk
import ../../../spec/harness/privacy.bend as S
import ../../base/staging.bend as LStaging
import ../../wire/wire_nat_exact.bend as PWireNatExact

# Logic
# -----

def ptk.IfF(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

def ptk.IfT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# a premise False == True proves anything
def ptk.absurd_ft(-G: Type, +e: {False{} == True{} : Bool}) -> G:
  %e : ptk.IfF(_, G)
  Unit{}

# a premise True == False proves anything
def ptk.absurd_tf(-G: Type, +e: {True{} == False{} : Bool}) -> G:
  %e : ptk.IfT(_, G)
  Unit{}

def ptk.IfSome(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# a premise None == Some proves anything
def ptk.none_some(-A: Data, -b: A, -G: Type, +e: {None{} == Some{b} : Maybe<&2, A>}) -> G:
  %e : ptk.IfSome(A, _, G)
  Unit{}

def ptk.some_val(-A: Data, d: A, m: Maybe<&2, A>) -> A:
  match m:
    case None{}:
      d
    case Some{x}:
      x

# Some is injective
def ptk.some_inj(-A: Data, +a: A, +b: A, +e: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  Equal.cong(Maybe<&2, A>, A, m => ptk.some_val(A, a, m), Some{a}, Some{b}, e)

def ptk.and_l(a: Bool, -b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      ptk.absurd_ft({False{} == True{} : Bool}, h)

def ptk.and_r(a: Bool, -b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      ptk.absurd_ft({b == True{} : Bool}, h)

def ptk.and_false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Nat
# ---

def ptk.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ptk.le_refl(p)

def ptk.eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ptk.eq_refl(p)

def ptk.eq_sound(a: Nat, b: Nat, +h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      ptk.absurd_ft({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      ptk.absurd_ft({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, ptk.eq_sound(p, q, h))

# i <= n, so i <= n + 1
def ptk.le_succ(i: Nat, n: Nat, +h: {Nat.is_le(i, n) == True{} : Bool}) -> {Nat.is_le(i, 1n+n) == True{} : Bool}:
  match i n:
    case 0n _:
      {==}
    case 1n+p 0n:
      ptk.absurd_ft({Nat.is_le(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      ptk.le_succ(p, q, h)

# i <= n, so i <= b + n
def ptk.le_add(b: Nat, +i: Nat, +n: Nat, +h: {Nat.is_le(i, n) == True{} : Bool}) -> {Nat.is_le(i, Nat.add(b, n)) == True{} : Bool}:
  match b:
    case 0n:
      h
    case 1n++p:
      ptk.le_succ(i, Nat.add(p, n), ptk.le_add(p, i, n, h))

# i <= n, so i is not n + 1
def ptk.le_ne(i: Nat, n: Nat, +h: {Nat.is_le(i, n) == True{} : Bool}) -> {Nat.is_eq(i, 1n+n) == False{} : Bool}:
  match i n:
    case 0n _:
      {==}
    case 1n+p 0n:
      ptk.absurd_ft({Nat.is_eq(1n+p, 1n) == False{} : Bool}, h)
    case 1n+p 1n+q:
      ptk.le_ne(p, q, h)

# Classes and texts
# -----------------

def ptk.cls_refl(c: Tk.Class) -> {Tk.Class.eq(c, c) == True{} : Bool}:
  match c:
    case Tk.Person{}:
      {==}
    case Tk.Email{}:
      {==}
    case Tk.Phone{}:
      {==}
    case Tk.Ip{}:
      {==}
    case Tk.Id{}:
      {==}
    case Tk.ApiKey{}:
      {==}
    case Tk.Card{}:
      {==}
    case Tk.Iban{}:
      {==}

def ptk.cls_of_tag(c: Tk.Class) -> {Tk.Class.of(Tk.Class.tag(c)) == Some{c} : Maybe<&2, Tk.Class>}:
  match c:
    case Tk.Person{}:
      {==}
    case Tk.Email{}:
      {==}
    case Tk.Phone{}:
      {==}
    case Tk.Ip{}:
      {==}
    case Tk.Id{}:
      {==}
    case Tk.ApiKey{}:
      {==}
    case Tk.Card{}:
      {==}
    case Tk.Iban{}:
      {==}

# Class.eq is equality
def ptk.cls_sound(+c: Tk.Class, +d: Tk.Class, +h: {Tk.Class.eq(c, d) == True{} : Bool}) -> {c == d : Tk.Class}:
  +ec = Equal.cong(Nat, Maybe<&2, Tk.Class>, n => Tk.Class.of(n), Tk.Class.tag(c), Tk.Class.tag(d), ptk.eq_sound(Tk.Class.tag(c), Tk.Class.tag(d), h))
  +e1 = Equal.trans(Maybe<&2, Tk.Class>, Some{c}, Tk.Class.of(Tk.Class.tag(c)), Tk.Class.of(Tk.Class.tag(d)), Equal.sym(Maybe<&2, Tk.Class>, Tk.Class.of(Tk.Class.tag(c)), Some{c}, ptk.cls_of_tag(c)), ec)
  ptk.some_inj(Tk.Class, c, d, Equal.trans(Maybe<&2, Tk.Class>, Some{c}, Tk.Class.of(Tk.Class.tag(d)), Some{d}, e1, ptk.cls_of_tag(d)))

def ptk.same_refl(a: String) -> {Tk.same(a, a) == True{} : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{+x, t}:
      %Equal.sym(Bool, Char.is_eq(x, x), True{}, LStaging.stg.char_refl(x)) : {Bool.and(_, Tk.same(t, t)) == True{} : Bool}
      ptk.same_refl(t)

# same is equality
def ptk.same_sound(+a: String, +b: String, +h: {Tk.same(a, b) == True{} : Bool}) -> {a == b : String}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, bt}:
      ptk.absurd_ft({SNil{} == SCon{y, bt} : String}, h)
    case SCon{x, at} SNil{}:
      ptk.absurd_ft({SCon{x, at} == SNil{} : String}, h)
    case SCon{+x, +at} SCon{+y, +bt}:
      +ex = LStaging.stg.char_sound(x, y, ptk.and_l(Char.is_eq(x, y), Tk.same(at, bt), h))
      +et = ptk.same_sound(at, bt, ptk.and_r(Char.is_eq(x, y), Tk.same(at, bt), h))
      %ex : {SCon{x, at} == SCon{_, bt} : String}
      %et : {SCon{x, at} == SCon{x, _} : String}
      {==}

# The map
# -------

def ptk.find_le.at(b: Bool, +c: Tk.Class, +d: Tk.Class, +v: String, +w: String, +rest: List<&2, Tk.Ent>, +i: Nat,
  +eb: {Bool.and(Tk.Class.eq(c, d), Tk.same(v, w)) == b : Bool},
  +h: {Tk.find.at(b, rest, c, Tk.find(rest, c, v)) == Some{i} : Maybe<&2, Nat>},
  ih: {Tk.find(rest, c, v) == Some{i} : Maybe<&2, Nat>} -> {Nat.is_le(i, Tk.count(rest, c)) == True{} : Bool}) ->
  {Nat.is_le(i, Nat.add(Tk.bit(Tk.Class.eq(c, d)), Tk.count(rest, c))) == True{} : Bool}:
  match b:
    case True{}:
      +ec = ptk.and_l(Tk.Class.eq(c, d), Tk.same(v, w), eb)
      +ei = ptk.some_inj(Nat, 1n+Tk.count(rest, c), i, h)
      %Equal.sym(Bool, Tk.Class.eq(c, d), True{}, ec) : {Nat.is_le(i, Nat.add(Tk.bit(_), Tk.count(rest, c))) == True{} : Bool}
      %ei : {Nat.is_le(_, 1n+Tk.count(rest, c)) == True{} : Bool}
      ptk.le_refl(1n+Tk.count(rest, c))
    case False{}:
      ptk.le_add(Tk.bit(Tk.Class.eq(c, d)), i, Tk.count(rest, c), ih(h))

# a value's index is at most the count of its class
def ptk.find_le(es: List<&2, Tk.Ent>, +c: Tk.Class, +v: String, +i: Nat, +h: {Tk.find(es, c, v) == Some{i} : Maybe<&2, Nat>}) -> {Nat.is_le(i, Tk.count(es, c)) == True{} : Bool}:
  match es:
    case Nil{}:
      ptk.none_some(Nat, i, {Nat.is_le(i, 0n) == True{} : Bool}, h)
    case e <> +rest:
      match e:
        case Tk.Ent{+d, +w}:
          ptk.find_le.at(Bool.and(Tk.Class.eq(c, d), Tk.same(v, w)), c, d, v, w, rest, i, {==}, h, h2 => ptk.find_le(rest, c, v, i, h2))

def ptk.value_le.at(b: Bool, +c: Tk.Class, +d: Tk.Class, +w: String, +rest: List<&2, Tk.Ent>, +i: Nat, +v: String,
  +eb: {Bool.and(Tk.Class.eq(c, d), Nat.is_eq(i, 1n+Tk.count(rest, c))) == b : Bool},
  +h: {Tk.value.at(b, w, Tk.value(rest, c, i)) == Some{v} : Maybe<&2, String>},
  ih: {Tk.value(rest, c, i) == Some{v} : Maybe<&2, String>} -> {Nat.is_le(i, Tk.count(rest, c)) == True{} : Bool}) ->
  {Nat.is_le(i, Nat.add(Tk.bit(Tk.Class.eq(c, d)), Tk.count(rest, c))) == True{} : Bool}:
  match b:
    case True{}:
      +ec = ptk.and_l(Tk.Class.eq(c, d), Nat.is_eq(i, 1n+Tk.count(rest, c)), eb)
      +ei = ptk.eq_sound(i, 1n+Tk.count(rest, c), ptk.and_r(Tk.Class.eq(c, d), Nat.is_eq(i, 1n+Tk.count(rest, c)), eb))
      %Equal.sym(Bool, Tk.Class.eq(c, d), True{}, ec) : {Nat.is_le(i, Nat.add(Tk.bit(_), Tk.count(rest, c))) == True{} : Bool}
      %Equal.sym(Nat, i, 1n+Tk.count(rest, c), ei) : {Nat.is_le(_, 1n+Tk.count(rest, c)) == True{} : Bool}
      ptk.le_refl(1n+Tk.count(rest, c))
    case False{}:
      ptk.le_add(Tk.bit(Tk.Class.eq(c, d)), i, Tk.count(rest, c), ih(h))

# an index the map holds is at most the count of its class
def ptk.value_le(es: List<&2, Tk.Ent>, +c: Tk.Class, +i: Nat, +v: String, +h: {Tk.value(es, c, i) == Some{v} : Maybe<&2, String>}) -> {Nat.is_le(i, Tk.count(es, c)) == True{} : Bool}:
  match es:
    case Nil{}:
      ptk.none_some(String, v, {Nat.is_le(i, 0n) == True{} : Bool}, h)
    case e <> +rest:
      match e:
        case Tk.Ent{+d, +w}:
          ptk.value_le.at(Bool.and(Tk.Class.eq(c, d), Nat.is_eq(i, 1n+Tk.count(rest, c))), c, d, w, rest, i, v, {==}, h, h2 => ptk.value_le(rest, c, i, v, h2))

# a value the map does not hold is found at the head it is put at
def ptk.find_head(+es: List<&2, Tk.Ent>, +c: Tk.Class, +v: String) -> {Tk.find(Tk.Ent{c, v} <> es, c, v) == Some{1n+Tk.count(es, c)} : Maybe<&2, Nat>}:
  %Equal.sym(Bool, Tk.Class.eq(c, c), True{}, ptk.cls_refl(c)) : {Tk.find.at(Bool.and(_, Tk.same(v, v)), es, c, Tk.find(es, c, v)) == Some{1n+Tk.count(es, c)} : Maybe<&2, Nat>}
  %Equal.sym(Bool, Tk.same(v, v), True{}, ptk.same_refl(v)) : {Tk.find.at(Bool.and(True{}, _), es, c, Tk.find(es, c, v)) == Some{1n+Tk.count(es, c)} : Maybe<&2, Nat>}
  {==}

# a value put at the head is the value of its index
def ptk.value_head(+es: List<&2, Tk.Ent>, +c: Tk.Class, +v: String) -> {Tk.value(Tk.Ent{c, v} <> es, c, 1n+Tk.count(es, c)) == Some{v} : Maybe<&2, String>}:
  %Equal.sym(Bool, Tk.Class.eq(c, c), True{}, ptk.cls_refl(c)) : {Tk.value.at(Bool.and(_, Nat.is_eq(1n+Tk.count(es, c), 1n+Tk.count(es, c))), v, Tk.value(es, c, 1n+Tk.count(es, c))) == Some{v} : Maybe<&2, String>}
  %Equal.sym(Bool, Nat.is_eq(1n+Tk.count(es, c), 1n+Tk.count(es, c)), True{}, ptk.eq_refl(1n+Tk.count(es, c))) : {Tk.value.at(Bool.and(True{}, _), v, Tk.value(es, c, 1n+Tk.count(es, c))) == Some{v} : Maybe<&2, String>}
  {==}

def ptk.find_value.at(b: Bool, +c: Tk.Class, +d: Tk.Class, +v: String, +w: String, +rest: List<&2, Tk.Ent>, +i: Nat,
  +eb: {Bool.and(Tk.Class.eq(c, d), Tk.same(v, w)) == b : Bool},
  +h: {Tk.find.at(b, rest, c, Tk.find(rest, c, v)) == Some{i} : Maybe<&2, Nat>},
  ih: {Tk.find(rest, c, v) == Some{i} : Maybe<&2, Nat>} -> {Tk.value(rest, c, i) == Some{v} : Maybe<&2, String>}) ->
  {Tk.value(Tk.Ent{d, w} <> rest, c, i) == Some{v} : Maybe<&2, String>}:
  match b:
    case True{}:
      +ec = ptk.cls_sound(c, d, ptk.and_l(Tk.Class.eq(c, d), Tk.same(v, w), eb))
      +ev = ptk.same_sound(v, w, ptk.and_r(Tk.Class.eq(c, d), Tk.same(v, w), eb))
      +ei = ptk.some_inj(Nat, 1n+Tk.count(rest, c), i, h)
      %ec : {Tk.value(Tk.Ent{_, w} <> rest, c, i) == Some{v} : Maybe<&2, String>}
      %ev : {Tk.value(Tk.Ent{c, _} <> rest, c, i) == Some{v} : Maybe<&2, String>}
      %ei : {Tk.value(Tk.Ent{c, v} <> rest, c, _) == Some{v} : Maybe<&2, String>}
      ptk.value_head(rest, c, v)
    case False{}:
      +le = ptk.find_le(rest, c, v, i, h)
      %Equal.sym(Bool, Nat.is_eq(i, 1n+Tk.count(rest, c)), False{}, ptk.le_ne(i, Tk.count(rest, c), le)) : {Tk.value.at(Bool.and(Tk.Class.eq(c, d), _), w, Tk.value(rest, c, i)) == Some{v} : Maybe<&2, String>}
      %Equal.sym(Bool, Bool.and(Tk.Class.eq(c, d), False{}), False{}, ptk.and_false(Tk.Class.eq(c, d))) : {Tk.value.at(_, w, Tk.value(rest, c, i)) == Some{v} : Maybe<&2, String>}
      ih(h)

# the index find gives is the index of the value
def ptk.find_value(es: List<&2, Tk.Ent>, +c: Tk.Class, +v: String, +i: Nat, +h: {Tk.find(es, c, v) == Some{i} : Maybe<&2, Nat>}) -> {Tk.value(es, c, i) == Some{v} : Maybe<&2, String>}:
  match es:
    case Nil{}:
      ptk.none_some(Nat, i, {Tk.value(Nil{}, c, i) == Some{v} : Maybe<&2, String>}, h)
    case e <> +rest:
      match e:
        case Tk.Ent{+d, +w}:
          ptk.find_value.at(Bool.and(Tk.Class.eq(c, d), Tk.same(v, w)), c, d, v, w, rest, i, {==}, h, h2 => ptk.find_value(rest, c, v, i, h2))

# a new value at the head moves no index
def ptk.value_new(+es: List<&2, Tk.Ent>, +c: Tk.Class, +v: String, +k: Tk.Class, +i: Nat, +x: String, +h: {Tk.value(es, k, i) == Some{x} : Maybe<&2, String>}) -> {Tk.value(Tk.Ent{c, v} <> es, k, i) == Some{x} : Maybe<&2, String>}:
  +le = ptk.value_le(es, k, i, x, h)
  %Equal.sym(Bool, Nat.is_eq(i, 1n+Tk.count(es, k)), False{}, ptk.le_ne(i, Tk.count(es, k), le)) : {Tk.value.at(Bool.and(Tk.Class.eq(k, c), _), v, Tk.value(es, k, i)) == Some{x} : Maybe<&2, String>}
  %Equal.sym(Bool, Bool.and(Tk.Class.eq(k, c), False{}), False{}, ptk.and_false(Tk.Class.eq(k, c))) : {Tk.value.at(_, v, Tk.value(es, k, i)) == Some{x} : Maybe<&2, String>}
  h

def ptk.find_new.at(b: Bool, +es: List<&2, Tk.Ent>, +c: Tk.Class, +v: String, +k: Tk.Class, +x: String, +i: Nat,
  +eb: {Bool.and(Tk.Class.eq(k, c), Tk.same(x, v)) == b : Bool},
  +h: {Tk.find(es, k, x) == Some{i} : Maybe<&2, Nat>},
  +no: {Tk.find(es, c, v) == None{} : Maybe<&2, Nat>}) ->
  {Tk.find.at(b, es, k, Tk.find(es, k, x)) == Some{i} : Maybe<&2, Nat>}:
  match b:
    case True{}:
      +ek = ptk.cls_sound(k, c, ptk.and_l(Tk.Class.eq(k, c), Tk.same(x, v), eb))
      +ex = ptk.same_sound(x, v, ptk.and_r(Tk.Class.eq(k, c), Tk.same(x, v), eb))
      +e1 = Equal.trans(Maybe<&2, Nat>, Tk.find(es, k, x), Tk.find(es, c, x), Tk.find(es, c, v), Equal.cong(Tk.Class, Maybe<&2, Nat>, z => Tk.find(es, z, x), k, c, ek), Equal.cong(String, Maybe<&2, Nat>, z => Tk.find(es, c, z), x, v, ex))
      +e2 = Equal.trans(Maybe<&2, Nat>, Tk.find(es, k, x), Tk.find(es, c, v), None{}, e1, no)
      +e3 = Equal.trans(Maybe<&2, Nat>, None{}, Tk.find(es, k, x), Some{i}, Equal.sym(Maybe<&2, Nat>, Tk.find(es, k, x), None{}, e2), h)
      ptk.none_some(Nat, i, {Tk.find.at(True{}, es, k, Tk.find(es, k, x)) == Some{i} : Maybe<&2, Nat>}, e3)
    case False{}:
      h

# a new value at the head moves no index another value has
def ptk.find_new(+es: List<&2, Tk.Ent>, +c: Tk.Class, +v: String, +k: Tk.Class, +x: String, +i: Nat, +h: {Tk.find(es, k, x) == Some{i} : Maybe<&2, Nat>}, +no: {Tk.find(es, c, v) == None{} : Maybe<&2, Nat>}) -> {Tk.find(Tk.Ent{c, v} <> es, k, x) == Some{i} : Maybe<&2, Nat>}:
  ptk.find_new.at(Bool.and(Tk.Class.eq(k, c), Tk.same(x, v)), es, c, v, k, x, i, {==}, h, no)

# the classes that map back are the spec's
def ptk.rev_spec(c: Tk.Class) -> {Tk.reversible(c) == S.reversible(c) : Bool}:
  match c:
    case Tk.Person{}:
      {==}
    case Tk.Email{}:
      {==}
    case Tk.Phone{}:
      {==}
    case Tk.Ip{}:
      {==}
    case Tk.Id{}:
      {==}
    case Tk.ApiKey{}:
      {==}
    case Tk.Card{}:
      {==}
    case Tk.Iban{}:
      {==}

def ptk.srev(+c: Tk.Class, -b: Bool, +e: {Tk.reversible(c) == b : Bool}) -> {S.reversible(c) == b : Bool}:
  Equal.trans(Bool, S.reversible(c), Tk.reversible(c), b, Equal.sym(Bool, Tk.reversible(c), S.reversible(c), ptk.rev_spec(c)), e)
