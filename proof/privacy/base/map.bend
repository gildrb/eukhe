# eukhe: lemmas of area privacy, section token: the token map
# (bend/privacy/token.bend) is the spec's state machine
# (spec/harness/privacy_map.bend): the code's count is the length of what
# a class holds, its find the place of a value there (no class holding a
# value twice), its value the value at a place; String.eq is equality
# (copied from proof/arg_repair/base.bend, prefix pmp.)

import Base
import ../../../bend/privacy/token.bend as Tk
import ../../../spec/harness/privacy.bend as S
import ../../../spec/harness/privacy_map.bend as Sm
import ../../../laws/privacy/token.bend as PrivacyToken

# Logic
# -----

def pmp.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pmp.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pmp.BD(_, A, Unit)
  Unit{}

def pmp.fst(-A: Type, -B: Type, p: A & B) -> A:
  (a, b) = p
  a

def pmp.and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pmp.absurd({False{} == True{} : Bool}, e)

def pmp.and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      pmp.absurd({b == True{} : Bool}, e)

# String.eq is equality
# ---------------------

def pmp.lt_eq(-G: Type, e: {LT{} == EQ{} : Cmp}) -> G:
  pmp.absurd(G, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), LT{}, EQ{}, e))

def pmp.gt_eq(-G: Type, e: {GT{} == EQ{} : Cmp}) -> G:
  pmp.absurd(G, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), GT{}, EQ{}, e))

def pmp.cmp_eq_fin(-p: Nat, -at: Word(p), -bt: Word(p), t: Cmp, +ab: Bool, +bb: Bool,
  et: {Word.cmp(p, at, bt) == t : Cmp},
  rec: {Word.cmp(p, at, bt) == EQ{} : Cmp} -> {at == bt : Word(p)},
  e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp})
  -> {WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}:
  match t:
    case LT{}:
      pmp.lt_eq({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, e)
    case GT{}:
      pmp.gt_eq({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, e)
    case EQ{}:
      match ab bb:
        case False{} False{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{False{}, w}, at, bt, rec(et))
        case False{} True{}:
          pmp.lt_eq({WCon{False{}, at} == WCon{True{}, bt} : Word.Con<p>}, e)
        case True{} False{}:
          pmp.gt_eq({WCon{True{}, at} == WCon{False{}, bt} : Word.Con<p>}, e)
        case True{} True{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{True{}, w}, at, bt, rec(et))

def pmp.word_eq(+n: Nat, +a: Word(n), +b: Word(n)) ->
  {Word.cmp(n, a, b) == EQ{} : Cmp} -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          e => {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          e => pmp.cmp_eq_fin(p, at, bt, Word.cmp(p, at, bt), ab, bb, {==}, pmp.word_eq(p, at, bt), e)

def pmp.u32_eq(+a: U32, +b: U32) -> {U32.cmp(a, b) == EQ{} : Cmp} -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      e => Equal.cong(Word(32n), U32, w => U32{w}, x, y, pmp.word_eq(32n, x, y)(e))

def pmp.str_cons(+x: U32, +y: U32, +t1: String, -t2: String, r: {t1 == t2 : String} & {U32.cmp(x, y) == EQ{} : Cmp}) -> {SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String} & {EQ{} == EQ{} : Cmp}:
  (p, q) = r
  %p : {SCon{Chr{x}, t1} == SCon{Chr{y}, _} : String} & {EQ{} == EQ{} : Cmp}
  %pmp.u32_eq(x, y)(q) : {SCon{Chr{x}, t1} == SCon{Chr{_}, t1} : String} & {EQ{} == EQ{} : Cmp}
  ({==}, {==})

def pmp.str_sound(+a: String, +b: String, c: Cmp, e: {Cmp.is_eq(String.order.go(a, b, c)) == True{} : Bool}) -> {a == b : String} & {c == EQ{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      match c:
        case LT{}:
          pmp.absurd({SNil{} == SNil{} : String} & {LT{} == EQ{} : Cmp}, e)
        case EQ{}:
          ({==}, {==})
        case GT{}:
          pmp.absurd({SNil{} == SNil{} : String} & {GT{} == EQ{} : Cmp}, e)
    case SNil{} SCon{h, t}:
      match c:
        case LT{}:
          pmp.absurd({SNil{} == SCon{h, t} : String} & {LT{} == EQ{} : Cmp}, e)
        case EQ{}:
          pmp.absurd({SNil{} == SCon{h, t} : String} & {EQ{} == EQ{} : Cmp}, e)
        case GT{}:
          pmp.absurd({SNil{} == SCon{h, t} : String} & {GT{} == EQ{} : Cmp}, e)
    case SCon{h, t} SNil{}:
      match c:
        case LT{}:
          pmp.absurd({SCon{h, t} == SNil{} : String} & {LT{} == EQ{} : Cmp}, e)
        case EQ{}:
          pmp.absurd({SCon{h, t} == SNil{} : String} & {EQ{} == EQ{} : Cmp}, e)
        case GT{}:
          pmp.absurd({SCon{h, t} == SNil{} : String} & {GT{} == EQ{} : Cmp}, e)
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      match c:
        case LT{}:
          pmp.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String} & {LT{} == EQ{} : Cmp}, e)
        case EQ{}:
          pmp.str_cons(x, y, t1, t2, pmp.str_sound(t1, t2, U32.cmp(x, y), e))
        case GT{}:
          pmp.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String} & {GT{} == EQ{} : Cmp}, e)

def pmp.str_eq(+a: String, +b: String, e: {String.eq(a, b) == True{} : Bool}) -> {a == b : String}:
  pmp.fst({a == b : String}, {EQ{} == EQ{} : Cmp}, pmp.str_sound(a, b, EQ{}, e))

# the code's char by char test is String.eq
def pmp.same_go(a: String, b: String, c: Cmp) -> {Cmp.is_eq(String.order.go(a, b, c)) == Bool.and(Cmp.is_eq(c), Tk.same(a, b)) : Bool}:
  match a b:
    case SNil{} SNil{}:
      match c:
        case LT{}:
          {==}
        case EQ{}:
          {==}
        case GT{}:
          {==}
    case SNil{} SCon{h, t}:
      match c:
        case LT{}:
          {==}
        case EQ{}:
          {==}
        case GT{}:
          {==}
    case SCon{h, t} SNil{}:
      match c:
        case LT{}:
          {==}
        case EQ{}:
          {==}
        case GT{}:
          {==}
    case SCon{Chr{+x}, t1} SCon{Chr{+y}, t2}:
      match c:
        case LT{}:
          {==}
        case EQ{}:
          pmp.same_go(t1, t2, U32.cmp(x, y))
        case GT{}:
          {==}

def pmp.same(+a: String, +b: String) -> {Tk.same(a, b) == String.eq(a, b) : Bool}:
  Equal.sym(Bool, String.eq(a, b), Tk.same(a, b), pmp.same_go(a, b, EQ{}))

# Classes
# -------

def pmp.tag(c: Tk.Class) -> {Tk.Class.tag(c) == Sm.ord(c) : Nat}:
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

def pmp.ceq(+c: Tk.Class, +d: Tk.Class) -> {Tk.Class.eq(c, d) == Sm.same_class(c, d) : Bool}:
  %Equal.sym(Nat, Tk.Class.tag(c), Sm.ord(c), pmp.tag(c)) : {Nat.is_eq(_, Tk.Class.tag(d)) == Sm.same_class(c, d) : Bool}
  %Equal.sym(Nat, Tk.Class.tag(d), Sm.ord(d), pmp.tag(d)) : {Nat.is_eq(Sm.ord(c), _) == Sm.same_class(c, d) : Bool}
  {==}

# classes the spec tells apart by nothing are one
def pmp.class_eq(c: Tk.Class, d: Tk.Class, h: {Sm.same_class(c, d) == True{} : Bool}) -> {c == d : Tk.Class}:
  match c d:
    case Tk.Person{} Tk.Person{}:
      {==}
    case Tk.Person{} Tk.Email{}:
      pmp.absurd({Tk.Person{} == Tk.Email{} : Tk.Class}, h)
    case Tk.Person{} Tk.Phone{}:
      pmp.absurd({Tk.Person{} == Tk.Phone{} : Tk.Class}, h)
    case Tk.Person{} Tk.Ip{}:
      pmp.absurd({Tk.Person{} == Tk.Ip{} : Tk.Class}, h)
    case Tk.Person{} Tk.Id{}:
      pmp.absurd({Tk.Person{} == Tk.Id{} : Tk.Class}, h)
    case Tk.Person{} Tk.ApiKey{}:
      pmp.absurd({Tk.Person{} == Tk.ApiKey{} : Tk.Class}, h)
    case Tk.Person{} Tk.Card{}:
      pmp.absurd({Tk.Person{} == Tk.Card{} : Tk.Class}, h)
    case Tk.Person{} Tk.Iban{}:
      pmp.absurd({Tk.Person{} == Tk.Iban{} : Tk.Class}, h)
    case Tk.Email{} Tk.Person{}:
      pmp.absurd({Tk.Email{} == Tk.Person{} : Tk.Class}, h)
    case Tk.Email{} Tk.Email{}:
      {==}
    case Tk.Email{} Tk.Phone{}:
      pmp.absurd({Tk.Email{} == Tk.Phone{} : Tk.Class}, h)
    case Tk.Email{} Tk.Ip{}:
      pmp.absurd({Tk.Email{} == Tk.Ip{} : Tk.Class}, h)
    case Tk.Email{} Tk.Id{}:
      pmp.absurd({Tk.Email{} == Tk.Id{} : Tk.Class}, h)
    case Tk.Email{} Tk.ApiKey{}:
      pmp.absurd({Tk.Email{} == Tk.ApiKey{} : Tk.Class}, h)
    case Tk.Email{} Tk.Card{}:
      pmp.absurd({Tk.Email{} == Tk.Card{} : Tk.Class}, h)
    case Tk.Email{} Tk.Iban{}:
      pmp.absurd({Tk.Email{} == Tk.Iban{} : Tk.Class}, h)
    case Tk.Phone{} Tk.Person{}:
      pmp.absurd({Tk.Phone{} == Tk.Person{} : Tk.Class}, h)
    case Tk.Phone{} Tk.Email{}:
      pmp.absurd({Tk.Phone{} == Tk.Email{} : Tk.Class}, h)
    case Tk.Phone{} Tk.Phone{}:
      {==}
    case Tk.Phone{} Tk.Ip{}:
      pmp.absurd({Tk.Phone{} == Tk.Ip{} : Tk.Class}, h)
    case Tk.Phone{} Tk.Id{}:
      pmp.absurd({Tk.Phone{} == Tk.Id{} : Tk.Class}, h)
    case Tk.Phone{} Tk.ApiKey{}:
      pmp.absurd({Tk.Phone{} == Tk.ApiKey{} : Tk.Class}, h)
    case Tk.Phone{} Tk.Card{}:
      pmp.absurd({Tk.Phone{} == Tk.Card{} : Tk.Class}, h)
    case Tk.Phone{} Tk.Iban{}:
      pmp.absurd({Tk.Phone{} == Tk.Iban{} : Tk.Class}, h)
    case Tk.Ip{} Tk.Person{}:
      pmp.absurd({Tk.Ip{} == Tk.Person{} : Tk.Class}, h)
    case Tk.Ip{} Tk.Email{}:
      pmp.absurd({Tk.Ip{} == Tk.Email{} : Tk.Class}, h)
    case Tk.Ip{} Tk.Phone{}:
      pmp.absurd({Tk.Ip{} == Tk.Phone{} : Tk.Class}, h)
    case Tk.Ip{} Tk.Ip{}:
      {==}
    case Tk.Ip{} Tk.Id{}:
      pmp.absurd({Tk.Ip{} == Tk.Id{} : Tk.Class}, h)
    case Tk.Ip{} Tk.ApiKey{}:
      pmp.absurd({Tk.Ip{} == Tk.ApiKey{} : Tk.Class}, h)
    case Tk.Ip{} Tk.Card{}:
      pmp.absurd({Tk.Ip{} == Tk.Card{} : Tk.Class}, h)
    case Tk.Ip{} Tk.Iban{}:
      pmp.absurd({Tk.Ip{} == Tk.Iban{} : Tk.Class}, h)
    case Tk.Id{} Tk.Person{}:
      pmp.absurd({Tk.Id{} == Tk.Person{} : Tk.Class}, h)
    case Tk.Id{} Tk.Email{}:
      pmp.absurd({Tk.Id{} == Tk.Email{} : Tk.Class}, h)
    case Tk.Id{} Tk.Phone{}:
      pmp.absurd({Tk.Id{} == Tk.Phone{} : Tk.Class}, h)
    case Tk.Id{} Tk.Ip{}:
      pmp.absurd({Tk.Id{} == Tk.Ip{} : Tk.Class}, h)
    case Tk.Id{} Tk.Id{}:
      {==}
    case Tk.Id{} Tk.ApiKey{}:
      pmp.absurd({Tk.Id{} == Tk.ApiKey{} : Tk.Class}, h)
    case Tk.Id{} Tk.Card{}:
      pmp.absurd({Tk.Id{} == Tk.Card{} : Tk.Class}, h)
    case Tk.Id{} Tk.Iban{}:
      pmp.absurd({Tk.Id{} == Tk.Iban{} : Tk.Class}, h)
    case Tk.ApiKey{} Tk.Person{}:
      pmp.absurd({Tk.ApiKey{} == Tk.Person{} : Tk.Class}, h)
    case Tk.ApiKey{} Tk.Email{}:
      pmp.absurd({Tk.ApiKey{} == Tk.Email{} : Tk.Class}, h)
    case Tk.ApiKey{} Tk.Phone{}:
      pmp.absurd({Tk.ApiKey{} == Tk.Phone{} : Tk.Class}, h)
    case Tk.ApiKey{} Tk.Ip{}:
      pmp.absurd({Tk.ApiKey{} == Tk.Ip{} : Tk.Class}, h)
    case Tk.ApiKey{} Tk.Id{}:
      pmp.absurd({Tk.ApiKey{} == Tk.Id{} : Tk.Class}, h)
    case Tk.ApiKey{} Tk.ApiKey{}:
      {==}
    case Tk.ApiKey{} Tk.Card{}:
      pmp.absurd({Tk.ApiKey{} == Tk.Card{} : Tk.Class}, h)
    case Tk.ApiKey{} Tk.Iban{}:
      pmp.absurd({Tk.ApiKey{} == Tk.Iban{} : Tk.Class}, h)
    case Tk.Card{} Tk.Person{}:
      pmp.absurd({Tk.Card{} == Tk.Person{} : Tk.Class}, h)
    case Tk.Card{} Tk.Email{}:
      pmp.absurd({Tk.Card{} == Tk.Email{} : Tk.Class}, h)
    case Tk.Card{} Tk.Phone{}:
      pmp.absurd({Tk.Card{} == Tk.Phone{} : Tk.Class}, h)
    case Tk.Card{} Tk.Ip{}:
      pmp.absurd({Tk.Card{} == Tk.Ip{} : Tk.Class}, h)
    case Tk.Card{} Tk.Id{}:
      pmp.absurd({Tk.Card{} == Tk.Id{} : Tk.Class}, h)
    case Tk.Card{} Tk.ApiKey{}:
      pmp.absurd({Tk.Card{} == Tk.ApiKey{} : Tk.Class}, h)
    case Tk.Card{} Tk.Card{}:
      {==}
    case Tk.Card{} Tk.Iban{}:
      pmp.absurd({Tk.Card{} == Tk.Iban{} : Tk.Class}, h)
    case Tk.Iban{} Tk.Person{}:
      pmp.absurd({Tk.Iban{} == Tk.Person{} : Tk.Class}, h)
    case Tk.Iban{} Tk.Email{}:
      pmp.absurd({Tk.Iban{} == Tk.Email{} : Tk.Class}, h)
    case Tk.Iban{} Tk.Phone{}:
      pmp.absurd({Tk.Iban{} == Tk.Phone{} : Tk.Class}, h)
    case Tk.Iban{} Tk.Ip{}:
      pmp.absurd({Tk.Iban{} == Tk.Ip{} : Tk.Class}, h)
    case Tk.Iban{} Tk.Id{}:
      pmp.absurd({Tk.Iban{} == Tk.Id{} : Tk.Class}, h)
    case Tk.Iban{} Tk.ApiKey{}:
      pmp.absurd({Tk.Iban{} == Tk.ApiKey{} : Tk.Class}, h)
    case Tk.Iban{} Tk.Card{}:
      pmp.absurd({Tk.Iban{} == Tk.Card{} : Tk.Class}, h)
    case Tk.Iban{} Tk.Iban{}:
      {==}

# Lists
# -----

def pmp.len_snoc(xs: List<&2, String>, -w: String) -> {List.length(&2, String, List.append(&2, String, xs, [w])) == 1n+List.length(&2, String, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, String, List.append(&2, String, rest, [w])), 1n+List.length(&2, String, rest), pmp.len_snoc(rest, w))

def pmp.count_at(b: Bool, -n: Nat, +xs: List<&2, String>, +w: String, ih: {n == List.length(&2, String, xs) : Nat}) -> {Nat.add(Tk.bit(b), n) == List.length(&2, String, Sm.held.add(b, xs, w)) : Nat}:
  match b:
    case True{}:
      %Equal.sym(Nat, List.length(&2, String, List.append(&2, String, xs, [w])), 1n+List.length(&2, String, xs), pmp.len_snoc(xs, w)) : {1n+n == _ : Nat}
      Equal.cong(Nat, Nat, k => 1n+k, n, List.length(&2, String, xs), ih)
    case False{}:
      ih

# the code's count of a class is the length of what the class holds
def pmp.count(es: List<&2, Tk.Ent>, +c: Tk.Class) -> {Tk.count(es, c) == List.length(&2, String, Sm.held(es, c)) : Nat}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Tk.Ent{+d, +w}:
          %Equal.sym(Bool, Tk.Class.eq(c, d), Sm.same_class(c, d), pmp.ceq(c, d)) : {Nat.add(Tk.bit(_), Tk.count(rest, c)) == List.length(&2, String, Sm.held.add(Sm.same_class(c, d), Sm.held(rest, c), w)) : Nat}
          pmp.count_at(Sm.same_class(c, d), Tk.count(rest, c), Sm.held(rest, c), w, pmp.count(rest, c))

# Places
# ------

# the place of v in a list with w after it: its place before, else the
# new last place when v is w
def pmp.psnoc(m: Maybe<&2, Nat>, hit: Bool, +n: Nat) -> Maybe<&2, Nat>:
  match m:
    case Some{i}:
      Some{i}
    case None{}:
      match hit:
        case True{}:
          Some{1n+n}
        case False{}:
          None{}

def pmp.p_nil(b: Bool) -> {Sm.place.at(b, None{}) == pmp.psnoc(None{}, b, 0n) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pmp.p_cons(a: Bool, m: Maybe<&2, Nat>, b: Bool, +n: Nat) -> {Sm.place.at(a, pmp.psnoc(m, b, n)) == pmp.psnoc(Sm.place.at(a, m), b, 1n+n) : Maybe<&2, Nat>}:
  match a:
    case True{}:
      {==}
    case False{}:
      match m:
        case Some{i}:
          {==}
        case None{}:
          match b:
            case True{}:
              {==}
            case False{}:
              {==}

def pmp.place_snoc(xs: List<&2, String>, +w: String, +v: String) -> {Sm.place(List.append(&2, String, xs, [w]), v) == pmp.psnoc(Sm.place(xs, v), String.eq(v, w), List.length(&2, String, xs)) : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      pmp.p_nil(String.eq(v, w))
    case +x <> +rest:
      %Equal.sym(Maybe<&2, Nat>, Sm.place(List.append(&2, String, rest, [w]), v), pmp.psnoc(Sm.place(rest, v), String.eq(v, w), List.length(&2, String, rest)), pmp.place_snoc(rest, w, v)) : {Sm.place.at(String.eq(v, x), _) == pmp.psnoc(Sm.place.at(String.eq(v, x), Sm.place(rest, v)), String.eq(v, w), 1n+List.length(&2, String, rest)) : Maybe<&2, Nat>}
      pmp.p_cons(String.eq(v, x), Sm.place(rest, v), String.eq(v, w), List.length(&2, String, rest))

def pmp.psnoc_f(m: Maybe<&2, Nat>, -n: Nat) -> {pmp.psnoc(m, False{}, n) == m : Maybe<&2, Nat>}:
  match m:
    case Some{i}:
      {==}
    case None{}:
      {==}

def pmp.fresh_none(m: Maybe<&2, Nat>, h: {Sm.fresh(m) == True{} : Bool}) -> {m == None{} : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{i}:
      pmp.absurd({Some{i} == None{} : Maybe<&2, Nat>}, h)

# find
# ----

# a value equal to the newest entry of its class: the map holds it
# nowhere older
def pmp.find_hit(q: Bool, +rest: List<&2, Tk.Ent>, +c: Tk.Class, +d: Tk.Class, +v: String, +w: String,
  eq: {String.eq(v, w) == q : Bool}, ec: {c == d : Tk.Class},
  hf: {Sm.fresh(Sm.place(Sm.held(rest, d), w)) == True{} : Bool})
  -> {Tk.find.at(q, rest, c, Sm.place(Sm.held(rest, c), v)) == pmp.psnoc(Sm.place(Sm.held(rest, c), v), q, List.length(&2, String, Sm.held(rest, c))) : Maybe<&2, Nat>}:
  match q:
    case True{}:
      +ev = pmp.str_eq(v, w, eq)
      +hn = pmp.fresh_none(Sm.place(Sm.held(rest, d), w), hf)
      %Equal.sym(Tk.Class, c, d, ec) : {Tk.find.at(True{}, rest, c, Sm.place(Sm.held(rest, c), v)) == pmp.psnoc(Sm.place(Sm.held(rest, _), v), True{}, List.length(&2, String, Sm.held(rest, c))) : Maybe<&2, Nat>}
      %Equal.sym(String, v, w, ev) : {Tk.find.at(True{}, rest, c, Sm.place(Sm.held(rest, c), v)) == pmp.psnoc(Sm.place(Sm.held(rest, d), _), True{}, List.length(&2, String, Sm.held(rest, c))) : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>, Sm.place(Sm.held(rest, d), w), None{}, hn) : {Tk.find.at(True{}, rest, c, Sm.place(Sm.held(rest, c), v)) == pmp.psnoc(_, True{}, List.length(&2, String, Sm.held(rest, c))) : Maybe<&2, Nat>}
      Equal.cong(Nat, Maybe<&2, Nat>, n => Some{1n+n}, Tk.count(rest, c), List.length(&2, String, Sm.held(rest, c)), pmp.count(rest, c))
    case False{}:
      Equal.sym(Maybe<&2, Nat>, pmp.psnoc(Sm.place(Sm.held(rest, c), v), False{}, List.length(&2, String, Sm.held(rest, c))), Sm.place(Sm.held(rest, c), v), pmp.psnoc_f(Sm.place(Sm.held(rest, c), v), List.length(&2, String, Sm.held(rest, c))))

def pmp.find_at(sc: Bool, +rest: List<&2, Tk.Ent>, +c: Tk.Class, +d: Tk.Class, +v: String, +w: String,
  es: {Sm.same_class(c, d) == sc : Bool},
  hf: {Sm.fresh(Sm.place(Sm.held(rest, d), w)) == True{} : Bool})
  -> {Tk.find.at(Bool.and(sc, String.eq(v, w)), rest, c, Sm.place(Sm.held(rest, c), v)) == Sm.place(Sm.held.add(sc, Sm.held(rest, c), w), v) : Maybe<&2, Nat>}:
  match sc:
    case True{}:
      %Equal.sym(Maybe<&2, Nat>, Sm.place(List.append(&2, String, Sm.held(rest, c), [w]), v), pmp.psnoc(Sm.place(Sm.held(rest, c), v), String.eq(v, w), List.length(&2, String, Sm.held(rest, c))), pmp.place_snoc(Sm.held(rest, c), w, v)) : {Tk.find.at(String.eq(v, w), rest, c, Sm.place(Sm.held(rest, c), v)) == _ : Maybe<&2, Nat>}
      pmp.find_hit(String.eq(v, w), rest, c, d, v, w, {==}, pmp.class_eq(c, d, es), hf)
    case False{}:
      {==}

# with no class holding a value twice, the code's find is the place of
# the value among its class's values
def pmp.find(es: List<&2, Tk.Ent>, +c: Tk.Class, +v: String, +ok: {Sm.distinct(es) == True{} : Bool}) -> {Tk.find(es, c, v) == Sm.place(Sm.held(es, c), v) : Maybe<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Tk.Ent{+d, +w}:
          +hf = pmp.and_l(Sm.fresh(Sm.place(Sm.held(rest, d), w)), Sm.distinct(rest), ok)
          +hr = pmp.and_r(Sm.fresh(Sm.place(Sm.held(rest, d), w)), Sm.distinct(rest), ok)
          %Equal.sym(Bool, Tk.Class.eq(c, d), Sm.same_class(c, d), pmp.ceq(c, d)) : {Tk.find.at(Bool.and(_, Tk.same(v, w)), rest, c, Tk.find(rest, c, v)) == Sm.place(Sm.held.add(Sm.same_class(c, d), Sm.held(rest, c), w), v) : Maybe<&2, Nat>}
          %Equal.sym(Bool, Tk.same(v, w), String.eq(v, w), pmp.same(v, w)) : {Tk.find.at(Bool.and(Sm.same_class(c, d), _), rest, c, Tk.find(rest, c, v)) == Sm.place(Sm.held.add(Sm.same_class(c, d), Sm.held(rest, c), w), v) : Maybe<&2, Nat>}
          %Equal.sym(Maybe<&2, Nat>, Tk.find(rest, c, v), Sm.place(Sm.held(rest, c), v), pmp.find(rest, c, v, hr)) : {Tk.find.at(Bool.and(Sm.same_class(c, d), String.eq(v, w)), rest, c, _) == Sm.place(Sm.held.add(Sm.same_class(c, d), Sm.held(rest, c), w), v) : Maybe<&2, Nat>}
          pmp.find_at(Sm.same_class(c, d), rest, c, d, v, w, {==}, hf)

# value
# -----

def pmp.at_snoc(xs: List<&2, String>, +w: String, i: Nat) -> {Sm.at(List.append(&2, String, xs, [w]), i) == Tk.value.at(Nat.is_eq(i, 1n+List.length(&2, String, xs)), w, Sm.at(xs, i)) : Maybe<&2, String>}:
  match xs:
    case Nil{}:
      match i:
        case 0n:
          {==}
        case 1n+j:
          match j:
            case 0n:
              {==}
            case 1n+k:
              {==}
    case +x <> +rest:
      match i:
        case 0n:
          {==}
        case 1n+j:
          match j:
            case 0n:
              {==}
            case 1n+k:
              pmp.at_snoc(rest, w, 1n+k)

def pmp.value_at(sc: Bool, +rest: List<&2, Tk.Ent>, +c: Tk.Class, +i: Nat, +w: String)
  -> {Tk.value.at(Bool.and(sc, Nat.is_eq(i, 1n+List.length(&2, String, Sm.held(rest, c)))), w, Sm.at(Sm.held(rest, c), i)) == Sm.at(Sm.held.add(sc, Sm.held(rest, c), w), i) : Maybe<&2, String>}:
  match sc:
    case True{}:
      Equal.sym(Maybe<&2, String>, Sm.at(List.append(&2, String, Sm.held(rest, c), [w]), i), Tk.value.at(Nat.is_eq(i, 1n+List.length(&2, String, Sm.held(rest, c))), w, Sm.at(Sm.held(rest, c), i)), pmp.at_snoc(Sm.held(rest, c), w, i))
    case False{}:
      {==}

# the code's value of a class at an index is the spec's value at that
# place
def pmp.value(es: List<&2, Tk.Ent>, +c: Tk.Class, +i: Nat) -> {Tk.value(es, c, i) == Sm.at(Sm.held(es, c), i) : Maybe<&2, String>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Tk.Ent{+d, +w}:
          %Equal.sym(Bool, Tk.Class.eq(c, d), Sm.same_class(c, d), pmp.ceq(c, d)) : {Tk.value.at(Bool.and(_, Nat.is_eq(i, 1n+Tk.count(rest, c))), w, Tk.value(rest, c, i)) == Sm.at(Sm.held.add(Sm.same_class(c, d), Sm.held(rest, c), w), i) : Maybe<&2, String>}
          %Equal.sym(Nat, Tk.count(rest, c), List.length(&2, String, Sm.held(rest, c)), pmp.count(rest, c)) : {Tk.value.at(Bool.and(Sm.same_class(c, d), Nat.is_eq(i, 1n+_)), w, Tk.value(rest, c, i)) == Sm.at(Sm.held.add(Sm.same_class(c, d), Sm.held(rest, c), w), i) : Maybe<&2, String>}
          %Equal.sym(Maybe<&2, String>, Tk.value(rest, c, i), Sm.at(Sm.held(rest, c), i), pmp.value(rest, c, i)) : {Tk.value.at(Bool.and(Sm.same_class(c, d), Nat.is_eq(i, 1n+List.length(&2, String, Sm.held(rest, c)))), w, _) == Sm.at(Sm.held.add(Sm.same_class(c, d), Sm.held(rest, c), w), i) : Maybe<&2, String>}
          pmp.value_at(Sm.same_class(c, d), rest, c, i, w)

# One value, one token
# --------------------

def pmp.new(+es: List<&2, Tk.Ent>, +c: Tk.Class, +v: String, m: Maybe<&2, Nat>) -> {Tk.scrub_val.new(es, c, v, m) == Sm.scrub1.place(m, es, c, v) : Tk.Step}:
  match m:
    case Some{i}:
      {==}
    case None{}:
      Equal.cong(Nat, Tk.Step, n => Tk.Step{Tk.Book{Tk.Ent{c, v} <> es}, Tk.Mapped{1n+n}}, Tk.count(es, c), List.length(&2, String, Sm.held(es, c)), pmp.count(es, c))

def pmp.val_of(r: Bool, +es: List<&2, Tk.Ent>, +c: Tk.Class, +v: String, ok: {Sm.distinct(es) == True{} : Bool}) -> {Tk.scrub_val.of(r, Tk.Book{es}, c, v) == Sm.scrub1.of(r, Tk.Book{es}, c, v) : Tk.Step}:
  match r:
    case True{}:
      %Equal.sym(Maybe<&2, Nat>, Tk.find(es, c, v), Sm.place(Sm.held(es, c), v), pmp.find(es, c, v, ok)) : {Tk.scrub_val.new(es, c, v, _) == Sm.scrub1.place(Sm.place(Sm.held(es, c), v), es, c, v) : Tk.Step}
      pmp.new(es, c, v, Sm.place(Sm.held(es, c), v))
    case False{}:
      {==}

# with no class holding a value twice, a value's token and the map after
# it are the spec's
def pmp.val(b: Tk.Book, +c: Tk.Class, +v: String, ok: {Sm.book_distinct(b) == True{} : Bool}) -> {Tk.scrub_val(b, c, v) == Sm.scrub1(b, c, v) : Tk.Step}:
  match b:
    case Tk.Book{+es}:
      %Equal.sym(Bool, Tk.reversible(c), S.reversible(c), PrivacyToken.privacy_classes(c)) : {Tk.scrub_val.of(_, Tk.Book{es}, c, v) == Sm.scrub1(Tk.Book{es}, c, v) : Tk.Step}
      pmp.val_of(S.reversible(c), es, c, v, ok)

def pmp.kept_place(m: Maybe<&2, Nat>, +es: List<&2, Tk.Ent>, +c: Tk.Class, +v: String, em: {Sm.place(Sm.held(es, c), v) == m : Maybe<&2, Nat>}, ok: {Sm.distinct(es) == True{} : Bool}) -> {Sm.book_distinct(Sm.step_book(Sm.scrub1.place(m, es, c, v))) == True{} : Bool}:
  match m:
    case Some{i}:
      ok
    case None{}:
      %Equal.sym(Maybe<&2, Nat>, Sm.place(Sm.held(es, c), v), None{}, em) : {Bool.and(Sm.fresh(_), Sm.distinct(es)) == True{} : Bool}
      ok

def pmp.kept_of(r: Bool, +es: List<&2, Tk.Ent>, +c: Tk.Class, +v: String, ok: {Sm.distinct(es) == True{} : Bool}) -> {Sm.book_distinct(Sm.step_book(Sm.scrub1.of(r, Tk.Book{es}, c, v))) == True{} : Bool}:
  match r:
    case True{}:
      pmp.kept_place(Sm.place(Sm.held(es, c), v), es, c, v, {==}, ok)
    case False{}:
      ok

# a scrub from a map with no value held twice leaves one
def pmp.kept(b: Tk.Book, +c: Tk.Class, +v: String, ok: {Sm.book_distinct(b) == True{} : Bool}) -> {Sm.book_distinct(Sm.step_book(Sm.scrub1(b, c, v))) == True{} : Bool}:
  match b:
    case Tk.Book{+es}:
      pmp.kept_of(S.reversible(c), es, c, v, ok)

# A text
# ------

def pmp.push(t: Tk.Tok, r: Tk.Toks) -> {Tk.scrub_vals.cons(t, r) == Sm.push(t, r) : Tk.Toks}:
  match r:
    case Tk.Toks{m, ts}:
      {==}

def pmp.step(r: Tk.Step, +rest: List<&2, Tk.Val>, ih: {Tk.scrub_vals(rest, Sm.step_book(r)) == Sm.scrub_vals(rest, Sm.step_book(r)) : Tk.Toks}) -> {Tk.scrub_vals.cons(Tk.Step.t(r), Tk.scrub_vals(rest, Tk.Step.m(r))) == Sm.push(Sm.step_tok(r), Sm.scrub_vals(rest, Sm.step_book(r))) : Tk.Toks}:
  match r:
    case Tk.Step{+m, +t}:
      %Equal.sym(Tk.Toks, Tk.scrub_vals(rest, m), Sm.scrub_vals(rest, m), ih) : {Tk.scrub_vals.cons(t, _) == Sm.push(t, Sm.scrub_vals(rest, m)) : Tk.Toks}
      pmp.push(t, Sm.scrub_vals(rest, m))

def pmp.toks_book(t: Tk.Tok, r: Tk.Toks) -> {Sm.toks_book(Sm.push(t, r)) == Sm.toks_book(r) : Tk.Book}:
  match r:
    case Tk.Toks{m, ts}:
      {==}

# with no class holding a value twice, a text's tokens and the map after
# them are the spec's
def pmp.scrub_vals(vs: List<&2, Tk.Val>, +b: Tk.Book, +ok: {Sm.book_distinct(b) == True{} : Bool}) -> {Tk.scrub_vals(vs, b) == Sm.scrub_vals(vs, b) : Tk.Toks}:
  match vs:
    case Nil{}:
      {==}
    case x <> +rest:
      match x:
        case Tk.Val{+c, +v}:
          %Equal.sym(Tk.Step, Tk.scrub_val(b, c, v), Sm.scrub1(b, c, v), pmp.val(b, c, v, ok)) : {Tk.scrub_vals.cons(Tk.Step.t(_), Tk.scrub_vals(rest, Tk.Step.m(_))) == Sm.push(Sm.step_tok(Sm.scrub1(b, c, v)), Sm.scrub_vals(rest, Sm.step_book(Sm.scrub1(b, c, v)))) : Tk.Toks}
          pmp.step(Sm.scrub1(b, c, v), rest, pmp.scrub_vals(rest, Sm.step_book(Sm.scrub1(b, c, v)), pmp.kept(b, c, v, ok)))

# every scrub from a map with no value held twice leaves one
def pmp.dk(vs: List<&2, Tk.Val>, +b: Tk.Book, +ok: {Sm.book_distinct(b) == True{} : Bool}) -> {Sm.book_distinct(Sm.toks_book(Sm.scrub_vals(vs, b))) == True{} : Bool}:
  match vs:
    case Nil{}:
      ok
    case x <> +rest:
      match x:
        case Tk.Val{+c, +v}:
          %Equal.sym(Tk.Book, Sm.toks_book(Sm.push(Sm.step_tok(Sm.scrub1(b, c, v)), Sm.scrub_vals(rest, Sm.step_book(Sm.scrub1(b, c, v))))), Sm.toks_book(Sm.scrub_vals(rest, Sm.step_book(Sm.scrub1(b, c, v)))), pmp.toks_book(Sm.step_tok(Sm.scrub1(b, c, v)), Sm.scrub_vals(rest, Sm.step_book(Sm.scrub1(b, c, v))))) : {Sm.book_distinct(_) == True{} : Bool}
          pmp.dk(rest, Sm.step_book(Sm.scrub1(b, c, v)), pmp.kept(b, c, v, ok))

# Restores
# --------

def pmp.tok_of(r: Bool, b: Tk.Book, +c: Tk.Class, +i: Nat) -> {Tk.restore_tok.of(r, b, c, i) == Sm.restore1.of(r, b, c, i) : Maybe<&2, String>}:
  match r:
    case True{}:
      match b:
        case Tk.Book{es}:
          pmp.value(es, c, i)
    case False{}:
      {==}

def pmp.tok(+b: Tk.Book, +c: Tk.Class, +i: Nat) -> {Tk.restore_tok(b, c, i) == Sm.restore1(b, c, i) : Maybe<&2, String>}:
  %Equal.sym(Bool, Tk.reversible(c), S.reversible(c), PrivacyToken.privacy_classes(c)) : {Tk.restore_tok.of(_, b, c, i) == Sm.restore1(b, c, i) : Maybe<&2, String>}
  pmp.tok_of(S.reversible(c), b, c, i)

# a text's tokens restore to the spec's values
def pmp.restore_toks(rs: List<&2, Tk.Ref>, +b: Tk.Book) -> {Tk.restore_toks(rs, b) == Sm.restore_toks(rs, b) : List<&2, Maybe<&2, String>>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +rest:
      match r:
        case Tk.Ref{+c, +i}:
          %Equal.sym(Maybe<&2, String>, Tk.restore_tok(b, c, i), Sm.restore1(b, c, i), pmp.tok(b, c, i)) : {_ <> Tk.restore_toks(rest, b) == Sm.restore1(b, c, i) <> Sm.restore_toks(rest, b) : List<&2, Maybe<&2, String>>}
          Equal.cong(List<&2, Maybe<&2, String>>, List<&2, Maybe<&2, String>>, z => Sm.restore1(b, c, i) <> z, Tk.restore_toks(rest, b), Sm.restore_toks(rest, b), pmp.restore_toks(rest, b))
