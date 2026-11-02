# eukhe: lemmas of area ai_text about runs of digits and Maybe: a text is
# its digits then the rest (aitd.split), the digits are digits
# (aitd.take_digits), the rest begins with no digit (aitd.drop_nodig), and
# digits then a text that begins with no digit split there (aitd.take_app,
# aitd.drop_app).

import Base
import ../../../bend/text_pat.bend as Tp
import ../../../bend/ai_text.bend as T
import ../../../laws/model_name.bend as ModelName
import ../../../laws/ai_text.bend as AiText
import ../../model_name/base.bend as LA

# Maybe
# -----

def aitd.MIf(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# None is no Some
def aitd.none_some(-A: Data, -b: A, -G: Type, e: {None{} == Some{b} : Maybe<&2, A>}) -> G:
  %e : aitd.MIf(A, _, G)
  Unit{}

def aitd.get(-A: Data, m: Maybe<&2, A>, z: A) -> A:
  match m:
    case None{}:
      z
    case Some{x}:
      x

# Some is one to one
def aitd.some_inj(-A: Data, +a: A, -b: A, e: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  Equal.cong(Maybe<&2, A>, A, m => aitd.get(A, m, a), Some{a}, Some{b}, e)

# Digits
# ------

def aitd.split_at(b: Bool, +x: Char, -t: String, ih: {t == String.append(T.dig.take(t), T.dig.drop(t)) : String}) -> {SCon{x, t} == String.append(T.dig.take.at(b, x, u => T.dig.take(t)), T.dig.drop.at(b, SCon{x, t}, u => T.dig.drop(t))) : String}:
  match b:
    case True{}:
      LA.mnb.cons_eq(x, t, String.append(T.dig.take(t), T.dig.drop(t)), ih)
    case False{}:
      {==}

# a text is its digits, then the rest
def aitd.split(s: String) -> {s == String.append(T.dig.take(s), T.dig.drop(s)) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      aitd.split_at(Tp.is_dig(x), x, t, aitd.split(t))

def aitd.take_digits_at(b: Bool, +xc: U32, -t: String, eb: {Tp.is_dig(Chr{xc}) == b : Bool}, ih: {ModelName.sp_digits(T.dig.take(t)) == True{} : Bool}) -> {ModelName.sp_digits(T.dig.take.at(b, Chr{xc}, u => T.dig.take(t))) == True{} : Bool}:
  match b:
    case True{}:
      LA.mnb.and_t(Tp.is_dig(Chr{xc}), ModelName.sp_digits(T.dig.take(t)), eb, ih)
    case False{}:
      {==}

# the digits at the start are digits
def aitd.take_digits(s: String) -> {ModelName.sp_digits(T.dig.take(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          aitd.take_digits_at(Tp.is_dig(Chr{xc}), xc, t, {==}, aitd.take_digits(t))

def aitd.drop_nodig_at(b: Bool, +xc: U32, -t: String, eb: {Tp.is_dig(Chr{xc}) == b : Bool}, ih: {AiText.sp_no_dig(T.dig.drop(t)) == True{} : Bool}) -> {AiText.sp_no_dig(T.dig.drop.at(b, SCon{Chr{xc}, t}, u => T.dig.drop(t))) == True{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, Tp.is_dig(Chr{xc}), False{}, eb) : {Bool.not(_) == True{} : Bool}
      {==}

# what follows the digits at the start begins with no digit
def aitd.drop_nodig(s: String) -> {AiText.sp_no_dig(T.dig.drop(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          aitd.drop_nodig_at(Tp.is_dig(Chr{xc}), xc, t, {==}, aitd.drop_nodig(t))

# a text that begins with no digit has no digits at its start
def aitd.take_none(r: String, h: {AiText.sp_no_dig(r) == True{} : Bool}) -> {T.dig.take(r) == SNil{} : String} & {T.dig.drop(r) == r : String}:
  match r:
    case SNil{}:
      ({==}, {==})
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +e2 = LA.mnb.not_t(Tp.is_dig(Chr{xc}), h)
          (Equal.trans(String, T.dig.take(SCon{Chr{xc}, t}), T.dig.take.at(False{}, Chr{xc}, u => T.dig.take(t)), SNil{}, Equal.cong(Bool, String, b => T.dig.take.at(b, Chr{xc}, u => T.dig.take(t)), Tp.is_dig(Chr{xc}), False{}, e2), {==}), Equal.trans(String, T.dig.drop(SCon{Chr{xc}, t}), T.dig.drop.at(False{}, SCon{Chr{xc}, t}, u => T.dig.drop(t)), SCon{Chr{xc}, t}, Equal.cong(Bool, String, b => T.dig.drop.at(b, SCon{Chr{xc}, t}, u => T.dig.drop(t)), Tp.is_dig(Chr{xc}), False{}, e2), {==}))

def aitd.app_cons(+xc: U32, +t: String, +r: String, e: {Tp.is_dig(Chr{xc}) == True{} : Bool}, p: {T.dig.take(String.append(t, r)) == t : String} & {T.dig.drop(String.append(t, r)) == r : String}) -> {T.dig.take(SCon{Chr{xc}, String.append(t, r)}) == SCon{Chr{xc}, t} : String} & {T.dig.drop(SCon{Chr{xc}, String.append(t, r)}) == r : String}:
  (ta, da) = p
  +e2 = e
  +y = String.append(t, r)
  (Equal.trans(String, T.dig.take(SCon{Chr{xc}, y}), T.dig.take.at(True{}, Chr{xc}, u => T.dig.take(y)), SCon{Chr{xc}, t}, Equal.cong(Bool, String, b => T.dig.take.at(b, Chr{xc}, u => T.dig.take(y)), Tp.is_dig(Chr{xc}), True{}, e2), LA.mnb.cons_eq(Chr{xc}, T.dig.take(y), t, ta)), Equal.trans(String, T.dig.drop(SCon{Chr{xc}, y}), T.dig.drop.at(True{}, SCon{Chr{xc}, y}, u => T.dig.drop(y)), r, Equal.cong(Bool, String, b => T.dig.drop.at(b, SCon{Chr{xc}, y}, u => T.dig.drop(y)), Tp.is_dig(Chr{xc}), True{}, e2), da))

# digits, then a text that begins with no digit: the digits at the start
# are those digits, and the rest is that text
def aitd.app(d: String, +r: String, hd: {ModelName.sp_digits(d) == True{} : Bool}, hr: {AiText.sp_no_dig(r) == True{} : Bool}) -> {T.dig.take(String.append(d, r)) == d : String} & {T.dig.drop(String.append(d, r)) == r : String}:
  match d:
    case SNil{}:
      aitd.take_none(r, hr)
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +hh = hd
          aitd.app_cons(xc, t, r, LA.mnb.and_l(Tp.is_dig(Chr{xc}), ModelName.sp_digits(t), hh), aitd.app(t, r, LA.mnb.and_r(Tp.is_dig(Chr{xc}), ModelName.sp_digits(t), hh), hr))

# digits, not none: one or more digits
def aitd.digs_of(d: String, hd: {ModelName.sp_digits(d) == True{} : Bool}, hn: {Bool.not(String.is_empty(d)) == True{} : Bool}) -> {AiText.sp_digs(d) == True{} : Bool}:
  match d:
    case SNil{}:
      LA.mnb.absurd_f({AiText.sp_digs(SNil{}) == True{} : Bool}, hn)
    case SCon{x, t}:
      hd

# one or more digits are digits
def aitd.digs_digits(d: String, h: {AiText.sp_digs(d) == True{} : Bool}) -> {ModelName.sp_digits(d) == True{} : Bool}:
  match d:
    case SNil{}:
      LA.mnb.absurd_f({ModelName.sp_digits(SNil{}) == True{} : Bool}, h)
    case SCon{x, t}:
      h
