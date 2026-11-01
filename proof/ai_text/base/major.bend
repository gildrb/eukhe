# eukhe: lemmas of the R1 proofs (gemini_major): digits then a text that
# begins with no digit read back as those digits (aitm.digits), and what
# major.digits answers is the run at the start (aitm.dig_sound); the walk
# over the prefixes (aitm.s*).

import Base
import ../../../bend/model_name.bend as M
import ../../../bend/ai_text.bend as T
import ../../../laws/model_name.bend as ModelName
import ../../../laws/ai_text.bend as AiText
import ../../model_name/base.bend as LA
import ./dig.bend as LD

def aitm.found(d: String, hd: {AiText.sp_digs(d) == True{} : Bool}) -> {T.found(Bool.not(String.is_empty(d)), d) == Some{d} : Maybe<&2, String>}:
  match d:
    case SNil{}:
      LA.mnb.absurd_f({T.found(Bool.not(String.is_empty(SNil{})), SNil{}) == Some{SNil{}} : Maybe<&2, String>}, hd)
    case SCon{x, t}:
      {==}

def aitm.take(-d: String, -r: String, p: {T.dig.take(String.append(d, r)) == d : String} & {T.dig.drop(String.append(d, r)) == r : String}) -> {T.dig.take(String.append(d, r)) == d : String}:
  (a, b) = p
  a

def aitm.drop(-d: String, -r: String, p: {T.dig.take(String.append(d, r)) == d : String} & {T.dig.drop(String.append(d, r)) == r : String}) -> {T.dig.drop(String.append(d, r)) == r : String}:
  (a, b) = p
  b

# one or more digits, then a text that begins with no digit: the digits
def aitm.digits(+d: String, +rest: String, hd: {AiText.sp_digs(d) == True{} : Bool}, hr: {AiText.sp_no_dig(rest) == True{} : Bool}) -> {T.major.digits(String.append(d, rest)) == Some{d} : Maybe<&2, String>}:
  +h2 = hd
  %Equal.sym(String, T.dig.take(String.append(d, rest)), d, aitm.take(d, rest, LD.aitd.app(d, rest, LD.aitd.digs_digits(d, h2), hr))) : {T.found(Bool.not(String.is_empty(_)), _) == Some{d} : Maybe<&2, String>}
  aitm.found(d, h2)

def aitm.found_sound(b: Bool, +t: String, -d: String, eb: {Bool.not(String.is_empty(t)) == b : Bool}, h: {T.found(b, t) == Some{d} : Maybe<&2, String>}) -> {t == d : String} & {Bool.not(String.is_empty(t)) == True{} : Bool}:
  match b:
    case True{}:
      (LD.aitd.some_inj(String, t, d, h), eb)
    case False{}:
      LD.aitd.none_some(String, d, {t == d : String} & {Bool.not(String.is_empty(t)) == True{} : Bool}, h)

def aitm.DS(y: String, d: String) -> Type:
  {y == String.append(d, T.dig.drop(y)) : String} & ({AiText.sp_digs(d) == True{} : Bool} & {AiText.sp_no_dig(T.dig.drop(y)) == True{} : Bool})

def aitm.ds_fin(+y: String, +d: String, p: {T.dig.take(y) == d : String} & {Bool.not(String.is_empty(T.dig.take(y))) == True{} : Bool}) -> aitm.DS(y, d):
  (et, ne) = p
  +e = et
  +ty = T.dig.take(y)
  +dy = T.dig.drop(y)
  +e1 = Equal.trans(String, y, String.append(ty, dy), String.append(d, dy), LD.aitd.split(y), Equal.cong(String, String, z => String.append(z, dy), ty, d, e))
  +eds = Equal.trans(Bool, ModelName.sp_digits(d), ModelName.sp_digits(ty), True{}, Equal.cong(String, Bool, z => ModelName.sp_digits(z), d, ty, Equal.sym(String, ty, d, e)), LD.aitd.take_digits(y))
  +edn = Equal.trans(Bool, Bool.not(String.is_empty(d)), Bool.not(String.is_empty(ty)), True{}, Equal.cong(String, Bool, z => Bool.not(String.is_empty(z)), d, ty, Equal.sym(String, ty, d, e)), ne)
  (e1, (LD.aitd.digs_of(d, eds, edn), LD.aitd.drop_nodig(y)))

# what major.digits answers is the run of digits at the start, one or
# more, and the rest begins with no digit
def aitm.dig_sound(+y: String, +d: String, h: {T.major.digits(y) == Some{d} : Maybe<&2, String>}) -> aitm.DS(y, d):
  aitm.ds_fin(y, d, aitm.found_sound(Bool.not(String.is_empty(T.dig.take(y))), T.dig.take(y), d, {==}, h))

# the sound walk
# --------------

def aitm.G(id: String, d: String) -> Type:
  Sigma<&1, &1, Bool, live => Sigma<&1, &1, String, rest => {id == String.append(AiText.sp_gem(live), String.append(d, rest)) : String} & ({AiText.sp_digs(d) == True{} : Bool} & {AiText.sp_no_dig(rest) == True{} : Bool})>>

def aitm.g_plain(-id: String, +y: String, +d: String, v: {id == String.append("gemini-", y) : String}, ds: aitm.DS(y, d)) -> aitm.G(id, d):
  (e, (hd, hr)) = ds
  (False{}, (T.dig.drop(y), (Equal.trans(String, id, String.append("gemini-", y), String.append("gemini-", String.append(d, T.dig.drop(y))), v, Equal.cong(String, String, z => String.append("gemini-", z), y, String.append(d, T.dig.drop(y)), e)), (hd, hr))))

def aitm.g_live(-id: String, -y: String, +z: String, +d: String, v: {id == String.append("gemini-", y) : String}, v2: {y == String.append("live-", z) : String}, ds: aitm.DS(z, d)) -> aitm.G(id, d):
  (e, (hd, hr)) = ds
  +w = String.append(d, T.dig.drop(z))
  +e1 = Equal.trans(String, id, String.append("gemini-", y), String.append("gemini-", String.append("live-", z)), v, Equal.cong(String, String, u => String.append("gemini-", u), y, String.append("live-", z), v2))
  (True{}, (T.dig.drop(z), (Equal.trans(String, id, String.append("gemini-", String.append("live-", z)), String.append("gemini-live-", w), e1, Equal.cong(String, String, u => String.append("gemini-", String.append("live-", u)), z, w, e)), (hd, hr))))

def aitm.s3(-id: String, -y: String, +d: String, v: {id == String.append("gemini-", y) : String}, m: Maybe<&2, String>, v2: LA.mnb.SP("live-", y, m), h: {T.major.live(m) == Some{d} : Maybe<&2, String>}) -> aitm.G(id, d):
  match m:
    case None{}:
      LD.aitd.none_some(String, d, aitm.G(id, d), h)
    case Some{+z}:
      aitm.g_live(id, y, z, d, v, v2, aitm.dig_sound(z, d, h))

def aitm.s2(-id: String, +y: String, +d: String, v: {id == String.append("gemini-", y) : String}, m: Maybe<&2, String>, e: {T.major.digits(y) == m : Maybe<&2, String>}, h: {T.major.or(m, u => T.major.live(M.strip("live-", y))) == Some{d} : Maybe<&2, String>}) -> aitm.G(id, d):
  match m:
    case None{}:
      aitm.s3(id, y, d, v, M.strip("live-", y), LA.mnb.sp("live-", y), h)
    case Some{+x}:
      +exd = LD.aitd.some_inj(String, x, d, h)
      +e2 = Equal.trans(Maybe<&2, String>, T.major.digits(y), Some{x}, Some{d}, e, Equal.cong(String, Maybe<&2, String>, u => Some{u}, x, d, exd))
      aitm.g_plain(id, y, d, v, aitm.dig_sound(y, d, e2))

def aitm.s1(+id: String, +d: String, m: Maybe<&2, String>, v: LA.mnb.SP("gemini-", id, m), h: {T.major.after(m) == Some{d} : Maybe<&2, String>}) -> aitm.G(id, d):
  match m:
    case None{}:
      LD.aitd.none_some(String, d, aitm.G(id, d), h)
    case Some{+y}:
      aitm.s2(id, y, d, v, T.major.digits(y), {==}, h)
