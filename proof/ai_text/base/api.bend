# eukhe: lemmas of the R2 proofs (api_version): the walk over the text
# reaches a part with the start flag the spec computes (aita.walk); a part
# "v" ++ D ++ B is a version (aita.ver_ok); a version is that shape
# (aita.ver_sound); a hit of the walk is such a part after a place that
# ends with `/` or the text's start (aita.go_sound).

import Base
import ../../../bend/phrase.bend as P
import ../../../bend/model_name.bend as M
import ../../../bend/ai_text.bend as T
import ../../../laws/model_name.bend as ModelName
import ../../../laws/ai_text.bend as AiText
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../../model_name/base.bend as LA
import ./dig.bend as LD

# the code's end of a part is the spec's
def aita.at_end_eq(b: String) -> {T.at_end(b) == AiText.sp_part_end(b) : Bool}:
  match b:
    case SNil{}:
      {==}
    case SCon{x, t}:
      match x:
        case Chr{xc}:
          {==}

# a lazy `or` whose left side is True is True
def aita.or_lt(y: Bool, -z: Bool, ey: {y == True{} : Bool}) -> {P.pm.or(y, u => z) == True{} : Bool}:
  match y:
    case True{}:
      {==}
    case False{}:
      LA.mnb.absurd_f({P.pm.or(False{}, u => z) == True{} : Bool}, ey)

# one or more digits are not none
def aita.digs_ne(d: String, h: {AiText.sp_digs(d) == True{} : Bool}) -> {Bool.not(String.is_empty(d)) == True{} : Bool}:
  match d:
    case SNil{}:
      LA.mnb.absurd_f({Bool.not(String.is_empty(SNil{})) == True{} : Bool}, h)
    case SCon{x, t}:
      {==}

def aita.take(-d: String, -r: String, p: {T.dig.take(String.append(d, r)) == d : String} & {T.dig.drop(String.append(d, r)) == r : String}) -> {T.dig.take(String.append(d, r)) == d : String}:
  (a, b) = p
  a

def aita.drop(-d: String, -r: String, p: {T.dig.take(String.append(d, r)) == d : String} & {T.dig.drop(String.append(d, r)) == r : String}) -> {T.dig.drop(String.append(d, r)) == r : String}:
  (a, b) = p
  b

# Complete
# --------

# the walk over a reaches what follows with the start flag of the spec
def aita.walk(a: String, +u: String, st: Bool, h: {T.api.go(u, AiText.sp_last_slash(a, st)) == True{} : Bool}) -> {T.api.go(String.append(a, u), st) == True{} : Bool}:
  match a:
    case SNil{}:
      h
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          LA.mnb.or_rl(P.pm.and(st, w => T.ver(SCon{Chr{xc}, String.append(t, u)})), T.api.go(String.append(t, u), U32.is_eq(xc, 47)), aita.walk(t, u, U32.is_eq(xc, 47), h))

# the text after B begins with no digit
def aita.nodig_tail(m: Maybe<&2, String>, +b: String, hb: {AiText.sp_part_end(b) == True{} : Bool}) -> {AiText.sp_no_dig(String.append(AiText.sp_beta(m), b)) == True{} : Bool}:
  match m:
    case None{}:
      match b:
        case SNil{}:
          {==}
        case SCon{x, +t}:
          match x:
            case Chr{+xc}:
              %Equal.sym(U32, xc, 47, PWireBoolExact.wr_eq_sound(xc, 47, hb)) : {AiText.sp_no_dig(SCon{Chr{_}, t}) == True{} : Bool}
              {==}
    case Some{e}:
      {==}

def aita.at_end_t(+b: String, hb: {AiText.sp_part_end(b) == True{} : Bool}) -> {T.at_end(b) == True{} : Bool}:
  Equal.trans(Bool, T.at_end(b), AiText.sp_part_end(b), True{}, aita.at_end_eq(b), hb)

# after the digits, B and the end of the part pass
def aita.tail_ok(m: Maybe<&2, String>, +b: String, hm: {AiText.sp_beta_ok(m) == True{} : Bool}, hb: {AiText.sp_part_end(b) == True{} : Bool}) -> {T.ver.tail(String.append(AiText.sp_beta(m), b)) == True{} : Bool}:
  match m:
    case None{}:
      aita.or_lt(T.at_end(b), T.ver.beta(M.strip("beta", b)), aita.at_end_t(b, hb))
    case Some{+e}:
      +h2 = hb
      %Equal.sym(String, T.dig.drop(String.append(e, b)), b, aita.drop(e, b, LD.aitd.app(e, b, hm, aita.nodig_tail(None{}, b, h2)))) : {T.at_end(_) == True{} : Bool}
      aita.at_end_t(b, h2)

# "v" ++ D ++ B, the part ending there, is a version
def aita.ver_ok(+d: String, +m: Maybe<&2, String>, +b: String, hd: {AiText.sp_digs(d) == True{} : Bool}, hm: {AiText.sp_beta_ok(m) == True{} : Bool}, hb: {AiText.sp_part_end(b) == True{} : Bool}) -> {T.ver(String.append("v", String.append(d, String.append(AiText.sp_beta(m), b)))) == True{} : Bool}:
  +y = String.append(AiText.sp_beta(m), b)
  +w = String.append(d, y)
  +h2 = hd
  +hb2 = hb
  %Equal.sym(String, T.dig.take(w), d, aita.take(d, y, LD.aitd.app(d, y, LD.aitd.digs_digits(d, h2), aita.nodig_tail(m, b, hb2)))) : {P.pm.and(Bool.not(String.is_empty(_)), u => T.ver.tail(T.dig.drop(w))) == True{} : Bool}
  %Equal.sym(String, T.dig.drop(w), y, aita.drop(d, y, LD.aitd.app(d, y, LD.aitd.digs_digits(d, h2), aita.nodig_tail(m, b, hb2)))) : {P.pm.and(Bool.not(String.is_empty(d)), u => T.ver.tail(_)) == True{} : Bool}
  LA.mnb.and_lt(Bool.not(String.is_empty(d)), T.ver.tail(y), aita.digs_ne(d, h2), aita.tail_ok(m, b, hm, hb2))

# a version at the text's start, or after a `/`, is a hit
def aita.go_here(+u: String, h: {T.ver(u) == True{} : Bool}) -> {T.api.go(u, True{}) == True{} : Bool}:
  match u:
    case SNil{}:
      LA.mnb.absurd_f({T.api.go(SNil{}, True{}) == True{} : Bool}, h)
    case SCon{+x, +t}:
      aita.or_lt(T.ver(SCon{x, t}), T.api.go(t, Char.is_eq(x, '/')), h)

# Sound
# -----

def aita.TP(y: String) -> Type:
  Sigma<&1, &1, Maybe<&2, String>, m => Sigma<&1, &1, String, b => {y == String.append(AiText.sp_beta(m), b) : String} & ({AiText.sp_beta_ok(m) == True{} : Bool} & {AiText.sp_part_end(b) == True{} : Bool})>>

def aita.beta_sound(-y: String, m0: Maybe<&2, String>, v: LA.mnb.SP("beta", y, m0), h: {T.ver.beta(m0) == True{} : Bool}) -> aita.TP(y):
  match m0:
    case None{}:
      LA.mnb.absurd_f(aita.TP(y), h)
    case Some{+z}:
      +ty = T.dig.take(z)
      +dy = T.dig.drop(z)
      (Some{ty}, (dy, (Equal.trans(String, y, String.append("beta", z), String.append("beta", String.append(ty, dy)), v, Equal.cong(String, String, u => String.append("beta", u), z, String.append(ty, dy), LD.aitd.split(z))), (LD.aitd.take_digits(z), Equal.trans(Bool, AiText.sp_part_end(dy), T.at_end(dy), True{}, Equal.sym(Bool, T.at_end(dy), AiText.sp_part_end(dy), aita.at_end_eq(dy)), h)))))

def aita.tail_sound(+y: String, c: Bool, ec: {T.at_end(y) == c : Bool}, h: {P.pm.or(c, u => T.ver.beta(M.strip("beta", y))) == True{} : Bool}) -> aita.TP(y):
  match c:
    case True{}:
      (None{}, (y, ({==}, ({==}, Equal.trans(Bool, AiText.sp_part_end(y), T.at_end(y), True{}, Equal.sym(Bool, T.at_end(y), AiText.sp_part_end(y), aita.at_end_eq(y)), ec)))))
    case False{}:
      aita.beta_sound(y, M.strip("beta", y), LA.mnb.sp("beta", y), h)

def aita.VP(s: String) -> Type:
  Sigma<&1, &1, String, d => Sigma<&1, &1, Maybe<&2, String>, m => Sigma<&1, &1, String, b => {s == String.append("v", String.append(d, String.append(AiText.sp_beta(m), b))) : String} & ({AiText.sp_digs(d) == True{} : Bool} & ({AiText.sp_beta_ok(m) == True{} : Bool} & {AiText.sp_part_end(b) == True{} : Bool}))>>>

def aita.ver_fin(-s: String, +w: String, v: {s == String.append("v", w) : String}, ne: {Bool.not(String.is_empty(T.dig.take(w))) == True{} : Bool}, tp: aita.TP(T.dig.drop(w))) -> aita.VP(s):
  (+m, (+b, (ey, (hm, hb)))) = tp
  +tw = T.dig.take(w)
  +dw = T.dig.drop(w)
  +z = String.append(AiText.sp_beta(m), b)
  +ew = Equal.trans(String, w, String.append(tw, dw), String.append(tw, z), LD.aitd.split(w), Equal.cong(String, String, u => String.append(tw, u), dw, z, ey))
  (tw, (m, (b, (Equal.trans(String, s, String.append("v", w), String.append("v", String.append(tw, z)), v, Equal.cong(String, String, u => String.append("v", u), w, String.append(tw, z), ew)), (LD.aitd.digs_of(tw, LD.aitd.take_digits(w), ne), (hm, hb))))))

def aita.ver_at(-s: String, m0: Maybe<&2, String>, v: LA.mnb.SP("v", s, m0), h: {T.ver.at(m0) == True{} : Bool}) -> aita.VP(s):
  match m0:
    case None{}:
      LA.mnb.absurd_f(aita.VP(s), h)
    case Some{+w}:
      +a = Bool.not(String.is_empty(T.dig.take(w)))
      +b = T.ver.tail(T.dig.drop(w))
      +e = Equal.trans(Bool, Bool.and(a, b), P.pm.and(a, u => b), True{}, Equal.sym(Bool, P.pm.and(a, u => b), Bool.and(a, b), LA.mnb.and_lazy(a, b)), h)
      aita.ver_fin(s, w, v, LA.mnb.and_l(a, b, e), aita.tail_sound(T.dig.drop(w), T.at_end(T.dig.drop(w)), {==}, LA.mnb.and_r(a, b, e)))

# a version is "v" ++ D ++ B, the part ending there
def aita.ver_sound(+s: String, h: {T.ver(s) == True{} : Bool}) -> aita.VP(s):
  aita.ver_at(s, M.strip("v", s), LA.mnb.sp("v", s), h)

def aita.GS(s: String, st: Bool) -> Type:
  Sigma<&1, &1, String, a => Sigma<&1, &1, String, d => Sigma<&1, &1, Maybe<&2, String>, m => Sigma<&1, &1, String, b => {s == String.append(a, String.append("v", String.append(d, String.append(AiText.sp_beta(m), b)))) : String} & ({AiText.sp_last_slash(a, st) == True{} : Bool} & ({AiText.sp_digs(d) == True{} : Bool} & ({AiText.sp_beta_ok(m) == True{} : Bool} & {AiText.sp_part_end(b) == True{} : Bool})))>>>>

def aita.here_fin(-u: String, vp: aita.VP(u)) -> aita.GS(u, True{}):
  (d, (m, (b, (e, (hd, (hm, hb)))))) = vp
  (SNil{}, (d, (m, (b, (e, ({==}, (hd, (hm, hb))))))))

def aita.here(st: Bool, +u: String, e: {P.pm.and(st, w => T.ver(u)) == True{} : Bool}) -> aita.GS(u, st):
  match st:
    case True{}:
      aita.here_fin(u, aita.ver_sound(u, e))
    case False{}:
      LA.mnb.absurd_f(aita.GS(u, False{}), e)

def aita.next(+xc: U32, -t: String, -st: Bool, gs: aita.GS(t, U32.is_eq(xc, 47))) -> aita.GS(SCon{Chr{xc}, t}, st):
  (+a, (+d, (+m, (+b, (e, (hl, r)))))) = gs
  (SCon{Chr{xc}, a}, (d, (m, (b, (LA.mnb.cons_eq(Chr{xc}, t, String.append(a, String.append("v", String.append(d, String.append(AiText.sp_beta(m), b)))), e), (hl, r))))))

def aita.go_or(+xc: U32, +t: String, +st: Bool, c: Bool, ec: {P.pm.and(st, w => T.ver(SCon{Chr{xc}, t})) == c : Bool}, h: {P.pm.or(c, v => T.api.go(t, U32.is_eq(xc, 47))) == True{} : Bool}, ih: {T.api.go(t, U32.is_eq(xc, 47)) == True{} : Bool} -> aita.GS(t, U32.is_eq(xc, 47))) -> aita.GS(SCon{Chr{xc}, t}, st):
  match c:
    case True{}:
      aita.here(st, SCon{Chr{xc}, t}, ec)
    case False{}:
      aita.next(xc, t, st, ih(h))

# a hit of the walk is a version part after a place that ends with `/`
# (or the start, with the start flag)
def aita.go_sound(s: String, +st: Bool, h: {T.api.go(s, st) == True{} : Bool}) -> aita.GS(s, st):
  match s:
    case SNil{}:
      LA.mnb.absurd_f(aita.GS(SNil{}, st), h)
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          aita.go_or(xc, t, st, P.pm.and(st, w => T.ver(SCon{Chr{xc}, t})), {==}, h, e => aita.go_sound(t, U32.is_eq(xc, 47), e))
