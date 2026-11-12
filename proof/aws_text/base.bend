# eukhe: lemmas shared by the proofs of area aws_text: R1 the shape of a
# region (awb.w_*, awb.shape_app, awb.ss_*), R2 the request-id header
# (awb.rid_*). The prefix strip and the logic come from
# proof/model_name/base.bend.

import Base
import ../../bend/text_pat.bend as Tp
import ../../bend/phrase.bend as P
import ../../bend/model_name.bend as M
import ../../bend/aws_text.bend as A
import ../../laws/model_name.bend as ModelName
import ../../laws/phrase.bend as Phrase
import ../../laws/aws_text.bend as AwsText
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../model_name/base.bend as LA

# R1: the digits of a region's number
# ----------------------------------

def awb.n_true(s: String) -> {A.shape.n(s, True{}) == ModelName.sp_digits(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          LA.mnb.and2(Tp.is_dig(Chr{xc}), A.shape.n(t, True{}), ModelName.sp_digits(t), awb.n_true(t))

def awb.n_false(s: String) -> {A.shape.n(s, False{}) == AwsText.sp_digs(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          LA.mnb.and2(Tp.is_dig(Chr{xc}), A.shape.n(t, True{}), ModelName.sp_digits(t), awb.n_true(t))

# R1: the shape, sound
# --------------------

def awb.WP(s: String, seen: Bool, v: Bool) -> Type:
  match v:
    case True{}:
      Sigma<&1, &1, String, w => Sigma<&1, &1, String, n => {s == String.append(w, String.append("-", n)) : String} & ({AwsText.sp_words0(w) == True{} : Bool} & ({Bool.or(seen, Bool.not(String.is_empty(w))) == True{} : Bool} & {AwsText.sp_digs(n) == True{} : Bool}))>>
    case False{}:
      Unit

def awb.w_n(+xc: U32, +t: String, ee: {U32.is_eq(xc, 45) == True{} : Bool}, c: Bool, ec: {A.shape.n(t, False{}) == c : Bool}) -> awb.WP(SCon{Chr{xc}, t}, True{}, c):
  match c:
    case True{}:
      +ed = Equal.trans(Bool, AwsText.sp_digs(t), A.shape.n(t, False{}), True{}, Equal.sym(Bool, A.shape.n(t, False{}), AwsText.sp_digs(t), awb.n_false(t)), ec)
      (SNil{}, (t, (Equal.cong(U32, String, v => SCon{Chr{v}, t}, xc, 45, PWireBoolExact.wr_eq_sound(xc, 45, ee)), ({==}, ({==}, ed)))))
    case False{}:
      Unit{}

def awb.w_e(+xc: U32, +t: String, e: Bool, ee: {U32.is_eq(xc, 45) == e : Bool}) -> awb.WP(SCon{Chr{xc}, t}, True{}, P.pm.and(e, z => A.shape.n(t, False{}))):
  match e:
    case True{}:
      awb.w_n(xc, t, ee, A.shape.n(t, False{}), {==})
    case False{}:
      Unit{}

def awb.w_seen(+xc: U32, +t: String, seen: Bool) -> awb.WP(SCon{Chr{xc}, t}, seen, P.pm.and(seen, w => P.pm.and(U32.is_eq(xc, 45), z => A.shape.n(t, False{})))):
  match seen:
    case True{}:
      awb.w_e(xc, t, U32.is_eq(xc, 45), {==})
    case False{}:
      Unit{}

def awb.w_word(+xc: U32, -t: String, +seen: Bool, eg: {P.is_word(Chr{xc}) == True{} : Bool}, v: Bool, ih: awb.WP(t, True{}, v)) -> awb.WP(SCon{Chr{xc}, t}, seen, v):
  match v:
    case True{}:
      (+w, (+n, (e, (ws, (sn, dn))))) = ih
      (SCon{Chr{xc}, w}, (n, (LA.mnb.cons_eq(Chr{xc}, t, String.append(w, String.append("-", n)), e), (LA.mnb.and_t(P.is_word(Chr{xc}), AwsText.sp_words0(w), eg, ws), (LA.mnb.or_rt(seen, True{}, {==}), dn)))))
    case False{}:
      Unit{}

def awb.w_at(+xc: U32, +t: String, +seen: Bool, g: Bool, eg: {P.is_word(Chr{xc}) == g : Bool}, ih: awb.WP(t, True{}, A.shape.w(t, True{}))) -> awb.WP(SCon{Chr{xc}, t}, seen, M.ite(g, u => A.shape.w(t, True{}), v => P.pm.and(seen, w => P.pm.and(U32.is_eq(xc, 45), z => A.shape.n(t, False{}))))):
  match g:
    case True{}:
      awb.w_word(xc, t, seen, eg, A.shape.w(t, True{}), ih)
    case False{}:
      awb.w_seen(xc, t, seen)

# what shape.w accepts is W, `-`, N
def awb.w_sp(s: String, +seen: Bool) -> awb.WP(s, seen, A.shape.w(s, seen)):
  match s:
    case SNil{}:
      Unit{}
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          awb.w_at(xc, t, seen, P.is_word(Chr{xc}), {==}, awb.w_sp(t, True{}))

def awb.wp_true(+r0: String, h: {A.shape.w(r0, False{}) == True{} : Bool}) -> awb.WP(r0, False{}, True{}):
  %h : awb.WP(r0, False{}, _)
  awb.w_sp(r0, False{})

def awb.words_of(w: String, ws: {AwsText.sp_words0(w) == True{} : Bool}, sn: {Bool.or(False{}, Bool.not(String.is_empty(w))) == True{} : Bool}) -> {AwsText.sp_words(w) == True{} : Bool}:
  match w:
    case SNil{}:
      LA.mnb.absurd_f({AwsText.sp_words(SNil{}) == True{} : Bool}, sn)
    case SCon{x, t}:
      ws

def awb.SS(p: String, r: String) -> Type:
  Sigma<&1, &1, String, w => Sigma<&1, &1, String, n => {r == String.append(p, String.append("-", String.append(w, String.append("-", n)))) : String} & ({AwsText.sp_words(w) == True{} : Bool} & {AwsText.sp_digs(n) == True{} : Bool})>>

def awb.ss_fin(+p: String, -r: String, +r0: String, v: {r == String.append(String.append(p, "-"), r0) : String}, wp: awb.WP(r0, False{}, True{})) -> awb.SS(p, r):
  (+w, (+n, (e, (ws, (sn, dn))))) = wp
  +e1 = Equal.trans(String, r, String.append(String.append(p, "-"), r0), String.append(p, String.append("-", r0)), v, LA.mnb.app_assoc(p, "-", r0))
  +e2 = Equal.trans(String, r, String.append(p, String.append("-", r0)), String.append(p, String.append("-", String.append(w, String.append("-", n)))), e1, Equal.cong(String, String, z => String.append(p, String.append("-", z)), r0, String.append(w, String.append("-", n)), e))
  (w, (n, (e2, (awb.words_of(w, ws, sn), dn))))

def awb.ss_m(+p: String, -r: String, m: Maybe<&2, String>, v: LA.mnb.SP(String.append(p, "-"), r, m), h: {A.shape.on(m) == True{} : Bool}) -> awb.SS(p, r):
  match m:
    case None{}:
      LA.mnb.absurd_f(awb.SS(p, r), h)
    case Some{+r0}:
      awb.ss_fin(p, r, r0, v, awb.wp_true(r0, h))

# R1: the shape, complete
# -----------------------

def awb.w_app(w: String, +n: String, +seen: Bool, hw: {AwsText.sp_words0(w) == True{} : Bool}, hs: {Bool.or(seen, Bool.not(String.is_empty(w))) == True{} : Bool}, hn: {AwsText.sp_digs(n) == True{} : Bool}) -> {A.shape.w(String.append(w, String.append("-", n)), seen) == True{} : Bool}:
  match w:
    case SNil{}:
      match seen:
        case True{}:
          Equal.trans(Bool, A.shape.n(n, False{}), AwsText.sp_digs(n), True{}, awb.n_false(n), hn)
        case False{}:
          LA.mnb.absurd_f({A.shape.w(String.append("-", n), False{}) == True{} : Bool}, hs)
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +hh = hw
          %Equal.sym(Bool, P.is_word(Chr{xc}), True{}, LA.mnb.and_l(P.is_word(Chr{xc}), AwsText.sp_words0(t), hh)) : {M.ite(_, u => A.shape.w(String.append(t, String.append("-", n)), True{}), v => P.pm.and(seen, w2 => P.pm.and(U32.is_eq(xc, 45), z => A.shape.n(String.append(t, String.append("-", n)), False{})))) == True{} : Bool}
          awb.w_app(t, n, True{}, LA.mnb.and_r(P.is_word(Chr{xc}), AwsText.sp_words0(t), hh), {==}, hn)

def awb.shape_app(+p: String, w: String, +n: String, hw: {AwsText.sp_words(w) == True{} : Bool}, hn: {AwsText.sp_digs(n) == True{} : Bool}) -> {A.shape(p, String.append(p, String.append("-", String.append(w, String.append("-", n))))) == True{} : Bool}:
  match w:
    case SNil{}:
      LA.mnb.absurd_f({A.shape(p, String.append(p, String.append("-", String.append(SNil{}, String.append("-", n))))) == True{} : Bool}, hw)
    case SCon{+x, +t}:
      +y = String.append(SCon{x, t}, String.append("-", n))
      %LA.mnb.app_assoc(p, "-", y) : {A.shape.on(M.strip(String.append(p, "-"), _)) == True{} : Bool}
      %Equal.sym(Maybe<&2, String>, M.strip(String.append(p, "-"), String.append(String.append(p, "-"), y)), Some{y}, LA.mnb.strip_app(String.append(p, "-"), y)) : {A.shape.on(_) == True{} : Bool}
      awb.w_app(SCon{x, t}, n, False{}, hw, {==}, hn)

# R2: the request-id header, complete
# -----------------------------------

def awb.rid_app(m: String, +k: Bool, +seen: Bool, hm: {AwsText.sp_wds0(m) == True{} : Bool}, hs: {Bool.or(seen, Bool.not(String.is_empty(m))) == True{} : Bool}) -> {A.rid.go(String.append(m, AwsText.sp_rid_tail(k)), seen) == True{} : Bool}:
  match m:
    case SNil{}:
      match k:
        case True{}:
          match seen:
            case True{}:
              {==}
            case False{}:
              LA.mnb.absurd_f({A.rid.go(AwsText.sp_rid_tail(True{}), False{}) == True{} : Bool}, hs)
        case False{}:
          match seen:
            case True{}:
              {==}
            case False{}:
              LA.mnb.absurd_f({A.rid.go(AwsText.sp_rid_tail(False{}), False{}) == True{} : Bool}, hs)
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +hh = hm
          +y = String.append(t, AwsText.sp_rid_tail(k))
          LA.mnb.or_rl(P.pm.and(seen, v => A.rid.tail(SCon{Chr{xc}, y})), P.pm.and(A.is_wd(Chr{xc}), w => A.rid.go(y, True{})), LA.mnb.and_lt(A.is_wd(Chr{xc}), A.rid.go(y, True{}), LA.mnb.and_l(A.is_wd(Chr{xc}), AwsText.sp_wds0(t), hh), awb.rid_app(t, k, True{}, LA.mnb.and_r(A.is_wd(Chr{xc}), AwsText.sp_wds0(t), hh), {==})))

# R2: the request-id header, sound
# --------------------------------

def awb.AllP(p: String, s: String, b: Bool) -> Type:
  match b:
    case True{}:
      {s == p : String}
    case False{}:
      Unit

def awb.all_some(+p: String, -s: String, r: String, v: {s == String.append(p, r) : String}) -> awb.AllP(p, s, String.is_empty(r)):
  match r:
    case SNil{}:
      Equal.trans(String, s, String.append(p, SNil{}), p, v, LA.mnb.app_nil(p))
    case SCon{x, t}:
      Unit{}

def awb.all_sp(+p: String, -s: String, m: Maybe<&2, String>, v: LA.mnb.SP(p, s, m)) -> awb.AllP(p, s, M.got_all(m)):
  match m:
    case None{}:
      Unit{}
    case Some{r}:
      awb.all_some(p, s, r, v)

def awb.TailP(s: String, b: Bool) -> Type:
  match b:
    case True{}:
      Sigma<&1, &1, Bool, k => {s == AwsText.sp_rid_tail(k) : String}>
    case False{}:
      Unit

def awb.tail_or(-s: String, b1: Bool, v1: awb.AllP("-request-id", s, b1), b2: Bool, v2: awb.AllP("-requestid", s, b2)) -> awb.TailP(s, P.pm.or(b1, u => b2)):
  match b1:
    case True{}:
      (True{}, v1)
    case False{}:
      match b2:
        case True{}:
          (False{}, v2)
        case False{}:
          Unit{}

def awb.tail_sp(+s: String) -> awb.TailP(s, A.rid.tail(s)):
  awb.tail_or(s, M.got_all(M.strip("-request-id", s)), awb.all_sp("-request-id", s, M.strip("-request-id", s), LA.mnb.sp("-request-id", s)), M.got_all(M.strip("-requestid", s)), awb.all_sp("-requestid", s, M.strip("-requestid", s), LA.mnb.sp("-requestid", s)))

def awb.RidP(s: String, seen: Bool, v: Bool) -> Type:
  match v:
    case True{}:
      Sigma<&1, &1, String, m => Sigma<&1, &1, Bool, k => {s == String.append(m, AwsText.sp_rid_tail(k)) : String} & ({AwsText.sp_wds0(m) == True{} : Bool} & {Bool.or(seen, Bool.not(String.is_empty(m))) == True{} : Bool})>>
    case False{}:
      Unit

def awb.rid_s1(-s: String, seen: Bool, b: Bool, tp: awb.TailP(s, b)) -> awb.RidP(s, seen, P.pm.and(seen, u => b)):
  match seen:
    case True{}:
      match b:
        case True{}:
          (+k, e) = tp
          (SNil{}, (k, (e, ({==}, {==}))))
        case False{}:
          Unit{}
    case False{}:
      Unit{}

def awb.rid_s2(+xc: U32, -t: String, +seen: Bool, g: Bool, eg: {A.is_wd(Chr{xc}) == g : Bool}, v: Bool, ih: awb.RidP(t, True{}, v)) -> awb.RidP(SCon{Chr{xc}, t}, seen, P.pm.and(g, u => v)):
  match g:
    case True{}:
      match v:
        case True{}:
          (+m, (+k, (e, (ws, sn)))) = ih
          (SCon{Chr{xc}, m}, (k, (LA.mnb.cons_eq(Chr{xc}, t, String.append(m, AwsText.sp_rid_tail(k)), e), (LA.mnb.and_t(A.is_wd(Chr{xc}), AwsText.sp_wds0(m), eg, ws), LA.mnb.or_rt(seen, True{}, {==})))))
        case False{}:
          Unit{}
    case False{}:
      Unit{}

def awb.rid_or(-s: String, -seen: Bool, b1: Bool, v1: awb.RidP(s, seen, b1), b2: Bool, v2: awb.RidP(s, seen, b2)) -> awb.RidP(s, seen, P.pm.or(b1, u => b2)):
  match b1:
    case True{}:
      v1
    case False{}:
      v2

# what rid.go accepts is M, then a tail
def awb.rid_sp(s: String, +seen: Bool) -> awb.RidP(s, seen, A.rid.go(s, seen)):
  match s:
    case SNil{}:
      Unit{}
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +u = {SCon{Chr{xc}, t} : String}
          awb.rid_or(u, seen, P.pm.and(seen, v => A.rid.tail(u)), awb.rid_s1(u, seen, A.rid.tail(u), awb.tail_sp(u)), P.pm.and(A.is_wd(Chr{xc}), w => A.rid.go(t, True{})), awb.rid_s2(xc, t, seen, A.is_wd(Chr{xc}), {==}, A.rid.go(t, True{}), awb.rid_sp(t, True{})))

def awb.wds_of(m: String, ws: {AwsText.sp_wds0(m) == True{} : Bool}, sn: {Bool.or(False{}, Bool.not(String.is_empty(m))) == True{} : Bool}) -> {AwsText.sp_wds(m) == True{} : Bool}:
  match m:
    case SNil{}:
      LA.mnb.absurd_f({AwsText.sp_wds(SNil{}) == True{} : Bool}, sn)
    case SCon{x, t}:
      ws
