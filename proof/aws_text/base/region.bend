# eukhe: lemmas of the aws_text proofs: R4 the region of an endpoint host
# and R5 of an ARN. The run of region chars at the start of a text is taken
# off whole (awr.split, awr.take_app, awr.drop_app); each stage of the code
# answers Some only for the spelling the laws state (awr.EP, awr.ARP).

import Base
import ../../../bend/model_name.bend as M
import ../../../bend/phrase.bend as P
import ../../../bend/aws_text.bend as A
import ../../../laws/aws_text.bend as AwsText
import ../../model_name/base.bend as LA
import ../base.bend as LB

# The run of region chars
# -----------------------

# s opens with no region char
def awr.nlc(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{x, t}:
      Bool.not(AwsText.sp_lc(x))

def awr.take_app(r: String, +z: String, hr: {AwsText.sp_lcs0(r) == True{} : Bool}, hz: {awr.nlc(z) == True{} : Bool}) -> {A.lc.take(String.append(r, z)) == r : String}:
  match r:
    case SNil{}:
      match z:
        case SNil{}:
          {==}
        case SCon{x, +t}:
          match x:
            case Chr{+xc}:
              %Equal.sym(Bool, A.is_lc(Chr{xc}), False{}, LA.mnb.not_t(A.is_lc(Chr{xc}), hz)) : {A.lc.take.at(_, Chr{xc}, u => A.lc.take(t)) == SNil{} : String}
              {==}
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +hh = hr
          %Equal.sym(Bool, A.is_lc(Chr{xc}), True{}, LA.mnb.and_l(A.is_lc(Chr{xc}), AwsText.sp_lcs0(t), hh)) : {A.lc.take.at(_, Chr{xc}, u => A.lc.take(String.append(t, z))) == SCon{Chr{xc}, t} : String}
          LA.mnb.cons_eq(Chr{xc}, A.lc.take(String.append(t, z)), t, awr.take_app(t, z, LA.mnb.and_r(A.is_lc(Chr{xc}), AwsText.sp_lcs0(t), hh), hz))

def awr.drop_app(r: String, +z: String, hr: {AwsText.sp_lcs0(r) == True{} : Bool}, hz: {awr.nlc(z) == True{} : Bool}) -> {A.lc.drop(String.append(r, z)) == z : String}:
  match r:
    case SNil{}:
      match z:
        case SNil{}:
          {==}
        case SCon{x, +t}:
          match x:
            case Chr{+xc}:
              %Equal.sym(Bool, A.is_lc(Chr{xc}), False{}, LA.mnb.not_t(A.is_lc(Chr{xc}), hz)) : {A.lc.drop.at(_, SCon{Chr{xc}, t}, u => A.lc.drop(t)) == SCon{Chr{xc}, t} : String}
              {==}
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +hh = hr
          %Equal.sym(Bool, A.is_lc(Chr{xc}), True{}, LA.mnb.and_l(A.is_lc(Chr{xc}), AwsText.sp_lcs0(t), hh)) : {A.lc.drop.at(_, SCon{Chr{xc}, String.append(t, z)}, u => A.lc.drop(String.append(t, z))) == z : String}
          awr.drop_app(t, z, LA.mnb.and_r(A.is_lc(Chr{xc}), AwsText.sp_lcs0(t), hh), hz)

def awr.LT(s: String) -> Type:
  {s == String.append(A.lc.take(s), A.lc.drop(s)) : String} & ({AwsText.sp_lcs0(A.lc.take(s)) == True{} : Bool} & {awr.nlc(A.lc.drop(s)) == True{} : Bool})

def awr.split_at(+xc: U32, +t: String, b: Bool, eb: {A.is_lc(Chr{xc}) == b : Bool}, ih: awr.LT(t)) -> {SCon{Chr{xc}, t} == String.append(A.lc.take.at(b, Chr{xc}, u => A.lc.take(t)), A.lc.drop.at(b, SCon{Chr{xc}, t}, u => A.lc.drop(t))) : String} & ({AwsText.sp_lcs0(A.lc.take.at(b, Chr{xc}, u => A.lc.take(t))) == True{} : Bool} & {awr.nlc(A.lc.drop.at(b, SCon{Chr{xc}, t}, u => A.lc.drop(t))) == True{} : Bool}):
  match b:
    case True{}:
      (e, (l, n)) = ih
      (LA.mnb.cons_eq(Chr{xc}, t, String.append(A.lc.take(t), A.lc.drop(t)), e), (LA.mnb.and_t(A.is_lc(Chr{xc}), AwsText.sp_lcs0(A.lc.take(t)), eb, l), n))
    case False{}:
      ({==}, ({==}, LA.mnb.not_f(A.is_lc(Chr{xc}), eb)))

# every text is its run of region chars, then a rest that opens with none
def awr.split(s: String) -> awr.LT(s):
  match s:
    case SNil{}:
      ({==}, ({==}, {==}))
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          awr.split_at(xc, t, A.is_lc(Chr{xc}), {==}, awr.split(t))

def awr.lcs_of(r: String, l: {AwsText.sp_lcs0(r) == True{} : Bool}, ne: {Bool.not(String.is_empty(r)) == True{} : Bool}) -> {AwsText.sp_lcs(r) == True{} : Bool}:
  match r:
    case SNil{}:
      LA.mnb.absurd_f({AwsText.sp_lcs(SNil{}) == True{} : Bool}, ne)
    case SCon{x, t}:
      l

# R4: the endpoint, complete
# --------------------------

def awr.region_ep(r: String, c: Bool, +hr: {AwsText.sp_lcs(r) == True{} : Bool}) -> {A.ep.region(String.append(r, String.append(".amazonaws.com", AwsText.sp_cn(c)))) == Some{r} : Maybe<&2, String>}:
  match r:
    case SNil{}:
      LA.mnb.absurd_f({A.ep.region(String.append(SNil{}, String.append(".amazonaws.com", AwsText.sp_cn(c)))) == Some{SNil{}} : Maybe<&2, String>}, hr)
    case SCon{+x, +t}:
      match c:
        case True{}:
          +z = String.append(".amazonaws.com", ".cn")
          +s = String.append(SCon{x, t}, z)
          %Equal.sym(String, A.lc.take(s), SCon{x, t}, awr.take_app(SCon{x, t}, z, hr, {==})) : {A.found(Bool.and(Bool.not(String.is_empty(_)), P.pm.or(M.got_all(M.strip(".amazonaws.com", A.lc.drop(s))), u => M.got_all(M.strip(".amazonaws.com.cn", A.lc.drop(s))))), _) == Some{SCon{x, t}} : Maybe<&2, String>}
          %Equal.sym(String, A.lc.drop(s), z, awr.drop_app(SCon{x, t}, z, hr, {==})) : {A.found(Bool.and(Bool.not(String.is_empty(SCon{x, t})), P.pm.or(M.got_all(M.strip(".amazonaws.com", _)), u => M.got_all(M.strip(".amazonaws.com.cn", _)))), SCon{x, t}) == Some{SCon{x, t}} : Maybe<&2, String>}
          {==}
        case False{}:
          +z = String.append(".amazonaws.com", "")
          +s = String.append(SCon{x, t}, z)
          %Equal.sym(String, A.lc.take(s), SCon{x, t}, awr.take_app(SCon{x, t}, z, hr, {==})) : {A.found(Bool.and(Bool.not(String.is_empty(_)), P.pm.or(M.got_all(M.strip(".amazonaws.com", A.lc.drop(s))), u => M.got_all(M.strip(".amazonaws.com.cn", A.lc.drop(s))))), _) == Some{SCon{x, t}} : Maybe<&2, String>}
          %Equal.sym(String, A.lc.drop(s), z, awr.drop_app(SCon{x, t}, z, hr, {==})) : {A.found(Bool.and(Bool.not(String.is_empty(SCon{x, t})), P.pm.or(M.got_all(M.strip(".amazonaws.com", _)), u => M.got_all(M.strip(".amazonaws.com.cn", _)))), SCon{x, t}) == Some{SCon{x, t}} : Maybe<&2, String>}
          {==}

# R4: the endpoint, sound
# -----------------------

def awr.RG(s: String, m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{r}:
      Sigma<&1, &1, Bool, c => {s == String.append(r, String.append(".amazonaws.com", AwsText.sp_cn(c))) : String} & {AwsText.sp_lcs(r) == True{} : Bool}>

def awr.reg_at(+s: String, ne: Bool, ene: {Bool.not(String.is_empty(A.lc.take(s))) == ne : Bool}, a1: Bool, v1: LB.awb.AllP(".amazonaws.com", A.lc.drop(s), a1), a2: Bool, v2: LB.awb.AllP(".amazonaws.com.cn", A.lc.drop(s), a2), lt: awr.LT(s)) -> awr.RG(s, A.found(Bool.and(ne, P.pm.or(a1, u => a2)), A.lc.take(s))):
  match ne:
    case True{}:
      match a1:
        case True{}:
          (e, (l, n)) = lt
          (False{}, (Equal.trans(String, s, String.append(A.lc.take(s), A.lc.drop(s)), String.append(A.lc.take(s), ".amazonaws.com"), e, Equal.cong(String, String, z => String.append(A.lc.take(s), z), A.lc.drop(s), ".amazonaws.com", v1)), awr.lcs_of(A.lc.take(s), l, ene)))
        case False{}:
          match a2:
            case True{}:
              (e, (l, n)) = lt
              (True{}, (Equal.trans(String, s, String.append(A.lc.take(s), A.lc.drop(s)), String.append(A.lc.take(s), ".amazonaws.com.cn"), e, Equal.cong(String, String, z => String.append(A.lc.take(s), z), A.lc.drop(s), ".amazonaws.com.cn", v2)), awr.lcs_of(A.lc.take(s), l, ene)))
            case False{}:
              Unit{}
    case False{}:
      Unit{}

# what ep.region answers is a run of region chars, then the suffix
def awr.region_sp(+s: String) -> awr.RG(s, A.ep.region(s)):
  +d = A.lc.drop(s)
  awr.reg_at(s, Bool.not(String.is_empty(A.lc.take(s))), {==}, M.got_all(M.strip(".amazonaws.com", d)), LB.awb.all_sp(".amazonaws.com", d, M.strip(".amazonaws.com", d), LA.mnb.sp(".amazonaws.com", d)), M.got_all(M.strip(".amazonaws.com.cn", d)), LB.awb.all_sp(".amazonaws.com.cn", d, M.strip(".amazonaws.com.cn", d), LA.mnb.sp(".amazonaws.com.cn", d)), awr.split(s))

def awr.EP(host: String, m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{r}:
      Sigma<&1, &1, Bool, f => Sigma<&1, &1, Bool, c => {host == AwsText.sp_host(f, r, c) : String} & {AwsText.sp_lcs(r) == True{} : Bool}>>

def awr.ep_fin(-host: String, +f: Bool, +s: String, pre: {host == String.append("bedrock-runtime", String.append(AwsText.sp_fips(f), String.append(".", s))) : String}, m: Maybe<&2, String>, rg: awr.RG(s, m)) -> awr.EP(host, m):
  match m:
    case None{}:
      Unit{}
    case Some{+r}:
      (+c, (e, l)) = rg
      (f, (c, (Equal.trans(String, host, String.append("bedrock-runtime", String.append(AwsText.sp_fips(f), String.append(".", s))), AwsText.sp_host(f, r, c), pre, Equal.cong(String, String, z => String.append("bedrock-runtime", String.append(AwsText.sp_fips(f), String.append(".", z))), s, String.append(r, String.append(".amazonaws.com", AwsText.sp_cn(c))), e)), l)))

def awr.ep_fips(-host: String, +r1: String, pre: {host == String.append("bedrock-runtime", r1) : String}, m2: Maybe<&2, String>, v2: LA.mnb.SP("-fips.", r1, m2)) -> awr.EP(host, A.ep.fips(m2)):
  match m2:
    case None{}:
      Unit{}
    case Some{+s}:
      awr.ep_fin(host, True{}, s, Equal.trans(String, host, String.append("bedrock-runtime", r1), String.append("bedrock-runtime", String.append("-fips.", s)), pre, Equal.cong(String, String, z => String.append("bedrock-runtime", z), r1, String.append("-fips.", s), v2)), A.ep.region(s), awr.region_sp(s))

def awr.ep_dot(-host: String, +r1: String, pre: {host == String.append("bedrock-runtime", r1) : String}, m1: Maybe<&2, String>, v1: LA.mnb.SP(".", r1, m1)) -> awr.EP(host, A.ep.dot(m1, u => A.ep.fips(M.strip("-fips.", r1)))):
  match m1:
    case None{}:
      awr.ep_fips(host, r1, pre, M.strip("-fips.", r1), LA.mnb.sp("-fips.", r1))
    case Some{+s}:
      awr.ep_fin(host, False{}, s, Equal.trans(String, host, String.append("bedrock-runtime", r1), String.append("bedrock-runtime", String.append(".", s)), pre, Equal.cong(String, String, z => String.append("bedrock-runtime", z), r1, String.append(".", s), v1)), A.ep.region(s), awr.region_sp(s))

# what endpoint answers is the region of a standard endpoint host
def awr.ep_after(+host: String, m0: Maybe<&2, String>, v0: LA.mnb.SP("bedrock-runtime", host, m0)) -> awr.EP(host, A.ep.after(m0)):
  match m0:
    case None{}:
      Unit{}
    case Some{+r1}:
      awr.ep_dot(host, r1, v0, M.strip(".", r1), LA.mnb.sp(".", r1))

# R5: the ARN, complete
# ---------------------

def awr.region_arn(r: String, +rest: String, +hr: {AwsText.sp_lcs(r) == True{} : Bool}) -> {A.arn.region(String.append(r, String.append(":", rest))) == Some{r} : Maybe<&2, String>}:
  match r:
    case SNil{}:
      LA.mnb.absurd_f({A.arn.region(String.append(SNil{}, String.append(":", rest))) == Some{SNil{}} : Maybe<&2, String>}, hr)
    case SCon{+x, +t}:
      +z = String.append(":", rest)
      +s = String.append(SCon{x, t}, z)
      %Equal.sym(String, A.lc.take(s), SCon{x, t}, awr.take_app(SCon{x, t}, z, hr, {==})) : {A.found(Bool.and(Bool.not(String.is_empty(_)), M.got(M.strip(":", A.lc.drop(s)))), _) == Some{SCon{x, t}} : Maybe<&2, String>}
      %Equal.sym(String, A.lc.drop(s), z, awr.drop_app(SCon{x, t}, z, hr, {==})) : {A.found(Bool.and(Bool.not(String.is_empty(SCon{x, t})), M.got(M.strip(":", _))), SCon{x, t}) == Some{SCon{x, t}} : Maybe<&2, String>}
      {==}

def awr.part_arn(x: String, +r: String, +rest: String, +hx: {AwsText.sp_lcs(x) == True{} : Bool}, hr: {AwsText.sp_lcs(r) == True{} : Bool}) -> {A.arn.part(String.append(x, String.append(":bedrock:", String.append(r, String.append(":", rest))))) == Some{r} : Maybe<&2, String>}:
  match x:
    case SNil{}:
      LA.mnb.absurd_f({A.arn.part(String.append(SNil{}, String.append(":bedrock:", String.append(r, String.append(":", rest))))) == Some{r} : Maybe<&2, String>}, hx)
    case SCon{+y, +t}:
      +z = String.append(":bedrock:", String.append(r, String.append(":", rest)))
      +s = String.append(SCon{y, t}, z)
      %Equal.sym(String, A.lc.take(s), SCon{y, t}, awr.take_app(SCon{y, t}, z, hx, {==})) : {A.arn.part.at(String.is_empty(_), u => A.arn.bedrock(M.strip(":bedrock:", A.lc.drop(s)))) == Some{r} : Maybe<&2, String>}
      %Equal.sym(String, A.lc.drop(s), z, awr.drop_app(SCon{y, t}, z, hx, {==})) : {A.arn.part.at(String.is_empty(SCon{y, t}), u => A.arn.bedrock(M.strip(":bedrock:", _))) == Some{r} : Maybe<&2, String>}
      %Equal.sym(Maybe<&2, String>, M.strip(":bedrock:", z), Some{String.append(r, String.append(":", rest))}, LA.mnb.strip_app(":bedrock:", String.append(r, String.append(":", rest)))) : {A.arn.part.at(False{}, u => A.arn.bedrock(_)) == Some{r} : Maybe<&2, String>}
      awr.region_arn(r, rest, hr)

# R5: the ARN, sound
# ------------------

def awr.RA(s: String, m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{r}:
      Sigma<&1, &1, String, rest => {s == String.append(r, String.append(":", rest)) : String} & {AwsText.sp_lcs(r) == True{} : Bool}>

def awr.ra_at(+s: String, ne: Bool, ene: {Bool.not(String.is_empty(A.lc.take(s))) == ne : Bool}, m: Maybe<&2, String>, v: LA.mnb.SP(":", A.lc.drop(s), m), lt: awr.LT(s)) -> awr.RA(s, A.found(Bool.and(ne, M.got(m)), A.lc.take(s))):
  match ne:
    case True{}:
      match m:
        case None{}:
          Unit{}
        case Some{+rest}:
          (e, (l, n)) = lt
          (rest, (Equal.trans(String, s, String.append(A.lc.take(s), A.lc.drop(s)), String.append(A.lc.take(s), String.append(":", rest)), e, Equal.cong(String, String, z => String.append(A.lc.take(s), z), A.lc.drop(s), String.append(":", rest), v)), awr.lcs_of(A.lc.take(s), l, ene)))
    case False{}:
      Unit{}

# what arn.region answers is a run of region chars, then `:`
def awr.ra_sp(+s: String) -> awr.RA(s, A.arn.region(s)):
  awr.ra_at(s, Bool.not(String.is_empty(A.lc.take(s))), {==}, M.strip(":", A.lc.drop(s)), LA.mnb.sp(":", A.lc.drop(s)), awr.split(s))

def awr.ARP(id: String, m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{r}:
      Sigma<&1, &1, Maybe<&2, String>, a => Sigma<&1, &1, String, rest => {id == AwsText.sp_arn(a, r, rest) : String} & ({AwsText.sp_acct_ok(a) == True{} : Bool} & {AwsText.sp_lcs(r) == True{} : Bool})>>

def awr.ar_fin(-id: String, +a: Maybe<&2, String>, ha: {AwsText.sp_acct_ok(a) == True{} : Bool}, +s: String, pre: {id == String.append("arn:", String.append(AwsText.sp_acct(a), String.append(":bedrock:", s))) : String}, m: Maybe<&2, String>, ra: awr.RA(s, m)) -> awr.ARP(id, m):
  match m:
    case None{}:
      Unit{}
    case Some{+r}:
      (+rest, (e, l)) = ra
      (a, (rest, (Equal.trans(String, id, String.append("arn:", String.append(AwsText.sp_acct(a), String.append(":bedrock:", s))), AwsText.sp_arn(a, r, rest), pre, Equal.cong(String, String, z => String.append("arn:", String.append(AwsText.sp_acct(a), String.append(":bedrock:", z))), s, String.append(r, String.append(":", rest)), e)), (ha, l))))

def awr.ar_bed(-id: String, +x: String, hx: {AwsText.sp_lcs(x) == True{} : Bool}, +d: String, pre: {id == String.append("arn:aws", String.append("-", String.append(x, d))) : String}, m: Maybe<&2, String>, v: LA.mnb.SP(":bedrock:", d, m)) -> awr.ARP(id, A.arn.bedrock(m)):
  match m:
    case None{}:
      Unit{}
    case Some{+s}:
      awr.ar_fin(id, Some{x}, hx, s, Equal.trans(String, id, String.append("arn:aws", String.append("-", String.append(x, d))), String.append("arn:aws", String.append("-", String.append(x, String.append(":bedrock:", s)))), pre, Equal.cong(String, String, z => String.append("arn:aws", String.append("-", String.append(x, z))), d, String.append(":bedrock:", s), v)), A.arn.region(s), awr.ra_sp(s))

def awr.ar_part(-id: String, +r3: String, pre: {id == String.append("arn:aws", String.append("-", r3)) : String}, e: Bool, ee: {String.is_empty(A.lc.take(r3)) == e : Bool}, lt: awr.LT(r3)) -> awr.ARP(id, A.arn.part.at(e, u => A.arn.bedrock(M.strip(":bedrock:", A.lc.drop(r3))))):
  match e:
    case True{}:
      Unit{}
    case False{}:
      (es, (l, n)) = lt
      +x = A.lc.take(r3)
      +d = A.lc.drop(r3)
      +pre2 = Equal.trans(String, id, String.append("arn:aws", String.append("-", r3)), String.append("arn:aws", String.append("-", String.append(x, d))), pre, Equal.cong(String, String, z => String.append("arn:aws", String.append("-", z)), r3, String.append(x, d), es))
      awr.ar_bed(id, x, awr.lcs_of(x, l, LA.mnb.not_f(String.is_empty(x), ee)), d, pre2, M.strip(":bedrock:", d), LA.mnb.sp(":bedrock:", d))

def awr.ar_dash(-id: String, +r1: String, pre: {id == String.append("arn:aws", r1) : String}, m: Maybe<&2, String>, v: LA.mnb.SP("-", r1, m)) -> awr.ARP(id, A.arn.dash(m)):
  match m:
    case None{}:
      Unit{}
    case Some{+r3}:
      awr.ar_part(id, r3, Equal.trans(String, id, String.append("arn:aws", r1), String.append("arn:aws", String.append("-", r3)), pre, Equal.cong(String, String, z => String.append("arn:aws", z), r1, String.append("-", r3), v)), String.is_empty(A.lc.take(r3)), {==}, awr.split(r3))

def awr.ar_colon(-id: String, +r1: String, pre: {id == String.append("arn:aws", r1) : String}, m: Maybe<&2, String>, v: LA.mnb.SP(":bedrock:", r1, m)) -> awr.ARP(id, A.arn.colon(m, u => A.arn.dash(M.strip("-", r1)))):
  match m:
    case None{}:
      awr.ar_dash(id, r1, pre, M.strip("-", r1), LA.mnb.sp("-", r1))
    case Some{+s}:
      awr.ar_fin(id, None{}, {==}, s, Equal.trans(String, id, String.append("arn:aws", r1), String.append("arn:aws", String.append(":bedrock:", s)), pre, Equal.cong(String, String, z => String.append("arn:aws", z), r1, String.append(":bedrock:", s), v)), A.arn.region(s), awr.ra_sp(s))

# what arn answers is the region of a Bedrock ARN
def awr.ar_after(+id: String, m0: Maybe<&2, String>, v0: LA.mnb.SP("arn:aws", id, m0)) -> awr.ARP(id, A.arn.after(m0)):
  match m0:
    case None{}:
      Unit{}
    case Some{+r1}:
      awr.ar_colon(id, r1, v0, M.strip(":bedrock:", r1), LA.mnb.sp(":bedrock:", r1))
