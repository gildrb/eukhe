# eukhe: lemmas of the aws_text proofs: R6 without_fips. Where no FIPS
# part begins, the cut answers none (awf.cut_none); where one begins, the
# longest cut that stands there is taken off (awf.cut_at); a cut found at
# the start is the answer (awf.at_some).

import Base
import ../../../bend/model_name.bend as M
import ../../../bend/aws_text.bend as A
import ../../../laws/model_name.bend as ModelName
import ../../../laws/aws_text.bend as AwsText
import ../../model_name/base.bend as LA
import ../../model_name/base/decide.bend as LD

def awf.none_m(m: Maybe<&2, String>, h: {M.got(m) == False{} : Bool}) -> {m == None{} : Maybe<&2, String>}:
  match m:
    case None{}:
      {==}
    case Some{r}:
      LA.mnb.absurd({Some{r} == None{} : Maybe<&2, String>}, h)

# a prefix the spec refuses strips off as none
def awf.strip_none(+p: String, +u: String, h: {ModelName.sp_pre(p, u) == False{} : Bool}) -> {M.strip(p, u) == None{} : Maybe<&2, String>}:
  awf.none_m(M.strip(p, u), Equal.trans(Bool, M.got(M.strip(p, u)), ModelName.sp_pre(p, u), False{}, LD.mnd.got_pre(p, u), h))

# where no FIPS part begins, nothing is cut
def awf.cut_none(+u: String, h: {AwsText.sp_begins(u) == False{} : Bool}) -> {A.fips.cut(u) == None{} : Maybe<&2, String>}:
  +hh = h
  +n1 = awf.strip_none("fips-", u, LA.mnb.or_fl(ModelName.sp_pre("fips-", u), ModelName.sp_pre("-fips", u), hh))
  +n2 = awf.strip_none("-fips", u, LA.mnb.or_fr(ModelName.sp_pre("fips-", u), ModelName.sp_pre("-fips", u), hh))
  %Equal.sym(Maybe<&2, String>, M.strip("fips-", u), None{}, n1) : {A.fips.first(_, u) == None{} : Maybe<&2, String>}
  n2

# after `fips-`, with no `dkr-` or `prod-` standing, the rest is kept
def awf.tail(+r: String, hk: {Bool.and(Bool.not(ModelName.sp_pre("dkr-", r)), Bool.not(ModelName.sp_pre("prod-", r))) == True{} : Bool}) -> {A.fips.tail(r) == r : String}:
  +hh = hk
  +d = LA.mnb.not_t(ModelName.sp_pre("dkr-", r), LA.mnb.and_l(Bool.not(ModelName.sp_pre("dkr-", r)), Bool.not(ModelName.sp_pre("prod-", r)), hh))
  +p = LA.mnb.not_t(ModelName.sp_pre("prod-", r), LA.mnb.and_r(Bool.not(ModelName.sp_pre("dkr-", r)), Bool.not(ModelName.sp_pre("prod-", r)), hh))
  %Equal.sym(Maybe<&2, String>, M.strip("dkr-", r), None{}, awf.strip_none("dkr-", r, d)) : {A.fips.longer(_, u => A.fips.longer(M.strip("prod-", r), v => r)) == r : String}
  %Equal.sym(Maybe<&2, String>, M.strip("prod-", r), None{}, awf.strip_none("prod-", r, p)) : {A.fips.longer(None{}, u => A.fips.longer(_, v => r)) == r : String}
  {==}

# the cut k at the start, the longest that stands there, leaves r
def awf.cut_at(k: Nat, +r: String, hk: {AwsText.sp_cut_ok(k, r) == True{} : Bool}) -> {A.fips.cut(String.append(AwsText.sp_cut(k), r)) == Some{r} : Maybe<&2, String>}:
  match k:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      Equal.cong(String, Maybe<&2, String>, z => Some{z}, A.fips.tail(r), r, awf.tail(r, hk))
    case 3n+j:
      {==}

# a cut found at the start of s is the answer
def awf.at_some(s: String, -r: String, e: {A.fips.cut(s) == Some{r} : Maybe<&2, String>}) -> {A.without_fips(s) == r : String}:
  match s:
    case SNil{}:
      LA.mnb.absurd_f({A.without_fips(SNil{}) == r : String}, Equal.cong(Maybe<&2, String>, Bool, m => M.got(m), None{}, Some{r}, e))
    case SCon{+x, +t}:
      %Equal.sym(Maybe<&2, String>, A.fips.cut(SCon{x, t}), Some{r}, e) : {A.fips.at(_, x, u => A.without_fips(t)) == r : String}
      {==}

# a text whose first char begins no FIPS part keeps it
def awf.keep(+x: Char, +t: String, h: {AwsText.sp_begins(SCon{x, t}) == False{} : Bool}) -> {A.without_fips(SCon{x, t}) == SCon{x, A.without_fips(t)} : String}:
  %Equal.sym(Maybe<&2, String>, A.fips.cut(SCon{x, t}), None{}, awf.cut_none(SCon{x, t}, h)) : {A.fips.at(_, x, u => A.without_fips(t)) == SCon{x, A.without_fips(t)} : String}
  {==}

def awf.first(a: String, +k: Nat, +r: String, ha: {AwsText.sp_clear(a, String.append(AwsText.sp_cut(k), r)) == True{} : Bool}, hk: {AwsText.sp_cut_ok(k, r) == True{} : Bool}) -> {A.without_fips(String.append(a, String.append(AwsText.sp_cut(k), r))) == String.append(a, r) : String}:
  match a:
    case SNil{}:
      awf.at_some(String.append(AwsText.sp_cut(k), r), r, awf.cut_at(k, r, hk))
    case SCon{+x, +a2}:
      +hh = ha
      +w = String.append(AwsText.sp_cut(k), r)
      +b = AwsText.sp_begins(SCon{x, String.append(a2, w)})
      %Equal.sym(String, A.without_fips(SCon{x, String.append(a2, w)}), SCon{x, A.without_fips(String.append(a2, w))}, awf.keep(x, String.append(a2, w), LA.mnb.not_t(b, LA.mnb.and_l(Bool.not(b), AwsText.sp_clear(a2, w), hh)))) : {_ == SCon{x, String.append(a2, r)} : String}
      LA.mnb.cons_eq(x, A.without_fips(String.append(a2, w)), String.append(a2, r), awf.first(a2, k, r, LA.mnb.and_r(Bool.not(b), AwsText.sp_clear(a2, w), hh), hk))

def awf.none(s: String, h: {AwsText.sp_clear(s, "") == True{} : Bool}) -> {A.without_fips(s) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      +hh = h
      +b = AwsText.sp_begins(SCon{x, String.append(t, SNil{})})
      +nb = LA.mnb.not_t(b, LA.mnb.and_l(Bool.not(b), AwsText.sp_clear(t, SNil{}), hh))
      +nb2 = Equal.trans(Bool, AwsText.sp_begins(SCon{x, t}), b, False{}, Equal.cong(String, Bool, z => AwsText.sp_begins(SCon{x, z}), t, String.append(t, SNil{}), Equal.sym(String, String.append(t, SNil{}), t, LA.mnb.app_nil(t))), nb)
      %Equal.sym(String, A.without_fips(SCon{x, t}), SCon{x, A.without_fips(t)}, awf.keep(x, t, nb2)) : {_ == SCon{x, t} : String}
      LA.mnb.cons_eq(x, A.without_fips(t), t, awf.none(t, LA.mnb.and_r(Bool.not(b), AwsText.sp_clear(t, SNil{}), hh)))
