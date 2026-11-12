# eukhe: lemmas shared by the proofs of area package_source

import Base
import ../../bend/package_source.bend as Ps
import ../../bend/gateway_answer.bend as Ga
import ../../laws/package_source/model.bend as PackageSource
import ../base/staging.bend as LStg

# Bool
# ----

def psb.not_t(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      LStg.stg.absurdF({True{} == False{} : Bool}, e)
    case False{}:
      {==}

def psb.or_fl(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      LStg.stg.absurd({True{} == False{} : Bool}, e)
    case False{}:
      {==}

def psb.or_fr(a: Bool, b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      LStg.stg.absurd({b == False{} : Bool}, e)
    case False{}:
      e

def psb.and_tt(a: Bool, b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, eb) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

# Whitespace and trimming
# -----------------------

# the code's whitespace test is the laws' White_Space table
def psb.white(+c: Char) -> {Ga.space(c) == PackageSource.ps_white(c) : Bool}:
  {==}

def psb.sp_t(+c: Char, e: {PackageSource.ps_white(c) == True{} : Bool}) -> {Ga.space(c) == True{} : Bool}:
  Equal.trans(Bool, Ga.space(c), PackageSource.ps_white(c), True{}, psb.white(c), e)

def psb.sp_f(+c: Char, e: {PackageSource.ps_white(c) == False{} : Bool}) -> {Ga.space(c) == False{} : Bool}:
  Equal.trans(Bool, Ga.space(c), PackageSource.ps_white(c), False{}, psb.white(c), e)

# leading White_Space is dropped
def psb.lsp_blank(w: String, -y: String, +b: {PackageSource.ps_blank(w) == True{} : Bool}) -> {Ps.lspace(String.append(w, y)) == Ps.lspace(y) : String}:
  match w:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Ga.space(c), True{}, psb.sp_t(c, LStg.stg.and_l(PackageSource.ps_white(c), PackageSource.ps_blank(t), b))) : {Ps.lspace.at(_, c, String.append(t, y), Ps.lspace(String.append(t, y))) == Ps.lspace(y) : String}
      psb.lsp_blank(t, y, LStg.stg.and_r(PackageSource.ps_white(c), PackageSource.ps_blank(t), b))

# a White_Space text drops to nothing
def psb.lsp_nil(w: String, +b: {PackageSource.ps_blank(w) == True{} : Bool}) -> {Ps.lspace(w) == SNil{} : String}:
  match w:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Ga.space(c), True{}, psb.sp_t(c, LStg.stg.and_l(PackageSource.ps_white(c), PackageSource.ps_blank(t), b))) : {Ps.lspace.at(_, c, t, Ps.lspace(t)) == SNil{} : String}
      psb.lsp_nil(t, LStg.stg.and_r(PackageSource.ps_white(c), PackageSource.ps_blank(t), b))

def psb.lsp_app.at(b: Bool, c: Char, t: String, -acc: String, ih: {Ps.lspace(String.append(t, acc)) == String.append(Ps.lspace(t), acc) : String}) -> {Ps.lspace.at(b, c, String.append(t, acc), Ps.lspace(String.append(t, acc))) == String.append(Ps.lspace.at(b, c, t, Ps.lspace(t)), acc) : String}:
  match b:
    case True{}:
      ih
    case False{}:
      {==}

# the drop stops before a char that is not White_Space
def psb.lsp_app(a: String, +d: Char, +r: String, e: {Ga.space(d) == False{} : Bool}) -> {Ps.lspace(String.append(a, SCon{d, r})) == String.append(Ps.lspace(a), SCon{d, r}) : String}:
  match a:
    case SNil{}:
      %Equal.sym(Bool, Ga.space(d), False{}, e) : {Ps.lspace.at(_, d, r, Ps.lspace(r)) == SCon{d, r} : String}
      {==}
    case SCon{+c, +t}:
      psb.lsp_app.at(Ga.space(c), c, t, SCon{d, r}, psb.lsp_app(t, d, r, e))

# Reversal
# --------

def psb.app_assoc(a: String, -b: String, -c: String) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      Equal.cong(String, String, z => SCon{h, z}, String.append(String.append(t, b), c), String.append(t, String.append(b, c)), psb.app_assoc(t, b, c))

def psb.rev_app(a: String, -b: String, -acc: String) -> {String.reverse.go(String.append(a, b), acc) == String.reverse.go(b, String.reverse.go(a, acc)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      psb.rev_app(t, b, SCon{h, acc})

def psb.rev_acc(x: String, -acc: String) -> {String.reverse.go(x, acc) == String.append(String.reverse.go(x, SNil{}), acc) : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      +rt = String.reverse.go(t, SNil{})
      Equal.trans(String, String.reverse.go(t, SCon{h, acc}), String.append(rt, SCon{h, acc}), String.append(String.reverse.go(t, SCon{h, SNil{}}), acc), psb.rev_acc(t, SCon{h, acc}), Equal.trans(String, String.append(rt, SCon{h, acc}), String.append(String.append(rt, SCon{h, SNil{}}), acc), String.append(String.reverse.go(t, SCon{h, SNil{}}), acc), Equal.sym(String, String.append(String.append(rt, SCon{h, SNil{}}), acc), String.append(rt, SCon{h, acc}), psb.app_assoc(rt, SCon{h, SNil{}}, acc)), Equal.cong(String, String, z => String.append(z, acc), String.append(rt, SCon{h, SNil{}}), String.reverse.go(t, SCon{h, SNil{}}), Equal.sym(String, String.reverse.go(t, SCon{h, SNil{}}), String.append(rt, SCon{h, SNil{}}), psb.rev_acc(t, SCon{h, SNil{}})))))

def psb.rr(a: String, -acc: String) -> {String.reverse.go(String.reverse.go(a, acc), SNil{}) == String.reverse.go(acc, a) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      psb.rr(t, SCon{h, acc})

def psb.blank_cons(+c: Char, acc: String, ec: {PackageSource.ps_white(c) == True{} : Bool}, ea: {PackageSource.ps_blank(acc) == True{} : Bool}) -> {PackageSource.ps_blank(SCon{c, acc}) == True{} : Bool}:
  psb.and_tt(PackageSource.ps_white(c), PackageSource.ps_blank(acc), ec, ea)

# a White_Space text turned around onto one is White_Space
def psb.blank_rev(w: String, +acc: String, +bw: {PackageSource.ps_blank(w) == True{} : Bool}, ba: {PackageSource.ps_blank(acc) == True{} : Bool}) -> {PackageSource.ps_blank(String.reverse.go(w, acc)) == True{} : Bool}:
  match w:
    case SNil{}:
      ba
    case SCon{+c, +t}:
      psb.blank_rev(t, SCon{c, acc}, LStg.stg.and_r(PackageSource.ps_white(c), PackageSource.ps_blank(t), bw), psb.blank_cons(c, acc, LStg.stg.and_l(PackageSource.ps_white(c), PackageSource.ps_blank(t), bw), ba))

# Trim
# ----

# w, then P, then x, trimmed: P then x's text without its trailing
# White_Space, when w is White_Space and P neither starts nor ends with it
def psb.trim_pre(+w: String, b: {PackageSource.ps_blank(w) == True{} : Bool}, +p: String, +x: String, ep: {Ps.lspace(String.append(p, x)) == String.append(p, x) : String}, +d: Char, +r: String, +er: {String.reverse(p) == SCon{d, r} : String}, ed: {Ga.space(d) == False{} : Bool}) -> {Ps.trim(String.append(w, String.append(p, x))) == String.append(p, String.reverse(Ps.lspace(String.reverse(x)))) : String}:
  +rx = String.reverse.go(x, SNil{})
  +lrx = Ps.lspace(rx)
  +rhs = String.append(p, String.reverse(lrx))
  %Equal.sym(String, Ps.lspace(String.append(w, String.append(p, x))), Ps.lspace(String.append(p, x)), psb.lsp_blank(w, String.append(p, x), b)) : {String.reverse(Ps.lspace(String.reverse(_))) == rhs : String}
  %Equal.sym(String, Ps.lspace(String.append(p, x)), String.append(p, x), ep) : {String.reverse(Ps.lspace(String.reverse(_))) == rhs : String}
  %Equal.sym(String, String.reverse.go(String.append(p, x), SNil{}), String.reverse.go(x, String.reverse.go(p, SNil{})), psb.rev_app(p, x, SNil{})) : {String.reverse(Ps.lspace(_)) == rhs : String}
  %Equal.sym(String, String.reverse(p), SCon{d, r}, er) : {String.reverse(Ps.lspace(String.reverse.go(x, _))) == rhs : String}
  %Equal.sym(String, String.reverse.go(x, SCon{d, r}), String.append(rx, SCon{d, r}), psb.rev_acc(x, SCon{d, r})) : {String.reverse(Ps.lspace(_)) == rhs : String}
  %Equal.sym(String, Ps.lspace(String.append(rx, SCon{d, r})), String.append(lrx, SCon{d, r}), psb.lsp_app(rx, d, r, ed)) : {String.reverse(_) == rhs : String}
  %Equal.sym(String, String.reverse.go(String.append(lrx, SCon{d, r}), SNil{}), String.reverse.go(SCon{d, r}, String.reverse.go(lrx, SNil{})), psb.rev_app(lrx, SCon{d, r}, SNil{})) : {_ == rhs : String}
  %Equal.sym(String, String.reverse.go(SCon{d, r}, String.reverse.go(lrx, SNil{})), String.append(String.reverse.go(SCon{d, r}, SNil{}), String.reverse.go(lrx, SNil{})), psb.rev_acc(SCon{d, r}, String.reverse.go(lrx, SNil{}))) : {_ == rhs : String}
  %er : {String.append(String.reverse(_), String.reverse(lrx)) == rhs : String}
  %Equal.sym(String, String.reverse.go(String.reverse.go(p, SNil{}), SNil{}), p, psb.rr(p, SNil{})) : {String.append(_, String.reverse(lrx)) == rhs : String}
  {==}

def psb.lt.at(b: Bool, +c: Char, +t: String, +w2: String, b2: {PackageSource.ps_blank(w2) == True{} : Bool}, ih: {Ps.lspace(String.reverse(Ps.lspace(String.append(t, w2)))) == Ps.lspace(String.reverse(Ps.lspace(t))) : String}) -> {Ps.lspace(String.reverse(Ps.lspace.at(b, c, String.append(t, w2), Ps.lspace(String.append(t, w2))))) == Ps.lspace(String.reverse(Ps.lspace.at(b, c, t, Ps.lspace(t)))) : String}:
  match b:
    case True{}:
      ih
    case False{}:
      +x = String.reverse.go(t, SCon{c, SNil{}})
      +rw = String.reverse.go(w2, SNil{})
      %Equal.sym(String, String.reverse.go(String.append(t, w2), SCon{c, SNil{}}), String.reverse.go(w2, x), psb.rev_app(t, w2, SCon{c, SNil{}})) : {Ps.lspace(_) == Ps.lspace(x) : String}
      %Equal.sym(String, String.reverse.go(w2, x), String.append(rw, x), psb.rev_acc(w2, x)) : {Ps.lspace(_) == Ps.lspace(x) : String}
      psb.lsp_blank(rw, x, psb.blank_rev(w2, SNil{}, b2, {==}))

# trailing White_Space does not change the text kept after trimming
def psb.lt(s: String, +w2: String, +b2: {PackageSource.ps_blank(w2) == True{} : Bool}) -> {Ps.lspace(String.reverse(Ps.lspace(String.append(s, w2)))) == Ps.lspace(String.reverse(Ps.lspace(s))) : String}:
  match s:
    case SNil{}:
      %Equal.sym(String, Ps.lspace(w2), SNil{}, psb.lsp_nil(w2, b2)) : {Ps.lspace(String.reverse(_)) == SNil{} : String}
      {==}
    case SCon{+c, +t}:
      psb.lt.at(Ga.space(c), c, t, w2, b2, psb.lt(t, w2, b2))

# White_Space at both ends does not change a trimmed text
def psb.trim_pad(+w1: String, b1: {PackageSource.ps_blank(w1) == True{} : Bool}, +s: String, +w2: String, b2: {PackageSource.ps_blank(w2) == True{} : Bool}) -> {Ps.trim(String.append(w1, String.append(s, w2))) == Ps.trim(s) : String}:
  %Equal.sym(String, Ps.lspace(String.append(w1, String.append(s, w2))), Ps.lspace(String.append(s, w2)), psb.lsp_blank(w1, String.append(s, w2), b1)) : {String.reverse(Ps.lspace(String.reverse(_))) == Ps.trim(s) : String}
  Equal.cong(String, String, z => String.reverse(z), Ps.lspace(String.reverse(Ps.lspace(String.append(s, w2)))), Ps.lspace(String.reverse(Ps.lspace(s))), psb.lt(s, w2, b2))

# the local test of a trimmed value t
def psb.lbody(+t: String) -> Bool:
  Bool.not(Bool.or(String.starts_with(t, "npm:"), Bool.or(String.starts_with(t, "git:"), Bool.or(String.starts_with(t, "github:"), Bool.or(String.starts_with(t, "http:"), Bool.or(String.starts_with(t, "https:"), String.starts_with(t, "ssh:")))))))

def psb.local(+s: String) -> {Ps.local(s) == psb.lbody(Ps.trim(s)) : Bool}:
  {==}

# Checks
# ------

def psb.none_d(m: Maybe<&2, Ps.Defect>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{d}:
      False{}

def psb.none_f(m: Maybe<&2, Ps.Flaw>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{f}:
      False{}

def psb.ctl(c: Char) -> {Ps.control(c) == PackageSource.ps_control(c) : Bool}:
  match c:
    case Chr{x}:
      {==}

def psb.has(s: String, +x: Char) -> {Ps.has(s, x) == PackageSource.ps_has(s, x) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Equal.cong(Bool, Bool, z => Bool.or(Char.is_eq(c, x), z), Ps.has(t, x), PackageSource.ps_has(t, x), psb.has(t, x))

def psb.has.r(s: String, +x: Char) -> {PackageSource.ps_has(s, x) == Ps.has(s, x) : Bool}:
  Equal.sym(Bool, Ps.has(s, x), PackageSource.ps_has(s, x), psb.has(s, x))

def psb.alg(a: Bool, b: Bool, d: Bool, e: Bool) -> {Bool.and(Bool.not(Bool.or(a, d)), Bool.and(Bool.not(b), Bool.not(e))) == Bool.and(Bool.not(Bool.or(a, b)), Bool.not(Bool.or(d, e))) : Bool}:
  match a b d e:
    case True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{}:
      {==}

# no control char and no backslash: the code's two scans
def psb.clean(s: String) -> {PackageSource.ps_clean(s) == Bool.and(Bool.not(Ps.any_control(s)), Bool.not(Ps.has(s, Chr{92}))) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %psb.ctl(c) : {Bool.and(Bool.not(Bool.or(_, Char.is_eq(c, Chr{92}))), PackageSource.ps_clean(t)) == Bool.and(Bool.not(Bool.or(Ps.control(c), Ps.any_control(t))), Bool.not(Bool.or(Char.is_eq(c, Chr{92}), Ps.has(t, Chr{92})))) : Bool}
      %Equal.sym(Bool, PackageSource.ps_clean(t), Bool.and(Bool.not(Ps.any_control(t)), Bool.not(Ps.has(t, Chr{92}))), psb.clean(t)) : {Bool.and(Bool.not(Bool.or(Ps.control(c), Char.is_eq(c, Chr{92}))), _) == Bool.and(Bool.not(Bool.or(Ps.control(c), Ps.any_control(t))), Bool.not(Bool.or(Char.is_eq(c, Chr{92}), Ps.has(t, Chr{92})))) : Bool}
      psb.alg(Ps.control(c), Ps.any_control(t), Char.is_eq(c, Chr{92}), Ps.has(t, Chr{92}))

def psb.clean.r(s: String) -> {Bool.and(Bool.not(Ps.any_control(s)), Bool.not(Ps.has(s, Chr{92}))) == PackageSource.ps_clean(s) : Bool}:
  Equal.sym(Bool, PackageSource.ps_clean(s), Bool.and(Bool.not(Ps.any_control(s)), Bool.not(Ps.has(s, Chr{92}))), psb.clean(s))

def psb.arg.at(a: Bool, b: Bool, d: Bool) -> {psb.none_d(Ps.arg.at(a, b, d)) == Bool.and(Bool.not(a), Bool.and(Bool.not(b), Bool.not(d))) : Bool}:
  match a b d:
    case True{} _ _:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# R2: the code finds no argument defect exactly when the laws' ps_arg_ok holds
def psb.arg(s: String) -> {psb.none_d(Ps.arg(s)) == PackageSource.ps_arg_ok(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %psb.clean.r(SCon{c, t}) : {psb.none_d(Ps.arg(SCon{c, t})) == Bool.and(Bool.not(Char.is_eq(c, '-')), _) : Bool}
      psb.arg.at(Char.is_eq(c, '-'), Ps.any_control(SCon{c, t}), Ps.has(SCon{c, t}, Chr{92}))

def psb.arg.r(s: String) -> {PackageSource.ps_arg_ok(s) == psb.none_d(Ps.arg(s)) : Bool}:
  Equal.sym(Bool, psb.none_d(Ps.arg(s)), PackageSource.ps_arg_ok(s), psb.arg(s))

def psb.seg.at(a: Bool, b: Bool) -> {psb.none_d(Ps.seg.at(a, b)) == Bool.and(Bool.not(a), Bool.not(b)) : Bool}:
  match a b:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def psb.seg(s: String) -> {psb.none_d(Ps.seg(s)) == PackageSource.ps_seg_ok(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      psb.seg.at(Bool.or(String.eq(SCon{c, t}, "."), String.eq(SCon{c, t}, "..")), Bool.and(Char.is_alpha(c), String.starts_with(t, ":")))

def psb.seg.r(s: String) -> {PackageSource.ps_seg_ok(s) == psb.none_d(Ps.seg(s)) : Bool}:
  Equal.sym(Bool, psb.none_d(Ps.seg(s)), PackageSource.ps_seg_ok(s), psb.seg(s))

def psb.first(m: Maybe<&2, Ps.Defect>, r: Maybe<&2, Ps.Defect>) -> {psb.none_d(Ps.first.at(m, r)) == Bool.and(psb.none_d(m), psb.none_d(r)) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{d}:
      {==}

def psb.first.r(m: Maybe<&2, Ps.Defect>, r: Maybe<&2, Ps.Defect>) -> {Bool.and(psb.none_d(m), psb.none_d(r)) == psb.none_d(Ps.first.at(m, r)) : Bool}:
  Equal.sym(Bool, psb.none_d(Ps.first.at(m, r)), Bool.and(psb.none_d(m), psb.none_d(r)), psb.first(m, r))

def psb.segs(xs: List<&2, String>) -> {psb.none_d(Ps.segs(xs)) == PackageSource.ps_segs_ok(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %psb.first.r(Ps.seg(h), Ps.segs(t)) : {_ == PackageSource.ps_segs_ok(h <> t) : Bool}
      %psb.seg.r(h) : {Bool.and(_, psb.none_d(Ps.segs(t))) == PackageSource.ps_segs_ok(h <> t) : Bool}
      %Equal.sym(Bool, psb.none_d(Ps.segs(t)), PackageSource.ps_segs_ok(t), psb.segs(t)) : {Bool.and(PackageSource.ps_seg_ok(h), _) == PackageSource.ps_segs_ok(h <> t) : Bool}
      {==}

def psb.segs.r(xs: List<&2, String>) -> {PackageSource.ps_segs_ok(xs) == psb.none_d(Ps.segs(xs)) : Bool}:
  Equal.sym(Bool, psb.none_d(Ps.segs(xs)), PackageSource.ps_segs_ok(xs), psb.segs(xs))

# R2: the code finds no relative-path defect exactly when the laws'
# ps_rel_ok holds
def psb.rel(+s: String) -> {psb.none_d(Ps.rel(s)) == PackageSource.ps_rel_ok(s) : Bool}:
  %psb.first.r(Ps.arg(s), Ps.segs(String.split(s, '/'))) : {_ == PackageSource.ps_rel_ok(s) : Bool}
  %psb.arg.r(s) : {Bool.and(_, psb.none_d(Ps.segs(String.split(s, '/')))) == PackageSource.ps_rel_ok(s) : Bool}
  %psb.segs.r(String.split(s, '/')) : {Bool.and(PackageSource.ps_arg_ok(s), _) == PackageSource.ps_rel_ok(s) : Bool}
  {==}

def psb.rel.r(+s: String) -> {PackageSource.ps_rel_ok(s) == psb.none_d(Ps.rel(s)) : Bool}:
  Equal.sym(Bool, psb.none_d(Ps.rel(s)), PackageSource.ps_rel_ok(s), psb.rel(s))

def psb.dash.ok(b: Bool) -> {psb.none_f(Ps.dash.ok(b)) == Bool.not(b) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def psb.dash.f(c: Char, t: String, r: Maybe<&2, Ps.Cut>) -> {Ps.dash.at(Ps.proto.at(False{}, c, t, r)) == Ps.dash.at(r) : Maybe<&2, Ps.Flaw>}:
  match r:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case Ps.Cut{h, u}:
          {==}

def psb.dash.f.r(c: Char, t: String, r: Maybe<&2, Ps.Cut>) -> {Ps.dash.at(r) == Ps.dash.at(Ps.proto.at(False{}, c, t, r)) : Maybe<&2, Ps.Flaw>}:
  Equal.sym(Maybe<&2, Ps.Flaw>, Ps.dash.at(Ps.proto.at(False{}, c, t, r)), Ps.dash.at(r), psb.dash.f(c, t, r))

def psb.auth.at(b: Bool, c: Char, +t: String, r: Maybe<&2, Ps.Cut>, -k: Bool, ih: {psb.none_f(Ps.dash.at(r)) == k : Bool}) -> {psb.none_f(Ps.dash.at(Ps.proto.at(b, c, t, r))) == PackageSource.ps_auth_ok.at(b, t, k) : Bool}:
  match b:
    case True{}:
      psb.dash.ok(String.starts_with(String.drop(t, 2n), "-"))
    case False{}:
      %psb.dash.f.r(c, t, r) : {psb.none_f(_) == k : Bool}
      ih

# R5: the code finds no dash after the clone URL's `://` exactly when the
# laws' ps_auth_ok holds
def psb.auth(s: String) -> {psb.none_f(Ps.dash.at(Ps.proto(s))) == PackageSource.ps_auth_ok(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      psb.auth.at(String.starts_with(SCon{c, t}, "://"), c, t, Ps.proto(t), PackageSource.ps_auth_ok(t), psb.auth(t))

def psb.auth.r(s: String) -> {PackageSource.ps_auth_ok(s) == psb.none_f(Ps.dash.at(Ps.proto(s))) : Bool}:
  Equal.sym(Bool, psb.none_f(Ps.dash.at(Ps.proto(s))), PackageSource.ps_auth_ok(s), psb.auth(s))

def psb.or(m: Maybe<&2, Ps.Flaw>, r: Maybe<&2, Ps.Flaw>) -> {psb.none_f(Ps.flaw.or(m, r)) == Bool.and(psb.none_f(m), psb.none_f(r)) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{f}:
      {==}

def psb.or.r(m: Maybe<&2, Ps.Flaw>, r: Maybe<&2, Ps.Flaw>) -> {Bool.and(psb.none_f(m), psb.none_f(r)) == psb.none_f(Ps.flaw.or(m, r)) : Bool}:
  Equal.sym(Bool, psb.none_f(Ps.flaw.or(m, r)), Bool.and(psb.none_f(m), psb.none_f(r)), psb.or(m, r))

def psb.on(p: Ps.Part, m: Maybe<&2, Ps.Defect>) -> {psb.none_f(Ps.on(p, m)) == psb.none_d(m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{d}:
      {==}

def psb.on.r(p: Ps.Part, m: Maybe<&2, Ps.Defect>) -> {psb.none_d(m) == psb.none_f(Ps.on(p, m)) : Bool}:
  Equal.sym(Bool, psb.none_f(Ps.on(p, m)), psb.none_d(m), psb.on(p, m))

def psb.host(b: Bool, +h: String) -> {psb.none_d(Ps.host.at(b, h)) == Bool.and(Bool.not(b), PackageSource.ps_rel_ok(h)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      psb.rel(h)

def psb.host.r(b: Bool, +h: String) -> {Bool.and(Bool.not(b), PackageSource.ps_rel_ok(h)) == psb.none_d(Ps.host.at(b, h)) : Bool}:
  Equal.sym(Bool, psb.none_d(Ps.host.at(b, h)), Bool.and(Bool.not(b), PackageSource.ps_rel_ok(h)), psb.host(b, h))

def psb.gref(m: Maybe<&2, String>) -> {psb.none_f(Ps.gref(m)) == PackageSource.ps_ref_ok(m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %psb.on.r(Ps.PRef{}, Ps.arg(x)) : {_ == PackageSource.ps_ref_ok(Some{x}) : Bool}
      psb.arg(x)

def psb.gref.r(m: Maybe<&2, String>) -> {PackageSource.ps_ref_ok(m) == psb.none_f(Ps.gref(m)) : Bool}:
  Equal.sym(Bool, psb.none_f(Ps.gref(m)), PackageSource.ps_ref_ok(m), psb.gref(m))

def psb.git_ok_assoc(a: Bool, b: Bool, c: Bool) -> {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# R2, R5: the code finds no flaw in a git source exactly when the laws'
# ps_git_ok holds
def psb.flaws(g: Ps.GitSrc) -> {psb.none_f(Ps.flaws(g)) == PackageSource.ps_git_ok(g) : Bool}:
  match g:
    case Ps.GitSrc{+repo, +h, +p, +r, n}:
      +fh = Ps.on(Ps.PHost{}, Ps.host.at(Ps.has(h, '/'), h))
      +fp = Ps.on(Ps.PPath{}, Ps.rel(p))
      +fr = Ps.gref(r)
      +fc = Ps.on(Ps.PClone{}, Ps.arg(repo))
      +fd = Ps.dash.at(Ps.proto(repo))
      %psb.or.r(fh, Ps.flaw.or(fp, Ps.flaw.or(fr, Ps.flaw.or(fc, fd)))) : {_ == PackageSource.ps_git_ok(Ps.GitSrc{repo, h, p, r, n}) : Bool}
      %psb.or.r(fp, Ps.flaw.or(fr, Ps.flaw.or(fc, fd))) : {Bool.and(psb.none_f(fh), _) == PackageSource.ps_git_ok(Ps.GitSrc{repo, h, p, r, n}) : Bool}
      %psb.or.r(fr, Ps.flaw.or(fc, fd)) : {Bool.and(psb.none_f(fh), Bool.and(psb.none_f(fp), _)) == PackageSource.ps_git_ok(Ps.GitSrc{repo, h, p, r, n}) : Bool}
      %psb.or.r(fc, fd) : {Bool.and(psb.none_f(fh), Bool.and(psb.none_f(fp), Bool.and(psb.none_f(fr), _))) == PackageSource.ps_git_ok(Ps.GitSrc{repo, h, p, r, n}) : Bool}
      %psb.on.r(Ps.PHost{}, Ps.host.at(Ps.has(h, '/'), h)) : {Bool.and(_, Bool.and(psb.none_f(fp), Bool.and(psb.none_f(fr), Bool.and(psb.none_f(fc), psb.none_f(fd))))) == PackageSource.ps_git_ok(Ps.GitSrc{repo, h, p, r, n}) : Bool}
      %psb.host.r(Ps.has(h, '/'), h) : {Bool.and(_, Bool.and(psb.none_f(fp), Bool.and(psb.none_f(fr), Bool.and(psb.none_f(fc), psb.none_f(fd))))) == PackageSource.ps_git_ok(Ps.GitSrc{repo, h, p, r, n}) : Bool}
      %psb.has.r(h, '/') : {Bool.and(Bool.and(Bool.not(_), PackageSource.ps_rel_ok(h)), Bool.and(psb.none_f(fp), Bool.and(psb.none_f(fr), Bool.and(psb.none_f(fc), psb.none_f(fd))))) == PackageSource.ps_git_ok(Ps.GitSrc{repo, h, p, r, n}) : Bool}
      %psb.on.r(Ps.PPath{}, Ps.rel(p)) : {Bool.and(Bool.and(Bool.not(PackageSource.ps_has(h, '/')), PackageSource.ps_rel_ok(h)), Bool.and(_, Bool.and(psb.none_f(fr), Bool.and(psb.none_f(fc), psb.none_f(fd))))) == PackageSource.ps_git_ok(Ps.GitSrc{repo, h, p, r, n}) : Bool}
      %psb.rel.r(p) : {Bool.and(Bool.and(Bool.not(PackageSource.ps_has(h, '/')), PackageSource.ps_rel_ok(h)), Bool.and(_, Bool.and(psb.none_f(fr), Bool.and(psb.none_f(fc), psb.none_f(fd))))) == PackageSource.ps_git_ok(Ps.GitSrc{repo, h, p, r, n}) : Bool}
      %psb.gref.r(r) : {Bool.and(Bool.and(Bool.not(PackageSource.ps_has(h, '/')), PackageSource.ps_rel_ok(h)), Bool.and(PackageSource.ps_rel_ok(p), Bool.and(_, Bool.and(psb.none_f(fc), psb.none_f(fd))))) == PackageSource.ps_git_ok(Ps.GitSrc{repo, h, p, r, n}) : Bool}
      %psb.on.r(Ps.PClone{}, Ps.arg(repo)) : {Bool.and(Bool.and(Bool.not(PackageSource.ps_has(h, '/')), PackageSource.ps_rel_ok(h)), Bool.and(PackageSource.ps_rel_ok(p), Bool.and(PackageSource.ps_ref_ok(r), Bool.and(_, psb.none_f(fd))))) == PackageSource.ps_git_ok(Ps.GitSrc{repo, h, p, r, n}) : Bool}
      %psb.arg.r(repo) : {Bool.and(Bool.and(Bool.not(PackageSource.ps_has(h, '/')), PackageSource.ps_rel_ok(h)), Bool.and(PackageSource.ps_rel_ok(p), Bool.and(PackageSource.ps_ref_ok(r), Bool.and(_, psb.none_f(fd))))) == PackageSource.ps_git_ok(Ps.GitSrc{repo, h, p, r, n}) : Bool}
      %psb.auth.r(repo) : {Bool.and(Bool.and(Bool.not(PackageSource.ps_has(h, '/')), PackageSource.ps_rel_ok(h)), Bool.and(PackageSource.ps_rel_ok(p), Bool.and(PackageSource.ps_ref_ok(r), Bool.and(PackageSource.ps_arg_ok(repo), _)))) == PackageSource.ps_git_ok(Ps.GitSrc{repo, h, p, r, n}) : Bool}
      psb.git_ok_assoc(Bool.not(PackageSource.ps_has(h, '/')), PackageSource.ps_rel_ok(h), Bool.and(PackageSource.ps_rel_ok(p), Bool.and(PackageSource.ps_ref_ok(r), Bool.and(PackageSource.ps_arg_ok(repo), PackageSource.ps_auth_ok(repo)))))

# Answers
# -------

# a git answer is safe: an accepted git source passes ps_git_ok
def psb.ans_ok(a: Ps.GitAns) -> Bool:
  match a:
    case Ps.NoGit{}:
      True{}
    case Ps.IsGit{g}:
      PackageSource.ps_git_ok(g)
    case Ps.BadGit{f}:
      True{}

def psb.chk.at(f: Maybe<&2, Ps.Flaw>, g: Ps.GitSrc, e: {psb.none_f(f) == PackageSource.ps_git_ok(g) : Bool}) -> {psb.ans_ok(Ps.checked.at(f, g)) == True{} : Bool}:
  match f:
    case None{}:
      Equal.sym(Bool, True{}, PackageSource.ps_git_ok(g), e)
    case Some{x}:
      {==}

def psb.checked(m: Maybe<&2, Ps.GitSrc>) -> {psb.ans_ok(Ps.checked(m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+g}:
      psb.chk.at(Ps.flaws(g), g, psb.flaws(g))

def psb.gate(go: Bool, +u: String) -> {psb.ans_ok(Ps.git.gate(go, u)) == True{} : Bool}:
  match go:
    case True{}:
      psb.checked(Ps.found(u, Ps.sref(u)))
    case False{}:
      {==}

def psb.git.at(b: Bool, +t: String) -> {psb.ans_ok(Ps.git.at(b, t)) == True{} : Bool}:
  match b:
    case True{}:
      psb.gate(True{}, Ps.trim(String.drop(t, 4n)))
    case False{}:
      psb.gate(Ps.proto_url(t), t)

# R2, R5: every git answer is safe
def psb.git(s: String) -> {psb.ans_ok(Ps.git(s)) == True{} : Bool}:
  +t = Ps.trim(s)
  psb.git.at(String.starts_with(t, "git:"), t)

def psb.lspace.at(+b: Bool, +c: Char, +t: String, +r: String) -> {Ps.lspace.at(b, c, t, r) == PackageSource.ps_lspace.at(b, c, t, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def psb.space(+c: Char) -> {Ga.space(c) == PackageSource.ps_space(c) : Bool}:
  {==}

def psb.lspace(+s: String) -> {Ps.lspace(s) == PackageSource.ps_lspace(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Ps.lspace(t), PackageSource.ps_lspace(t), psb.lspace(t)) : {Ps.lspace.at(Ga.space(c), c, t, _) == PackageSource.ps_lspace.at(PackageSource.ps_space(c), c, t, PackageSource.ps_lspace(t)) : String}
      %Equal.sym(Bool, Ga.space(c), PackageSource.ps_space(c), psb.space(c)) : {Ps.lspace.at(_, c, t, PackageSource.ps_lspace(t)) == PackageSource.ps_lspace.at(PackageSource.ps_space(c), c, t, PackageSource.ps_lspace(t)) : String}
      psb.lspace.at(PackageSource.ps_space(c), c, t, PackageSource.ps_lspace(t))

def psb.trim(+s: String) -> {Ps.trim(s) == PackageSource.ps_trim(s) : String}:
  %Equal.sym(String, Ps.lspace(s), PackageSource.ps_lspace(s), psb.lspace(s)) : {String.reverse(Ps.lspace(String.reverse(_))) == String.reverse(PackageSource.ps_lspace(String.reverse(PackageSource.ps_lspace(s)))) : String}
  %Equal.sym(String, Ps.lspace(String.reverse(PackageSource.ps_lspace(s))), PackageSource.ps_lspace(String.reverse(PackageSource.ps_lspace(s))), psb.lspace(String.reverse(PackageSource.ps_lspace(s)))) : {String.reverse(_) == String.reverse(PackageSource.ps_lspace(String.reverse(PackageSource.ps_lspace(s)))) : String}
  {==}

def psb.local_orig(+s: String) -> {Ps.local(s) == PackageSource.ps_local(s) : Bool}:
  %Equal.sym(String, Ps.trim(s), PackageSource.ps_trim(s), psb.trim(s)) : {Bool.not(Bool.or(String.starts_with(_, "npm:"), Bool.or(String.starts_with(Ps.trim(s), "git:"), Bool.or(String.starts_with(Ps.trim(s), "github:"), Bool.or(String.starts_with(Ps.trim(s), "http:"), Bool.or(String.starts_with(Ps.trim(s), "https:"), String.starts_with(Ps.trim(s), "ssh:"))))))) == Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "git:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "github:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "http:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "https:"), String.starts_with(PackageSource.ps_trim(s), "ssh:"))))))) : Bool}
  %Equal.sym(String, Ps.trim(s), PackageSource.ps_trim(s), psb.trim(s)) : {Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(_, "git:"), Bool.or(String.starts_with(Ps.trim(s), "github:"), Bool.or(String.starts_with(Ps.trim(s), "http:"), Bool.or(String.starts_with(Ps.trim(s), "https:"), String.starts_with(Ps.trim(s), "ssh:"))))))) == Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "git:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "github:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "http:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "https:"), String.starts_with(PackageSource.ps_trim(s), "ssh:"))))))) : Bool}
  %Equal.sym(String, Ps.trim(s), PackageSource.ps_trim(s), psb.trim(s)) : {Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "git:"), Bool.or(String.starts_with(_, "github:"), Bool.or(String.starts_with(Ps.trim(s), "http:"), Bool.or(String.starts_with(Ps.trim(s), "https:"), String.starts_with(Ps.trim(s), "ssh:"))))))) == Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "git:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "github:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "http:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "https:"), String.starts_with(PackageSource.ps_trim(s), "ssh:"))))))) : Bool}
  %Equal.sym(String, Ps.trim(s), PackageSource.ps_trim(s), psb.trim(s)) : {Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "git:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "github:"), Bool.or(String.starts_with(_, "http:"), Bool.or(String.starts_with(Ps.trim(s), "https:"), String.starts_with(Ps.trim(s), "ssh:"))))))) == Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "git:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "github:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "http:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "https:"), String.starts_with(PackageSource.ps_trim(s), "ssh:"))))))) : Bool}
  %Equal.sym(String, Ps.trim(s), PackageSource.ps_trim(s), psb.trim(s)) : {Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "git:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "github:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "http:"), Bool.or(String.starts_with(_, "https:"), String.starts_with(Ps.trim(s), "ssh:"))))))) == Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "git:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "github:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "http:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "https:"), String.starts_with(PackageSource.ps_trim(s), "ssh:"))))))) : Bool}
  %Equal.sym(String, Ps.trim(s), PackageSource.ps_trim(s), psb.trim(s)) : {Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "git:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "github:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "http:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "https:"), String.starts_with(_, "ssh:"))))))) == Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "git:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "github:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "http:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "https:"), String.starts_with(PackageSource.ps_trim(s), "ssh:"))))))) : Bool}
  {==}

def psb.control(+c: Char) -> {Ps.control(c) == PackageSource.ps_control(c) : Bool}:
  match c:
    case Chr{+x}:
      {==}

def psb.any_control(+s: String) -> {Ps.any_control(s) == PackageSource.ps_any_control(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Ps.control(c), PackageSource.ps_control(c), psb.control(c)) : {Bool.or(_, Ps.any_control(t)) == Bool.or(PackageSource.ps_control(c), PackageSource.ps_any_control(t)) : Bool}
      %Equal.sym(Bool, Ps.any_control(t), PackageSource.ps_any_control(t), psb.any_control(t)) : {Bool.or(PackageSource.ps_control(c), _) == Bool.or(PackageSource.ps_control(c), PackageSource.ps_any_control(t)) : Bool}
      {==}

def psb.arg.at_orig(+dash: Bool, +ctl: Bool, +bs: Bool) -> {Ps.arg.at(dash, ctl, bs) == PackageSource.ps_arg.at(dash, ctl, bs) : Maybe<&2, Ps.Defect>}:
  match dash:
    case True{}:
      {==}
    case False{}:
      match ctl:
        case True{}:
          {==}
        case False{}:
          match bs:
            case True{}:
              {==}
            case False{}:
              {==}

def psb.has_orig(+s: String, +x: Char) -> {Ps.has(s, x) == PackageSource.ps_has(s, x) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Ps.has(t, x), PackageSource.ps_has(t, x), psb.has_orig(t, x)) : {Bool.or(Char.is_eq(c, x), _) == Bool.or(Char.is_eq(c, x), PackageSource.ps_has(t, x)) : Bool}
      {==}

def psb.arg_orig(+s: String) -> {Ps.arg(s) == PackageSource.ps_arg(s) : Maybe<&2, Ps.Defect>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Ps.any_control(SCon{c, t}), PackageSource.ps_any_control(SCon{c, t}), psb.any_control(SCon{c, t})) : {Ps.arg.at(Char.is_eq(c, '-'), _, Ps.has(SCon{c, t}, Chr{92})) == PackageSource.ps_arg.at(Char.is_eq(c, '-'), PackageSource.ps_any_control(SCon{c, t}), PackageSource.ps_has(SCon{c, t}, Chr{92})) : Maybe<&2, Ps.Defect>}
      %Equal.sym(Bool, Ps.has(SCon{c, t}, Chr{92}), PackageSource.ps_has(SCon{c, t}, Chr{92}), psb.has_orig(SCon{c, t}, Chr{92})) : {Ps.arg.at(Char.is_eq(c, '-'), PackageSource.ps_any_control(SCon{c, t}), _) == PackageSource.ps_arg.at(Char.is_eq(c, '-'), PackageSource.ps_any_control(SCon{c, t}), PackageSource.ps_has(SCon{c, t}, Chr{92})) : Maybe<&2, Ps.Defect>}
      psb.arg.at_orig(Char.is_eq(c, '-'), PackageSource.ps_any_control(SCon{c, t}), PackageSource.ps_has(SCon{c, t}, Chr{92}))

def psb.is_some(+m: Maybe<&2, String>) -> {Ps.is_some(m) == PackageSource.ps_is_some(m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      {==}

def psb.npm.ok(+m: Maybe<&2, Ps.Defect>, +name: String, +pinned: Bool, +spec: String) -> {Ps.npm.ok(m, name, pinned, spec) == PackageSource.ps_npm.ok(m, name, pinned, spec) : Ps.Parsed}:
  match m:
    case None{}:
      {==}
    case Some{+d}:
      {==}

def psb.first.at(+m: Maybe<&2, Ps.Defect>, +r: Maybe<&2, Ps.Defect>) -> {Ps.first.at(m, r) == PackageSource.ps_first.at(m, r) : Maybe<&2, Ps.Defect>}:
  match m:
    case None{}:
      {==}
    case Some{+d}:
      {==}

def psb.seg.at_orig(+dot: Bool, +drive: Bool) -> {Ps.seg.at(dot, drive) == PackageSource.ps_seg.at(dot, drive) : Maybe<&2, Ps.Defect>}:
  match dot:
    case True{}:
      {==}
    case False{}:
      match drive:
        case True{}:
          {==}
        case False{}:
          {==}

def psb.seg_orig(+s: String) -> {Ps.seg(s) == PackageSource.ps_seg(s) : Maybe<&2, Ps.Defect>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      psb.seg.at_orig(Bool.or(String.eq(SCon{c, t}, "."), String.eq(SCon{c, t}, "..")), Bool.and(Char.is_alpha(c), String.starts_with(t, ":")))

def psb.segs_orig(+xs: List<&2, String>) -> {Ps.segs(xs) == PackageSource.ps_segs(xs) : Maybe<&2, Ps.Defect>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %Equal.sym(Maybe<&2, Ps.Defect>, Ps.seg(h), PackageSource.ps_seg(h), psb.seg_orig(h)) : {Ps.first.at(_, Ps.segs(t)) == PackageSource.ps_first.at(PackageSource.ps_seg(h), PackageSource.ps_segs(t)) : Maybe<&2, Ps.Defect>}
      %Equal.sym(Maybe<&2, Ps.Defect>, Ps.segs(t), PackageSource.ps_segs(t), psb.segs_orig(t)) : {Ps.first.at(PackageSource.ps_seg(h), _) == PackageSource.ps_first.at(PackageSource.ps_seg(h), PackageSource.ps_segs(t)) : Maybe<&2, Ps.Defect>}
      psb.first.at(PackageSource.ps_seg(h), PackageSource.ps_segs(t))

def psb.rel_orig(+s: String) -> {Ps.rel(s) == PackageSource.ps_rel(s) : Maybe<&2, Ps.Defect>}:
  %Equal.sym(Maybe<&2, Ps.Defect>, Ps.arg(s), PackageSource.ps_arg(s), psb.arg_orig(s)) : {Ps.first.at(_, Ps.segs(String.split(s, '/'))) == PackageSource.ps_first.at(PackageSource.ps_arg(s), PackageSource.ps_segs(String.split(s, '/'))) : Maybe<&2, Ps.Defect>}
  %Equal.sym(Maybe<&2, Ps.Defect>, Ps.segs(String.split(s, '/')), PackageSource.ps_segs(String.split(s, '/')), psb.segs_orig(String.split(s, '/'))) : {Ps.first.at(PackageSource.ps_arg(s), _) == PackageSource.ps_first.at(PackageSource.ps_arg(s), PackageSource.ps_segs(String.split(s, '/'))) : Maybe<&2, Ps.Defect>}
  psb.first.at(PackageSource.ps_arg(s), PackageSource.ps_segs(String.split(s, '/')))

def psb.npm.name(+ns: Ps.NpmSpec, +spec: String) -> {Ps.npm.name(ns, spec) == PackageSource.ps_npm.name(ns, spec) : Ps.Parsed}:
  match ns:
    case Ps.NpmSpec{+name, +v}:
      %Equal.sym(Maybe<&2, Ps.Defect>, Ps.rel(name), PackageSource.ps_rel(name), psb.rel_orig(name)) : {Ps.npm.ok(_, name, Ps.is_some(v), spec) == PackageSource.ps_npm.ok(PackageSource.ps_rel(name), name, PackageSource.ps_is_some(v), spec) : Ps.Parsed}
      %Equal.sym(Bool, Ps.is_some(v), PackageSource.ps_is_some(v), psb.is_some(v)) : {Ps.npm.ok(PackageSource.ps_rel(name), name, _, spec) == PackageSource.ps_npm.ok(PackageSource.ps_rel(name), name, PackageSource.ps_is_some(v), spec) : Ps.Parsed}
      psb.npm.ok(PackageSource.ps_rel(name), name, PackageSource.ps_is_some(v), spec)

def psb.cut.at(+b: Bool, +c: Char, +t: String, +r: Maybe<&2, Ps.Cut>) -> {Ps.cut.at(b, c, t, r) == PackageSource.ps_cut.at(b, c, t, r) : Maybe<&2, Ps.Cut>}:
  match b:
    case True{}:
      {==}
    case False{}:
      match r:
        case None{}:
          {==}
        case Some{+x}:
          match x:
            case Ps.Cut{+h, +u}:
              {==}

def psb.cut(+s: String, +sep: Char) -> {Ps.cut(s, sep) == PackageSource.ps_cut(s, sep) : Maybe<&2, Ps.Cut>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(t, sep), PackageSource.ps_cut(t, sep), psb.cut(t, sep)) : {Ps.cut.at(Char.is_eq(c, sep), c, t, _) == PackageSource.ps_cut.at(Char.is_eq(c, sep), c, t, PackageSource.ps_cut(t, sep)) : Maybe<&2, Ps.Cut>}
      psb.cut.at(Char.is_eq(c, sep), c, t, PackageSource.ps_cut(t, sep))

def psb.npm_spec.ok(+e: Bool, +c: Char, +h: String, +v: String, +t: String) -> {Ps.npm_spec.ok(e, c, h, v, t) == PackageSource.ps_npm_spec.ok(e, c, h, v, t) : Ps.NpmSpec}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def psb.npm_spec.at(+m: Maybe<&2, Ps.Cut>, +c: Char, +t: String) -> {Ps.npm_spec.at(m, c, t) == PackageSource.ps_npm_spec.at(m, c, t) : Ps.NpmSpec}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+h, +v}:
          psb.npm_spec.ok(String.is_empty(v), c, h, v, t)

def psb.npm_spec(+s: String) -> {Ps.npm_spec(s) == PackageSource.ps_npm_spec(s) : Ps.NpmSpec}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(t, '@'), PackageSource.ps_cut(t, '@'), psb.cut(t, '@')) : {Ps.npm_spec.at(_, c, t) == PackageSource.ps_npm_spec.at(PackageSource.ps_cut(t, '@'), c, t) : Ps.NpmSpec}
      psb.npm_spec.at(PackageSource.ps_cut(t, '@'), c, t)

def psb.npm.at(+m: Maybe<&2, Ps.Defect>, +spec: String) -> {Ps.npm.at(m, spec) == PackageSource.ps_npm.at(m, spec) : Ps.Parsed}:
  match m:
    case None{}:
      %Equal.sym(Ps.NpmSpec, Ps.npm_spec(spec), PackageSource.ps_npm_spec(spec), psb.npm_spec(spec)) : {Ps.npm.name(_, spec) == PackageSource.ps_npm.name(PackageSource.ps_npm_spec(spec), spec) : Ps.Parsed}
      psb.npm.name(PackageSource.ps_npm_spec(spec), spec)
    case Some{+d}:
      {==}

def psb.npm(+spec: String) -> {Ps.npm(spec) == PackageSource.ps_npm(spec) : Ps.Parsed}:
  %Equal.sym(Maybe<&2, Ps.Defect>, Ps.arg(spec), PackageSource.ps_arg(spec), psb.arg_orig(spec)) : {Ps.npm.at(_, spec) == PackageSource.ps_npm.at(PackageSource.ps_arg(spec), spec) : Ps.Parsed}
  psb.npm.at(PackageSource.ps_arg(spec), spec)

def psb.checked.at(+m: Maybe<&2, Ps.Flaw>, +g: Ps.GitSrc) -> {Ps.checked.at(m, g) == PackageSource.ps_checked.at(m, g) : Ps.GitAns}:
  match m:
    case None{}:
      {==}
    case Some{+f}:
      {==}

def psb.dash.ok_orig(+b: Bool) -> {Ps.dash.ok(b) == PackageSource.ps_dash.ok(b) : Maybe<&2, Ps.Flaw>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def psb.dash.at(+m: Maybe<&2, Ps.Cut>) -> {Ps.dash.at(m) == PackageSource.ps_dash.at(m) : Maybe<&2, Ps.Flaw>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+s, +a}:
          psb.dash.ok_orig(String.starts_with(a, "-"))

def psb.flaw.or(+m: Maybe<&2, Ps.Flaw>, +r: Maybe<&2, Ps.Flaw>) -> {Ps.flaw.or(m, r) == PackageSource.ps_flaw.or(m, r) : Maybe<&2, Ps.Flaw>}:
  match m:
    case None{}:
      {==}
    case Some{+f}:
      {==}

def psb.on_orig(+p: Ps.Part, +m: Maybe<&2, Ps.Defect>) -> {Ps.on(p, m) == PackageSource.ps_on(p, m) : Maybe<&2, Ps.Flaw>}:
  match m:
    case None{}:
      {==}
    case Some{+d}:
      {==}

def psb.gref_orig(+m: Maybe<&2, String>) -> {Ps.gref(m) == PackageSource.ps_gref(m) : Maybe<&2, Ps.Flaw>}:
  match m:
    case None{}:
      {==}
    case Some{+r}:
      %Equal.sym(Maybe<&2, Ps.Defect>, Ps.arg(r), PackageSource.ps_arg(r), psb.arg_orig(r)) : {Ps.on(Ps.PRef{}, _) == PackageSource.ps_on(Ps.PRef{}, PackageSource.ps_arg(r)) : Maybe<&2, Ps.Flaw>}
      psb.on_orig(Ps.PRef{}, PackageSource.ps_arg(r))

def psb.host.at(+b: Bool, +h: String) -> {Ps.host.at(b, h) == PackageSource.ps_host.at(b, h) : Maybe<&2, Ps.Defect>}:
  match b:
    case True{}:
      {==}
    case False{}:
      psb.rel_orig(h)

def psb.proto.at(+b: Bool, +c: Char, +t: String, +r: Maybe<&2, Ps.Cut>) -> {Ps.proto.at(b, c, t, r) == PackageSource.ps_proto.at(b, c, t, r) : Maybe<&2, Ps.Cut>}:
  match b:
    case True{}:
      {==}
    case False{}:
      match r:
        case None{}:
          {==}
        case Some{+x}:
          match x:
            case Ps.Cut{+h, +u}:
              {==}

def psb.proto(+s: String) -> {Ps.proto(s) == PackageSource.ps_proto(s) : Maybe<&2, Ps.Cut>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Maybe<&2, Ps.Cut>, Ps.proto(t), PackageSource.ps_proto(t), psb.proto(t)) : {Ps.proto.at(String.starts_with(SCon{c, t}, "://"), c, t, _) == PackageSource.ps_proto.at(String.starts_with(SCon{c, t}, "://"), c, t, PackageSource.ps_proto(t)) : Maybe<&2, Ps.Cut>}
      psb.proto.at(String.starts_with(SCon{c, t}, "://"), c, t, PackageSource.ps_proto(t))

def psb.flaws_orig(+g: Ps.GitSrc) -> {Ps.flaws(g) == PackageSource.ps_flaws(g) : Maybe<&2, Ps.Flaw>}:
  match g:
    case Ps.GitSrc{+repo, +h, +p, +r, +n}:
      %Equal.sym(Bool, Ps.has(h, '/'), PackageSource.ps_has(h, '/'), psb.has_orig(h, '/')) : {Ps.flaw.or(Ps.on(Ps.PHost{}, Ps.host.at(_, h)), Ps.flaw.or(Ps.on(Ps.PPath{}, Ps.rel(p)), Ps.flaw.or(Ps.gref(r), Ps.flaw.or(Ps.on(Ps.PClone{}, Ps.arg(repo)), Ps.dash.at(Ps.proto(repo)))))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Defect>, Ps.host.at(PackageSource.ps_has(h, '/'), h), PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h), psb.host.at(PackageSource.ps_has(h, '/'), h)) : {Ps.flaw.or(Ps.on(Ps.PHost{}, _), Ps.flaw.or(Ps.on(Ps.PPath{}, Ps.rel(p)), Ps.flaw.or(Ps.gref(r), Ps.flaw.or(Ps.on(Ps.PClone{}, Ps.arg(repo)), Ps.dash.at(Ps.proto(repo)))))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Flaw>, Ps.on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), psb.on_orig(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h))) : {Ps.flaw.or(_, Ps.flaw.or(Ps.on(Ps.PPath{}, Ps.rel(p)), Ps.flaw.or(Ps.gref(r), Ps.flaw.or(Ps.on(Ps.PClone{}, Ps.arg(repo)), Ps.dash.at(Ps.proto(repo)))))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Defect>, Ps.rel(p), PackageSource.ps_rel(p), psb.rel_orig(p)) : {Ps.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), Ps.flaw.or(Ps.on(Ps.PPath{}, _), Ps.flaw.or(Ps.gref(r), Ps.flaw.or(Ps.on(Ps.PClone{}, Ps.arg(repo)), Ps.dash.at(Ps.proto(repo)))))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Flaw>, Ps.on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), psb.on_orig(Ps.PPath{}, PackageSource.ps_rel(p))) : {Ps.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), Ps.flaw.or(_, Ps.flaw.or(Ps.gref(r), Ps.flaw.or(Ps.on(Ps.PClone{}, Ps.arg(repo)), Ps.dash.at(Ps.proto(repo)))))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Flaw>, Ps.gref(r), PackageSource.ps_gref(r), psb.gref_orig(r)) : {Ps.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), Ps.flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), Ps.flaw.or(_, Ps.flaw.or(Ps.on(Ps.PClone{}, Ps.arg(repo)), Ps.dash.at(Ps.proto(repo)))))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Defect>, Ps.arg(repo), PackageSource.ps_arg(repo), psb.arg_orig(repo)) : {Ps.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), Ps.flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), Ps.flaw.or(PackageSource.ps_gref(r), Ps.flaw.or(Ps.on(Ps.PClone{}, _), Ps.dash.at(Ps.proto(repo)))))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Flaw>, Ps.on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), psb.on_orig(Ps.PClone{}, PackageSource.ps_arg(repo))) : {Ps.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), Ps.flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), Ps.flaw.or(PackageSource.ps_gref(r), Ps.flaw.or(_, Ps.dash.at(Ps.proto(repo)))))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Cut>, Ps.proto(repo), PackageSource.ps_proto(repo), psb.proto(repo)) : {Ps.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), Ps.flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), Ps.flaw.or(PackageSource.ps_gref(r), Ps.flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), Ps.dash.at(_))))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Flaw>, Ps.dash.at(PackageSource.ps_proto(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)), psb.dash.at(PackageSource.ps_proto(repo))) : {Ps.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), Ps.flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), Ps.flaw.or(PackageSource.ps_gref(r), Ps.flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), _)))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Flaw>, Ps.flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo))), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo))), psb.flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))) : {Ps.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), Ps.flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), Ps.flaw.or(PackageSource.ps_gref(r), _))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Flaw>, Ps.flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))), psb.flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo))))) : {Ps.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), Ps.flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), _)) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Flaw>, Ps.flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo))))), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo))))), psb.flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : {Ps.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), _) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      psb.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo))))))

def psb.checked_orig(+m: Maybe<&2, Ps.GitSrc>) -> {Ps.checked(m) == PackageSource.ps_checked(m) : Ps.GitAns}:
  match m:
    case None{}:
      {==}
    case Some{+g}:
      %Equal.sym(Maybe<&2, Ps.Flaw>, Ps.flaws(g), PackageSource.ps_flaws(g), psb.flaws_orig(g)) : {Ps.checked.at(_, g) == PackageSource.ps_checked.at(PackageSource.ps_flaws(g), g) : Ps.GitAns}
      psb.checked.at(PackageSource.ps_flaws(g), g)

def psb.nogit.at(+b: Bool, +r: String, +k: String) -> {Ps.nogit.at(b, r, k) == PackageSource.ps_nogit.at(b, r, k) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def psb.nogit(+n: Nat, +r: String) -> {Ps.nogit(n, r) == PackageSource.ps_nogit(n, r) : String}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(String, Ps.nogit(p, String.drop(r, 4n)), PackageSource.ps_nogit(p, String.drop(r, 4n)), psb.nogit(p, String.drop(r, 4n))) : {Ps.nogit.at(String.starts_with(r, "tig."), r, _) == PackageSource.ps_nogit.at(String.starts_with(r, "tig."), r, PackageSource.ps_nogit(p, String.drop(r, 4n))) : String}
      psb.nogit.at(String.starts_with(r, "tig."), r, PackageSource.ps_nogit(p, String.drop(r, 4n)))

def psb.unsuffix(+s: String) -> {Ps.unsuffix(s) == PackageSource.ps_unsuffix(s) : String}:
  %Equal.sym(String, Ps.nogit(String.length(s), String.reverse(s)), PackageSource.ps_nogit(String.length(s), String.reverse(s)), psb.nogit(String.length(s), String.reverse(s))) : {String.reverse(_) == String.reverse(PackageSource.ps_nogit(String.length(s), String.reverse(s))) : String}
  {==}

def psb.hosted.ok(+e: Bool, +d: String, +u: String, +p: String, +k: Maybe<&2, String>) -> {Ps.hosted.ok(e, d, u, p, k) == PackageSource.ps_hosted.ok(e, d, u, p, k) : Maybe<&2, Ps.Hosted>}:
  match e:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(String, Ps.unsuffix(p), PackageSource.ps_unsuffix(p), psb.unsuffix(p)) : {Some{Ps.Hosted{d, u, _, k}} == Some{Ps.Hosted{d, u, PackageSource.ps_unsuffix(p), k}} : Maybe<&2, Ps.Hosted>}
      {==}

def psb.hosted.parts(+d: String, +m: Maybe<&2, Ps.Cut>, +k: Maybe<&2, String>) -> {Ps.hosted.parts(d, m, k) == PackageSource.ps_hosted.parts(d, m, k) : Maybe<&2, Ps.Hosted>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+u, +p}:
          psb.hosted.ok(Bool.or(String.is_empty(u), String.is_empty(p)), d, u, p, k)

def psb.hosted.short(+m: Maybe<&2, Ps.Cut>, +k: Maybe<&2, String>) -> {Ps.hosted.short(m, k) == PackageSource.ps_hosted.short(m, k) : Maybe<&2, Ps.Hosted>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+d, +rest}:
          %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(rest, '/'), PackageSource.ps_cut(rest, '/'), psb.cut(rest, '/')) : {Ps.hosted.parts(d, _, k) == PackageSource.ps_hosted.parts(d, PackageSource.ps_cut(rest, '/'), k) : Maybe<&2, Ps.Hosted>}
          psb.hosted.parts(d, PackageSource.ps_cut(rest, '/'), k)

def psb.short.at(+a: Bool, +b: Bool, +c: Bool, +d: Bool, +u: String) -> {Ps.short.at(a, b, c, d, u) == PackageSource.ps_short.at(a, b, c, d, u) : Maybe<&2, Ps.Cut>}:
  match a:
    case True{}:
      {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          match c:
            case True{}:
              {==}
            case False{}:
              match d:
                case True{}:
                  {==}
                case False{}:
                  {==}

def psb.short(+u: String) -> {Ps.short(u) == PackageSource.ps_short(u) : Maybe<&2, Ps.Cut>}:
  psb.short.at(String.starts_with(u, "github:"), String.starts_with(u, "gitlab:"), String.starts_with(u, "bitbucket:"), String.starts_with(u, "gist:"), u)

def psb.hosted.at(+m: Maybe<&2, Ps.Cut>, +c: String) -> {Ps.hosted.at(m, c) == PackageSource.ps_hosted.at(m, c) : Maybe<&2, Ps.Hosted>}:
  match m:
    case None{}:
      %Equal.sym(Maybe<&2, Ps.Cut>, Ps.short(c), PackageSource.ps_short(c), psb.short(c)) : {Ps.hosted.short(_, None{}) == PackageSource.ps_hosted.short(PackageSource.ps_short(c), None{}) : Maybe<&2, Ps.Hosted>}
      psb.hosted.short(PackageSource.ps_short(c), None{})
    case Some{+x}:
      match x:
        case Ps.Cut{+u, +k}:
          %Equal.sym(Maybe<&2, Ps.Cut>, Ps.short(u), PackageSource.ps_short(u), psb.short(u)) : {Ps.hosted.short(_, Some{k}) == PackageSource.ps_hosted.short(PackageSource.ps_short(u), Some{k}) : Maybe<&2, Ps.Hosted>}
          psb.hosted.short(PackageSource.ps_short(u), Some{k})

def psb.hosted(+c: String) -> {Ps.hosted(c) == PackageSource.ps_hosted(c) : Maybe<&2, Ps.Hosted>}:
  %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(c, '#'), PackageSource.ps_cut(c, '#'), psb.cut(c, '#')) : {Ps.hosted.at(_, c) == PackageSource.ps_hosted.at(PackageSource.ps_cut(c, '#'), c) : Maybe<&2, Ps.Hosted>}
  psb.hosted.at(PackageSource.ps_cut(c, '#'), c)

def psb.keep.at(+drop: Bool, +h: Ps.Hosted) -> {Ps.keep.at(drop, h) == PackageSource.ps_keep.at(drop, h) : Maybe<&2, Ps.Hosted>}:
  match drop:
    case True{}:
      {==}
    case False{}:
      {==}

def psb.keep.of(+h: Ps.Hosted, +r: Bool) -> {Ps.keep.of(h, r) == PackageSource.ps_keep.of(h, r) : Maybe<&2, Ps.Hosted>}:
  match h:
    case Ps.Hosted{+d, +u, +p, +k}:
      %Equal.sym(Bool, Ps.has(p, '@'), PackageSource.ps_has(p, '@'), psb.has_orig(p, '@')) : {Ps.keep.at(Bool.and(r, _), Ps.Hosted{d, u, p, k}) == PackageSource.ps_keep.at(Bool.and(r, PackageSource.ps_has(p, '@')), Ps.Hosted{d, u, p, k}) : Maybe<&2, Ps.Hosted>}
      psb.keep.at(Bool.and(r, PackageSource.ps_has(p, '@')), Ps.Hosted{d, u, p, k})

def psb.keep(+m: Maybe<&2, Ps.Hosted>, +r: Bool) -> {Ps.keep(m, r) == PackageSource.ps_keep(m, r) : Maybe<&2, Ps.Hosted>}:
  match m:
    case None{}:
      {==}
    case Some{+h}:
      psb.keep.of(h, r)

def psb.cand.at(+repo: String, +m: Maybe<&2, String>) -> {Ps.cand.at(repo, m) == PackageSource.ps_cand.at(repo, m) : Maybe<&2, Ps.Hosted>}:
  match m:
    case None{}:
      {==}
    case Some{+r}:
      %Equal.sym(Maybe<&2, Ps.Hosted>, Ps.hosted(String.concat([repo, "#", r])), PackageSource.ps_hosted(String.concat([repo, "#", r])), psb.hosted(String.concat([repo, "#", r]))) : {Ps.keep(_, True{}) == PackageSource.ps_keep(PackageSource.ps_hosted(String.concat([repo, "#", r])), True{}) : Maybe<&2, Ps.Hosted>}
      psb.keep(PackageSource.ps_hosted(String.concat([repo, "#", r])), True{})

def psb.cand(+rd: Ps.Refd) -> {Ps.cand(rd) == PackageSource.ps_cand(rd) : Maybe<&2, Ps.Hosted>}:
  match rd:
    case Ps.Refd{+repo, +m}:
      psb.cand.at(repo, m)

def psb.https.at(+b: Bool, +r: String) -> {Ps.https.at(b, r) == PackageSource.ps_https.at(b, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def psb.https(+r: String) -> {Ps.https(r) == PackageSource.ps_https(r) : String}:
  psb.https.at(Bool.or(String.starts_with(r, "http://"), Bool.or(String.starts_with(r, "https://"), Bool.or(String.starts_with(r, "ssh://"), Bool.or(String.starts_with(r, "git://"), String.starts_with(r, "git@"))))), r)

def psb.or_ref(+a: Maybe<&2, String>, +b: Maybe<&2, String>) -> {Ps.or_ref(a, b) == PackageSource.ps_or_ref(a, b) : Maybe<&2, String>}:
  match a:
    case None{}:
      {==}
    case Some{+x}:
      {==}

def psb.from_hosted.at(+h: Ps.Hosted, +repo: String, +r: Maybe<&2, String>) -> {Ps.from_hosted.at(h, repo, r) == PackageSource.ps_from_hosted.at(h, repo, r) : Ps.GitSrc}:
  match h:
    case Ps.Hosted{+d, +u, +p, +k}:
      %Equal.sym(String, Ps.https(repo), PackageSource.ps_https(repo), psb.https(repo)) : {Ps.GitSrc{_, d, String.concat([u, "/", p]), Ps.or_ref(k, r), Bool.or(Ps.is_some(k), Ps.is_some(r))} == Ps.GitSrc{PackageSource.ps_https(repo), d, String.concat([u, "/", p]), PackageSource.ps_or_ref(k, r), Bool.or(PackageSource.ps_is_some(k), PackageSource.ps_is_some(r))} : Ps.GitSrc}
      %Equal.sym(Maybe<&2, String>, Ps.or_ref(k, r), PackageSource.ps_or_ref(k, r), psb.or_ref(k, r)) : {Ps.GitSrc{PackageSource.ps_https(repo), d, String.concat([u, "/", p]), _, Bool.or(Ps.is_some(k), Ps.is_some(r))} == Ps.GitSrc{PackageSource.ps_https(repo), d, String.concat([u, "/", p]), PackageSource.ps_or_ref(k, r), Bool.or(PackageSource.ps_is_some(k), PackageSource.ps_is_some(r))} : Ps.GitSrc}
      %Equal.sym(Bool, Ps.is_some(k), PackageSource.ps_is_some(k), psb.is_some(k)) : {Ps.GitSrc{PackageSource.ps_https(repo), d, String.concat([u, "/", p]), PackageSource.ps_or_ref(k, r), Bool.or(_, Ps.is_some(r))} == Ps.GitSrc{PackageSource.ps_https(repo), d, String.concat([u, "/", p]), PackageSource.ps_or_ref(k, r), Bool.or(PackageSource.ps_is_some(k), PackageSource.ps_is_some(r))} : Ps.GitSrc}
      %Equal.sym(Bool, Ps.is_some(r), PackageSource.ps_is_some(r), psb.is_some(r)) : {Ps.GitSrc{PackageSource.ps_https(repo), d, String.concat([u, "/", p]), PackageSource.ps_or_ref(k, r), Bool.or(PackageSource.ps_is_some(k), _)} == Ps.GitSrc{PackageSource.ps_https(repo), d, String.concat([u, "/", p]), PackageSource.ps_or_ref(k, r), Bool.or(PackageSource.ps_is_some(k), PackageSource.ps_is_some(r))} : Ps.GitSrc}
      {==}

def psb.from_hosted(+h: Ps.Hosted, +rd: Ps.Refd) -> {Ps.from_hosted(h, rd) == PackageSource.ps_from_hosted(h, rd) : Ps.GitSrc}:
  match rd:
    case Ps.Refd{+repo, +r}:
      psb.from_hosted.at(h, repo, r)

def psb.lslash.at(+b: Bool, +c: Char, +t: String, +r: String) -> {Ps.lslash.at(b, c, t, r) == PackageSource.ps_lslash.at(b, c, t, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def psb.lslash(+s: String) -> {Ps.lslash(s) == PackageSource.ps_lslash(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Ps.lslash(t), PackageSource.ps_lslash(t), psb.lslash(t)) : {Ps.lslash.at(Char.is_eq(c, '/'), c, t, _) == PackageSource.ps_lslash.at(Char.is_eq(c, '/'), c, t, PackageSource.ps_lslash(t)) : String}
      psb.lslash.at(Char.is_eq(c, '/'), c, t, PackageSource.ps_lslash(t))

def psb.shape.at(+bad: Bool, +h: String, +q: String, +clone: String, +r: Maybe<&2, String>) -> {Ps.shape.at(bad, h, q, clone, r) == PackageSource.ps_shape.at(bad, h, q, clone, r) : Maybe<&2, Ps.GitSrc>}:
  match bad:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Ps.is_some(r), PackageSource.ps_is_some(r), psb.is_some(r)) : {Some{Ps.GitSrc{clone, h, q, r, _}} == Some{Ps.GitSrc{clone, h, q, r, PackageSource.ps_is_some(r)}} : Maybe<&2, Ps.GitSrc>}
      {==}

def psb.shape(+h: String, +p: String, +clone: String, +r: Maybe<&2, String>) -> {Ps.shape(h, p, clone, r) == PackageSource.ps_shape(h, p, clone, r) : Maybe<&2, Ps.GitSrc>}:
  %Equal.sym(String, Ps.unsuffix(p), PackageSource.ps_unsuffix(p), psb.unsuffix(p)) : {Ps.shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(Ps.lslash(_)), Bool.not(Ps.has(Ps.lslash(Ps.unsuffix(p)), '/')))), h, Ps.lslash(Ps.unsuffix(p)), clone, r) == PackageSource.ps_shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')))), h, PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), clone, r) : Maybe<&2, Ps.GitSrc>}
  %Equal.sym(String, Ps.lslash(PackageSource.ps_unsuffix(p)), PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), psb.lslash(PackageSource.ps_unsuffix(p))) : {Ps.shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(_), Bool.not(Ps.has(Ps.lslash(Ps.unsuffix(p)), '/')))), h, Ps.lslash(Ps.unsuffix(p)), clone, r) == PackageSource.ps_shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')))), h, PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), clone, r) : Maybe<&2, Ps.GitSrc>}
  %Equal.sym(String, Ps.unsuffix(p), PackageSource.ps_unsuffix(p), psb.unsuffix(p)) : {Ps.shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(Ps.has(Ps.lslash(_), '/')))), h, Ps.lslash(Ps.unsuffix(p)), clone, r) == PackageSource.ps_shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')))), h, PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), clone, r) : Maybe<&2, Ps.GitSrc>}
  %Equal.sym(String, Ps.lslash(PackageSource.ps_unsuffix(p)), PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), psb.lslash(PackageSource.ps_unsuffix(p))) : {Ps.shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(Ps.has(_, '/')))), h, Ps.lslash(Ps.unsuffix(p)), clone, r) == PackageSource.ps_shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')))), h, PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), clone, r) : Maybe<&2, Ps.GitSrc>}
  %Equal.sym(Bool, Ps.has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/'), PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/'), psb.has_orig(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')) : {Ps.shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(_))), h, Ps.lslash(Ps.unsuffix(p)), clone, r) == PackageSource.ps_shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')))), h, PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), clone, r) : Maybe<&2, Ps.GitSrc>}
  %Equal.sym(String, Ps.unsuffix(p), PackageSource.ps_unsuffix(p), psb.unsuffix(p)) : {Ps.shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')))), h, Ps.lslash(_), clone, r) == PackageSource.ps_shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')))), h, PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), clone, r) : Maybe<&2, Ps.GitSrc>}
  %Equal.sym(String, Ps.lslash(PackageSource.ps_unsuffix(p)), PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), psb.lslash(PackageSource.ps_unsuffix(p))) : {Ps.shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')))), h, _, clone, r) == PackageSource.ps_shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')))), h, PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), clone, r) : Maybe<&2, Ps.GitSrc>}
  psb.shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')))), h, PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), clone, r)

def psb.generic.scp(+m: Maybe<&2, Ps.Cut>, +repo: String, +r: Maybe<&2, String>) -> {Ps.generic.scp(m, repo, r) == PackageSource.ps_generic.scp(m, repo, r) : Maybe<&2, Ps.GitSrc>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+h, +p}:
          psb.shape(h, p, repo, r)

def psb.generic.dot(+ok: Bool, +h: String, +p: String, +repo: String, +r: Maybe<&2, String>) -> {Ps.generic.dot(ok, h, p, repo, r) == PackageSource.ps_generic.dot(ok, h, p, repo, r) : Maybe<&2, Ps.GitSrc>}:
  match ok:
    case True{}:
      psb.shape(h, p, String.append("https://", repo), r)
    case False{}:
      {==}

def psb.generic.short(+m: Maybe<&2, Ps.Cut>, +repo: String, +r: Maybe<&2, String>) -> {Ps.generic.short(m, repo, r) == PackageSource.ps_generic.short(m, repo, r) : Maybe<&2, Ps.GitSrc>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+h, +p}:
          %Equal.sym(Bool, Ps.has(h, '.'), PackageSource.ps_has(h, '.'), psb.has_orig(h, '.')) : {Ps.generic.dot(Bool.or(_, String.eq(h, "localhost")), h, p, repo, r) == PackageSource.ps_generic.dot(Bool.or(PackageSource.ps_has(h, '.'), String.eq(h, "localhost")), h, p, repo, r) : Maybe<&2, Ps.GitSrc>}
          psb.generic.dot(Bool.or(PackageSource.ps_has(h, '.'), String.eq(h, "localhost")), h, p, repo, r)

def psb.before.at(+b: Bool, +c: Char, +r: String) -> {Ps.before.at(b, c, r) == PackageSource.ps_before.at(b, c, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def psb.before(+s: String, +sep: Char) -> {Ps.before(s, sep) == PackageSource.ps_before(s, sep) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Ps.before(t, sep), PackageSource.ps_before(t, sep), psb.before(t, sep)) : {Ps.before.at(Char.is_eq(c, sep), c, _) == PackageSource.ps_before.at(Char.is_eq(c, sep), c, PackageSource.ps_before(t, sep)) : String}
      psb.before.at(Char.is_eq(c, sep), c, PackageSource.ps_before(t, sep))

def psb.host_of(+a: String) -> {Ps.host_of(a) == PackageSource.ps_host_of(a) : String}:
  %Equal.sym(String, Ps.before(String.reverse(a), '@'), PackageSource.ps_before(String.reverse(a), '@'), psb.before(String.reverse(a), '@')) : {Ps.before(String.reverse(_), ':') == PackageSource.ps_before(String.reverse(PackageSource.ps_before(String.reverse(a), '@')), ':') : String}
  psb.before(String.reverse(PackageSource.ps_before(String.reverse(a), '@')), ':')

def psb.generic.url(+m: Maybe<&2, Ps.Url>, +repo: String, +r: Maybe<&2, String>) -> {Ps.generic.url(m, repo, r) == PackageSource.ps_generic.url(m, repo, r) : Maybe<&2, Ps.GitSrc>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Url{+sc, +a, +p}:
          %Equal.sym(String, Ps.host_of(a), PackageSource.ps_host_of(a), psb.host_of(a)) : {Ps.shape(_, Ps.lslash(p), repo, r) == PackageSource.ps_shape(PackageSource.ps_host_of(a), PackageSource.ps_lslash(p), repo, r) : Maybe<&2, Ps.GitSrc>}
          %Equal.sym(String, Ps.lslash(p), PackageSource.ps_lslash(p), psb.lslash(p)) : {Ps.shape(PackageSource.ps_host_of(a), _, repo, r) == PackageSource.ps_shape(PackageSource.ps_host_of(a), PackageSource.ps_lslash(p), repo, r) : Maybe<&2, Ps.GitSrc>}
          psb.shape(PackageSource.ps_host_of(a), PackageSource.ps_lslash(p), repo, r)

def psb.url.at(+sc: String, +m: Maybe<&2, Ps.Cut>) -> {Ps.url.at(sc, m) == PackageSource.ps_url.at(sc, m) : Maybe<&2, Ps.Url>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+a, +p}:
          {==}

def psb.url.of(+m: Maybe<&2, Ps.Cut>) -> {Ps.url.of(m) == PackageSource.ps_url.of(m) : Maybe<&2, Ps.Url>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+sc, +rest}:
          %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(rest, '/'), PackageSource.ps_cut(rest, '/'), psb.cut(rest, '/')) : {Ps.url.at(sc, _) == PackageSource.ps_url.at(sc, PackageSource.ps_cut(rest, '/')) : Maybe<&2, Ps.Url>}
          psb.url.at(sc, PackageSource.ps_cut(rest, '/'))

def psb.url(+s: String) -> {Ps.url(s) == PackageSource.ps_url(s) : Maybe<&2, Ps.Url>}:
  %Equal.sym(Maybe<&2, Ps.Cut>, Ps.proto(s), PackageSource.ps_proto(s), psb.proto(s)) : {Ps.url.of(_) == PackageSource.ps_url.of(PackageSource.ps_proto(s)) : Maybe<&2, Ps.Url>}
  psb.url.of(PackageSource.ps_proto(s))

def psb.generic.at(+scp: Bool, +pu: Bool, +repo: String, +r: Maybe<&2, String>) -> {Ps.generic.at(scp, pu, repo, r) == PackageSource.ps_generic.at(scp, pu, repo, r) : Maybe<&2, Ps.GitSrc>}:
  match scp:
    case True{}:
      %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(String.drop(repo, 4n), ':'), PackageSource.ps_cut(String.drop(repo, 4n), ':'), psb.cut(String.drop(repo, 4n), ':')) : {Ps.generic.scp(_, repo, r) == PackageSource.ps_generic.scp(PackageSource.ps_cut(String.drop(repo, 4n), ':'), repo, r) : Maybe<&2, Ps.GitSrc>}
      psb.generic.scp(PackageSource.ps_cut(String.drop(repo, 4n), ':'), repo, r)
    case False{}:
      match pu:
        case True{}:
          %Equal.sym(Maybe<&2, Ps.Url>, Ps.url(repo), PackageSource.ps_url(repo), psb.url(repo)) : {Ps.generic.url(_, repo, r) == PackageSource.ps_generic.url(PackageSource.ps_url(repo), repo, r) : Maybe<&2, Ps.GitSrc>}
          psb.generic.url(PackageSource.ps_url(repo), repo, r)
        case False{}:
          %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(repo, '/'), PackageSource.ps_cut(repo, '/'), psb.cut(repo, '/')) : {Ps.generic.short(_, repo, r) == PackageSource.ps_generic.short(PackageSource.ps_cut(repo, '/'), repo, r) : Maybe<&2, Ps.GitSrc>}
          psb.generic.short(PackageSource.ps_cut(repo, '/'), repo, r)

def psb.proto_url(+s: String) -> {Ps.proto_url(s) == PackageSource.ps_proto_url(s) : Bool}:
  {==}

def psb.generic(+rd: Ps.Refd) -> {Ps.generic(rd) == PackageSource.ps_generic(rd) : Maybe<&2, Ps.GitSrc>}:
  match rd:
    case Ps.Refd{+repo, +r}:
      %Equal.sym(Bool, Ps.proto_url(repo), PackageSource.ps_proto_url(repo), psb.proto_url(repo)) : {Ps.generic.at(String.starts_with(repo, "git@"), _, repo, r) == PackageSource.ps_generic.at(String.starts_with(repo, "git@"), PackageSource.ps_proto_url(repo), repo, r) : Maybe<&2, Ps.GitSrc>}
      psb.generic.at(String.starts_with(repo, "git@"), PackageSource.ps_proto_url(repo), repo, r)

def psb.found.at(+m: Maybe<&2, Ps.Hosted>, +rd: Ps.Refd) -> {Ps.found.at(m, rd) == PackageSource.ps_found.at(m, rd) : Maybe<&2, Ps.GitSrc>}:
  match m:
    case None{}:
      psb.generic(rd)
    case Some{+h}:
      %Equal.sym(Ps.GitSrc, Ps.from_hosted(h, rd), PackageSource.ps_from_hosted(h, rd), psb.from_hosted(h, rd)) : {Some{_} == Some{PackageSource.ps_from_hosted(h, rd)} : Maybe<&2, Ps.GitSrc>}
      {==}

def psb.pick(+a: Maybe<&2, Ps.Hosted>, +b: Maybe<&2, Ps.Hosted>) -> {Ps.pick(a, b) == PackageSource.ps_pick(a, b) : Maybe<&2, Ps.Hosted>}:
  match a:
    case None{}:
      {==}
    case Some{+h}:
      {==}

def psb.ref_some(+rd: Ps.Refd) -> {Ps.ref_some(rd) == PackageSource.ps_ref_some(rd) : Bool}:
  match rd:
    case Ps.Refd{+repo, +m}:
      psb.is_some(m)

def psb.found(+u: String, +rd: Ps.Refd) -> {Ps.found(u, rd) == PackageSource.ps_found(u, rd) : Maybe<&2, Ps.GitSrc>}:
  %Equal.sym(Maybe<&2, Ps.Hosted>, Ps.cand(rd), PackageSource.ps_cand(rd), psb.cand(rd)) : {Ps.found.at(Ps.pick(_, Ps.keep(Ps.hosted(u), Ps.ref_some(rd))), rd) == PackageSource.ps_found.at(PackageSource.ps_pick(PackageSource.ps_cand(rd), PackageSource.ps_keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd))), rd) : Maybe<&2, Ps.GitSrc>}
  %Equal.sym(Maybe<&2, Ps.Hosted>, Ps.hosted(u), PackageSource.ps_hosted(u), psb.hosted(u)) : {Ps.found.at(Ps.pick(PackageSource.ps_cand(rd), Ps.keep(_, Ps.ref_some(rd))), rd) == PackageSource.ps_found.at(PackageSource.ps_pick(PackageSource.ps_cand(rd), PackageSource.ps_keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd))), rd) : Maybe<&2, Ps.GitSrc>}
  %Equal.sym(Bool, Ps.ref_some(rd), PackageSource.ps_ref_some(rd), psb.ref_some(rd)) : {Ps.found.at(Ps.pick(PackageSource.ps_cand(rd), Ps.keep(PackageSource.ps_hosted(u), _)), rd) == PackageSource.ps_found.at(PackageSource.ps_pick(PackageSource.ps_cand(rd), PackageSource.ps_keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd))), rd) : Maybe<&2, Ps.GitSrc>}
  %Equal.sym(Maybe<&2, Ps.Hosted>, Ps.keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd)), PackageSource.ps_keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd)), psb.keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd))) : {Ps.found.at(Ps.pick(PackageSource.ps_cand(rd), _), rd) == PackageSource.ps_found.at(PackageSource.ps_pick(PackageSource.ps_cand(rd), PackageSource.ps_keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd))), rd) : Maybe<&2, Ps.GitSrc>}
  %Equal.sym(Maybe<&2, Ps.Hosted>, Ps.pick(PackageSource.ps_cand(rd), PackageSource.ps_keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd))), PackageSource.ps_pick(PackageSource.ps_cand(rd), PackageSource.ps_keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd))), psb.pick(PackageSource.ps_cand(rd), PackageSource.ps_keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd)))) : {Ps.found.at(_, rd) == PackageSource.ps_found.at(PackageSource.ps_pick(PackageSource.ps_cand(rd), PackageSource.ps_keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd))), rd) : Maybe<&2, Ps.GitSrc>}
  psb.found.at(PackageSource.ps_pick(PackageSource.ps_cand(rd), PackageSource.ps_keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd))), rd)

def psb.refcut.ok(+e: Bool, +a: String, +b: String) -> {Ps.refcut.ok(e, a, b) == PackageSource.ps_refcut.ok(e, a, b) : Maybe<&2, Ps.Cut>}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def psb.refcut.at(+m: Maybe<&2, Ps.Cut>) -> {Ps.refcut.at(m) == PackageSource.ps_refcut.at(m) : Maybe<&2, Ps.Cut>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+a, +b}:
          psb.refcut.ok(Bool.or(String.is_empty(a), String.is_empty(b)), a, b)

def psb.refcut(+s: String) -> {Ps.refcut(s) == PackageSource.ps_refcut(s) : Maybe<&2, Ps.Cut>}:
  %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(s, '@'), PackageSource.ps_cut(s, '@'), psb.cut(s, '@')) : {Ps.refcut.at(_) == PackageSource.ps_refcut.at(PackageSource.ps_cut(s, '@')) : Maybe<&2, Ps.Cut>}
  psb.refcut.at(PackageSource.ps_cut(s, '@'))

def psb.sref.scp.at(+h: String, +m: Maybe<&2, Ps.Cut>, +u: String) -> {Ps.sref.scp.at(h, m, u) == PackageSource.ps_sref.scp.at(h, m, u) : Ps.Refd}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+p, +r}:
          {==}

def psb.sref.short.at(+h: String, +m: Maybe<&2, Ps.Cut>, +u: String) -> {Ps.sref.short.at(h, m, u) == PackageSource.ps_sref.short.at(h, m, u) : Ps.Refd}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+p, +r}:
          {==}

def psb.sref.short(+m: Maybe<&2, Ps.Cut>, +u: String) -> {Ps.sref.short(m, u) == PackageSource.ps_sref.short(m, u) : Ps.Refd}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+h, +p}:
          %Equal.sym(Maybe<&2, Ps.Cut>, Ps.refcut(p), PackageSource.ps_refcut(p), psb.refcut(p)) : {Ps.sref.short.at(h, _, u) == PackageSource.ps_sref.short.at(h, PackageSource.ps_refcut(p), u) : Ps.Refd}
          psb.sref.short.at(h, PackageSource.ps_refcut(p), u)

def psb.sref.url.at(+sc: String, +a: String, +m: Maybe<&2, Ps.Cut>, +u: String) -> {Ps.sref.url.at(sc, a, m, u) == PackageSource.ps_sref.url.at(sc, a, m, u) : Ps.Refd}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+p, +r}:
          {==}

def psb.sref.url(+m: Maybe<&2, Ps.Url>, +u: String) -> {Ps.sref.url(m, u) == PackageSource.ps_sref.url(m, u) : Ps.Refd}:
  match m:
    case None{}:
      %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(u, '/'), PackageSource.ps_cut(u, '/'), psb.cut(u, '/')) : {Ps.sref.short(_, u) == PackageSource.ps_sref.short(PackageSource.ps_cut(u, '/'), u) : Ps.Refd}
      psb.sref.short(PackageSource.ps_cut(u, '/'), u)
    case Some{+x}:
      match x:
        case Ps.Url{+sc, +a, +p}:
          %Equal.sym(String, Ps.lslash(p), PackageSource.ps_lslash(p), psb.lslash(p)) : {Ps.sref.url.at(sc, a, Ps.refcut(_), u) == PackageSource.ps_sref.url.at(sc, a, PackageSource.ps_refcut(PackageSource.ps_lslash(p)), u) : Ps.Refd}
          %Equal.sym(Maybe<&2, Ps.Cut>, Ps.refcut(PackageSource.ps_lslash(p)), PackageSource.ps_refcut(PackageSource.ps_lslash(p)), psb.refcut(PackageSource.ps_lslash(p))) : {Ps.sref.url.at(sc, a, _, u) == PackageSource.ps_sref.url.at(sc, a, PackageSource.ps_refcut(PackageSource.ps_lslash(p)), u) : Ps.Refd}
          psb.sref.url.at(sc, a, PackageSource.ps_refcut(PackageSource.ps_lslash(p)), u)

def psb.sref.scp(+m: Maybe<&2, Ps.Cut>, +u: String) -> {Ps.sref.scp(m, u) == PackageSource.ps_sref.scp(m, u) : Ps.Refd}:
  match m:
    case None{}:
      %Equal.sym(Maybe<&2, Ps.Url>, Ps.url(u), PackageSource.ps_url(u), psb.url(u)) : {Ps.sref.url(_, u) == PackageSource.ps_sref.url(PackageSource.ps_url(u), u) : Ps.Refd}
      psb.sref.url(PackageSource.ps_url(u), u)
    case Some{+x}:
      match x:
        case Ps.Cut{+h, +p}:
          %Equal.sym(Maybe<&2, Ps.Cut>, Ps.refcut(p), PackageSource.ps_refcut(p), psb.refcut(p)) : {Ps.sref.scp.at(h, _, u) == PackageSource.ps_sref.scp.at(h, PackageSource.ps_refcut(p), u) : Ps.Refd}
          psb.sref.scp.at(h, PackageSource.ps_refcut(p), u)

def psb.sref.at(+b: Bool, +u: String) -> {Ps.sref.at(b, u) == PackageSource.ps_sref.at(b, u) : Ps.Refd}:
  match b:
    case True{}:
      %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(String.drop(u, 4n), ':'), PackageSource.ps_cut(String.drop(u, 4n), ':'), psb.cut(String.drop(u, 4n), ':')) : {Ps.sref.scp(_, u) == PackageSource.ps_sref.scp(PackageSource.ps_cut(String.drop(u, 4n), ':'), u) : Ps.Refd}
      psb.sref.scp(PackageSource.ps_cut(String.drop(u, 4n), ':'), u)
    case False{}:
      %Equal.sym(Maybe<&2, Ps.Url>, Ps.url(u), PackageSource.ps_url(u), psb.url(u)) : {Ps.sref.url(_, u) == PackageSource.ps_sref.url(PackageSource.ps_url(u), u) : Ps.Refd}
      psb.sref.url(PackageSource.ps_url(u), u)

def psb.sref(+u: String) -> {Ps.sref(u) == PackageSource.ps_sref(u) : Ps.Refd}:
  psb.sref.at(String.starts_with(u, "git@"), u)

def psb.git.gate(+go: Bool, +u: String) -> {Ps.git.gate(go, u) == PackageSource.ps_git.gate(go, u) : Ps.GitAns}:
  match go:
    case True{}:
      %Equal.sym(Ps.Refd, Ps.sref(u), PackageSource.ps_sref(u), psb.sref(u)) : {Ps.checked(Ps.found(u, _)) == PackageSource.ps_checked(PackageSource.ps_found(u, PackageSource.ps_sref(u))) : Ps.GitAns}
      %Equal.sym(Maybe<&2, Ps.GitSrc>, Ps.found(u, PackageSource.ps_sref(u)), PackageSource.ps_found(u, PackageSource.ps_sref(u)), psb.found(u, PackageSource.ps_sref(u))) : {Ps.checked(_) == PackageSource.ps_checked(PackageSource.ps_found(u, PackageSource.ps_sref(u))) : Ps.GitAns}
      psb.checked_orig(PackageSource.ps_found(u, PackageSource.ps_sref(u)))
    case False{}:
      {==}

def psb.git.at_orig(+b: Bool, +t: String) -> {Ps.git.at(b, t) == PackageSource.ps_git.at(b, t) : Ps.GitAns}:
  match b:
    case True{}:
      %Equal.sym(String, Ps.trim(String.drop(t, 4n)), PackageSource.ps_trim(String.drop(t, 4n)), psb.trim(String.drop(t, 4n))) : {Ps.git.gate(True{}, _) == PackageSource.ps_git.gate(True{}, PackageSource.ps_trim(String.drop(t, 4n))) : Ps.GitAns}
      psb.git.gate(True{}, PackageSource.ps_trim(String.drop(t, 4n)))
    case False{}:
      %Equal.sym(Bool, Ps.proto_url(t), PackageSource.ps_proto_url(t), psb.proto_url(t)) : {Ps.git.gate(_, t) == PackageSource.ps_git.gate(PackageSource.ps_proto_url(t), t) : Ps.GitAns}
      psb.git.gate(PackageSource.ps_proto_url(t), t)

def psb.git_orig(+s: String) -> {Ps.git(s) == PackageSource.ps_git(s) : Ps.GitAns}:
  %Equal.sym(String, Ps.trim(s), PackageSource.ps_trim(s), psb.trim(s)) : {Ps.git.at(String.starts_with(_, "git:"), Ps.trim(s)) == PackageSource.ps_git.at(String.starts_with(PackageSource.ps_trim(s), "git:"), PackageSource.ps_trim(s)) : Ps.GitAns}
  %Equal.sym(String, Ps.trim(s), PackageSource.ps_trim(s), psb.trim(s)) : {Ps.git.at(String.starts_with(PackageSource.ps_trim(s), "git:"), _) == PackageSource.ps_git.at(String.starts_with(PackageSource.ps_trim(s), "git:"), PackageSource.ps_trim(s)) : Ps.GitAns}
  psb.git.at_orig(String.starts_with(PackageSource.ps_trim(s), "git:"), PackageSource.ps_trim(s))

def psb.source.git(+a: Ps.GitAns, +s: String) -> {Ps.source.git(a, s) == PackageSource.ps_source.git(a, s) : Ps.Parsed}:
  match a:
    case Ps.NoGit{}:
      {==}
    case Ps.IsGit{+g}:
      {==}
    case Ps.BadGit{+f}:
      {==}

def psb.source.local(+b: Bool, +s: String) -> {Ps.source.local(b, s) == PackageSource.ps_source.local(b, s) : Ps.Parsed}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Ps.GitAns, Ps.git(s), PackageSource.ps_git(s), psb.git_orig(s)) : {Ps.source.git(_, s) == PackageSource.ps_source.git(PackageSource.ps_git(s), s) : Ps.Parsed}
      psb.source.git(PackageSource.ps_git(s), s)

def psb.source.at(+b: Bool, +s: String) -> {Ps.source.at(b, s) == PackageSource.ps_source.at(b, s) : Ps.Parsed}:
  match b:
    case True{}:
      %Equal.sym(String, Ps.trim(String.drop(s, 4n)), PackageSource.ps_trim(String.drop(s, 4n)), psb.trim(String.drop(s, 4n))) : {Ps.npm(_) == PackageSource.ps_npm(PackageSource.ps_trim(String.drop(s, 4n))) : Ps.Parsed}
      psb.npm(PackageSource.ps_trim(String.drop(s, 4n)))
    case False{}:
      %Equal.sym(Bool, Ps.local(s), PackageSource.ps_local(s), psb.local_orig(s)) : {Ps.source.local(_, s) == PackageSource.ps_source.local(PackageSource.ps_local(s), s) : Ps.Parsed}
      psb.source.local(PackageSource.ps_local(s), s)

def psb.source(+s: String) -> {Ps.source(s) == PackageSource.ps_source(s) : Ps.Parsed}:
  psb.source.at(String.starts_with(s, "npm:"), s)
