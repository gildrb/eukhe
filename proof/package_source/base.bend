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
