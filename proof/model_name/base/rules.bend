# eukhe: lemmas of the model_name proofs: each rule kind against its
# splits. For each kind, *_sp: what the code answers True for is a split of
# the name (the predicate is indexed by the code's answer); *_app / *_in: a
# split of the name makes the code answer True.

import Base
import ../../../bend/text_pat.bend as Tp
import ../../../bend/phrase.bend as P
import ../../../bend/model_name.bend as M
import ../../../laws/model_name.bend as ModelName
import ../base.bend as LA

# Lists of strings
# ----------------

def mnr.and_lt(n: Bool, -l: Bool, en: {n == True{} : Bool}, el: {l == True{} : Bool}) -> {P.pm.and(n, v => l) == True{} : Bool}:
  match n:
    case True{}:
      el
    case False{}:
      LA.mnb.absurd_f({P.pm.and(False{}, v => l) == True{} : Bool}, en)

# R3: starts
def mnr.HeadsP(ps: List<&2, String>, s: String, b: Bool) -> Type:
  match b:
    case True{}:
      Sigma<&1, &1, List<&2, String>, pre => Sigma<&1, &1, String, p => Sigma<&1, &1, List<&2, String>, post => Sigma<&1, &1, String, c => {ps == List.append(&2, String, pre, p <> post) : List<&2, String>} & {s == String.append(p, c) : String}>>>>
    case False{}:
      Unit

def mnr.heads_next(+q: String, +more: List<&2, String>, -s: String, b2: Bool, v2: mnr.HeadsP(more, s, b2)) -> mnr.HeadsP(q <> more, s, b2):
  match b2:
    case True{}:
      (+pre, (+p, (+post, (+c, (e1, e2))))) = v2
      (q <> pre, (p, (post, (c, (LA.mnb.lcons_eq(q, more, List.append(&2, String, pre, p <> post), e1), e2)))))
    case False{}:
      Unit{}

def mnr.heads_at(+q: String, +more: List<&2, String>, +s: String, m: Maybe<&2, String>, v: LA.mnb.SP(q, s, m), b2: Bool, v2: mnr.HeadsP(more, s, b2)) -> mnr.HeadsP(q <> more, s, P.pm.or(M.got(m), u => b2)):
  match m:
    case None{}:
      mnr.heads_next(q, more, s, b2, v2)
    case Some{+r}:
      (Nil{}, (q, (more, (r, ({==}, v)))))

# a list of heads found: s begins with one of them
def mnr.heads_sp(ps: List<&2, String>, +s: String) -> mnr.HeadsP(ps, s, M.heads(ps, s)):
  match ps:
    case Nil{}:
      Unit{}
    case +q <> +more:
      mnr.heads_at(q, more, s, M.strip(q, s), LA.mnb.sp(q, s), M.heads(more, s), mnr.heads_sp(more, s))

def mnr.heads_in(pre: List<&2, String>, +p: String, +post: List<&2, String>, +s: String, h: {M.got(M.strip(p, s)) == True{} : Bool}) -> {M.heads(List.append(&2, String, pre, p <> post), s) == True{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, M.got(M.strip(p, s)), True{}, h) : {P.pm.or(_, u => M.heads(post, s)) == True{} : Bool}
      {==}
    case +q <> more:
      LA.mnb.or_rl(M.got(M.strip(q, s)), M.heads(List.append(&2, String, more, p <> post), s), mnr.heads_in(more, p, post, s, h))

# R2: is
def mnr.IssP(ps: List<&2, String>, s: String, b: Bool) -> Type:
  match b:
    case True{}:
      Sigma<&1, &1, List<&2, String>, pre => Sigma<&1, &1, List<&2, String>, post => {ps == List.append(&2, String, pre, s <> post) : List<&2, String>}>>
    case False{}:
      Unit

def mnr.iss_next(+q: String, +more: List<&2, String>, -s: String, b2: Bool, v2: mnr.IssP(more, s, b2)) -> mnr.IssP(q <> more, s, b2):
  match b2:
    case True{}:
      (+pre, (+post, e1)) = v2
      (q <> pre, (post, LA.mnb.lcons_eq(q, more, List.append(&2, String, pre, s <> post), e1)))
    case False{}:
      Unit{}

def mnr.iss_eq(+q: String, +more: List<&2, String>, +s: String, v: {s == String.append(q, SNil{}) : String}) -> {q <> more == s <> more : List<&2, String>}:
  +e = Equal.trans(String, s, String.append(q, SNil{}), q, v, LA.mnb.app_nil(q))
  Equal.cong(String, List<&2, String>, z => z <> more, q, s, Equal.sym(String, s, q, e))

def mnr.iss_some(+q: String, +more: List<&2, String>, +s: String, r: String, v: {s == String.append(q, r) : String}, b2: Bool, v2: mnr.IssP(more, s, b2)) -> mnr.IssP(q <> more, s, P.pm.or(String.is_empty(r), u => b2)):
  match r:
    case SNil{}:
      (Nil{}, (more, mnr.iss_eq(q, more, s, v)))
    case SCon{x, t}:
      mnr.iss_next(q, more, s, b2, v2)

def mnr.iss_at(+q: String, +more: List<&2, String>, +s: String, m: Maybe<&2, String>, v: LA.mnb.SP(q, s, m), b2: Bool, v2: mnr.IssP(more, s, b2)) -> mnr.IssP(q <> more, s, P.pm.or(M.got_all(m), u => b2)):
  match m:
    case None{}:
      mnr.iss_next(q, more, s, b2, v2)
    case Some{r}:
      mnr.iss_some(q, more, s, r, v, b2, v2)

# a list whose one string is s found: s is one of them
def mnr.iss_sp(ps: List<&2, String>, +s: String) -> mnr.IssP(ps, s, M.iss(ps, s)):
  match ps:
    case Nil{}:
      Unit{}
    case +q <> +more:
      mnr.iss_at(q, more, s, M.strip(q, s), LA.mnb.sp(q, s), M.iss(more, s), mnr.iss_sp(more, s))

# s strips whole off itself
def mnr.strip_self(+s: String) -> {M.strip(s, s) == Some{SNil{}} : Maybe<&2, String>}:
  %LA.mnb.app_nil(s) : {M.strip(s, _) == Some{SNil{}} : Maybe<&2, String>}
  LA.mnb.strip_app(s, SNil{})

def mnr.iss_in(pre: List<&2, String>, +s: String, +post: List<&2, String>) -> {M.iss(List.append(&2, String, pre, s <> post), s) == True{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Maybe<&2, String>, M.strip(s, s), Some{SNil{}}, mnr.strip_self(s)) : {P.pm.or(M.got_all(_), u => M.iss(post, s)) == True{} : Bool}
      {==}
    case +q <> more:
      LA.mnb.or_rl(M.got_all(M.strip(q, s)), M.iss(List.append(&2, String, more, s <> post), s), mnr.iss_in(more, s, post))

# R4: then
# --------

def mnr.LineP(b: String, s: String, v: Bool) -> Type:
  match v:
    case True{}:
      Sigma<&1, &1, String, y => Sigma<&1, &1, String, z => {s == String.append(y, String.append(b, z)) : String} & {ModelName.sp_no_lf(y) == True{} : Bool}>>
    case False{}:
      Unit

def mnr.line_at(+b: String, +s: String, m: Maybe<&2, String>, v: LA.mnb.SP(b, s, m)) -> mnr.LineP(b, s, M.got(m)):
  match m:
    case None{}:
      Unit{}
    case Some{+r}:
      (SNil{}, (r, (v, {==})))

def mnr.line_more(x: Char, -t: String, -b: String, c: Bool, ec: {Bool.not(Char.is_eq(x, '\n')) == c : Bool}, b2: Bool, v2: mnr.LineP(b, t, b2)) -> mnr.LineP(b, SCon{x, t}, P.pm.and(c, v => b2)):
  match x:
    case Chr{+xc}:
      match c:
        case True{}:
          match b2:
            case True{}:
              (+y, (+z, (e, n))) = v2
              (SCon{Chr{xc}, y}, (z, (LA.mnb.cons_eq(Chr{xc}, t, String.append(y, String.append(b, z)), e), LA.mnb.and_t(Bool.not(U32.is_eq(xc, 10)), ModelName.sp_no_lf(y), ec, n))))
            case False{}:
              Unit{}
        case False{}:
          Unit{}

def mnr.line_or(+x: Char, -t: String, -b: String, b1: Bool, v1: mnr.LineP(b, SCon{x, t}, b1), b3: Bool, v3: mnr.LineP(b, SCon{x, t}, b3)) -> mnr.LineP(b, SCon{x, t}, P.pm.or(b1, u => b3)):
  match b1:
    case True{}:
      v1
    case False{}:
      v3

# a line part found: s holds b before its first line feed
def mnr.line_sp(+b: String, s: String) -> mnr.LineP(b, s, M.line_part(b, s)):
  match s:
    case SNil{}:
      mnr.line_at(b, SNil{}, M.strip(b, SNil{}), LA.mnb.sp(b, SNil{}))
    case SCon{+x, +t}:
      mnr.line_or(x, t, b, M.got(M.strip(b, SCon{x, t})), mnr.line_at(b, SCon{x, t}, M.strip(b, SCon{x, t}), LA.mnb.sp(b, SCon{x, t})), P.pm.and(Bool.not(Char.is_eq(x, '\n')), v => M.line_part(b, t)), mnr.line_more(x, t, b, Bool.not(Char.is_eq(x, '\n')), {==}, M.line_part(b, t), mnr.line_sp(b, t)))

def mnr.ThenP(a: String, b: String, s: String, v: Bool) -> Type:
  match v:
    case True{}:
      Sigma<&1, &1, String, x => Sigma<&1, &1, String, y => Sigma<&1, &1, String, z => {s == String.append(x, String.append(a, String.append(y, String.append(b, z)))) : String} & {ModelName.sp_no_lf(y) == True{} : Bool}>>>
    case False{}:
      Unit

def mnr.then_line(+a: String, +b: String, -s: String, +r: String, v: {s == String.append(a, r) : String}, c: Bool, lv: mnr.LineP(b, r, c)) -> mnr.ThenP(a, b, s, c):
  match c:
    case True{}:
      (+y, (+z, (e, n))) = lv
      (SNil{}, (y, (z, (Equal.trans(String, s, String.append(a, r), String.append(a, String.append(y, String.append(b, z))), v, Equal.cong(String, String, w => String.append(a, w), r, String.append(y, String.append(b, z)), e)), n))))
    case False{}:
      Unit{}

def mnr.then_at(+a: String, +b: String, -s: String, m: Maybe<&2, String>, v: LA.mnb.SP(a, s, m)) -> mnr.ThenP(a, b, s, M.then.at(m, b)):
  match m:
    case None{}:
      Unit{}
    case Some{+r}:
      mnr.then_line(a, b, s, r, v, M.line_part(b, r), mnr.line_sp(b, r))

def mnr.then_or(+x: Char, -t: String, -a: String, -b: String, b1: Bool, v1: mnr.ThenP(a, b, SCon{x, t}, b1), b2: Bool, v2: mnr.ThenP(a, b, t, b2)) -> mnr.ThenP(a, b, SCon{x, t}, P.pm.or(b1, u => b2)):
  match b1:
    case True{}:
      v1
    case False{}:
      match b2:
        case True{}:
          (+w, (+y, (+z, (e, n)))) = v2
          (SCon{x, w}, (y, (z, (LA.mnb.cons_eq(x, t, String.append(w, String.append(a, String.append(y, String.append(b, z)))), e), n))))
        case False{}:
          Unit{}

# a `then` found: a, then b on the same line
def mnr.then_sp(+a: String, +b: String, s: String) -> mnr.ThenP(a, b, s, M.then(a, b, s)):
  match s:
    case SNil{}:
      mnr.then_at(a, b, SNil{}, M.strip(a, SNil{}), LA.mnb.sp(a, SNil{}))
    case SCon{+x, +t}:
      mnr.then_or(x, t, a, b, M.then.at(M.strip(a, SCon{x, t}), b), mnr.then_at(a, b, SCon{x, t}, M.strip(a, SCon{x, t}), LA.mnb.sp(a, SCon{x, t})), M.then(a, b, t), mnr.then_sp(a, b, t))

def mnr.line_here(+b: String, s: String, h: {M.got(M.strip(b, s)) == True{} : Bool}) -> {M.line_part(b, s) == True{} : Bool}:
  match s:
    case SNil{}:
      h
    case SCon{+x, +t}:
      %Equal.sym(Bool, M.got(M.strip(b, SCon{x, t})), True{}, h) : {P.pm.or(_, u => P.pm.and(Bool.not(Char.is_eq(x, '\n')), v => M.line_part(b, t))) == True{} : Bool}
      {==}

# b after a text with no line feed is a line part
def mnr.line_app(y: String, +b: String, +z: String, h: {ModelName.sp_no_lf(y) == True{} : Bool}) -> {M.line_part(b, String.append(y, String.append(b, z))) == True{} : Bool}:
  match y:
    case SNil{}:
      mnr.line_here(b, String.append(b, z), LA.mnb.got_app(b, z))
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +hh = h
          +n = Bool.not(U32.is_eq(xc, 10))
          LA.mnb.or_rl(M.got(M.strip(b, SCon{Chr{xc}, String.append(t, String.append(b, z))})), P.pm.and(n, v => M.line_part(b, String.append(t, String.append(b, z)))), mnr.and_lt(n, M.line_part(b, String.append(t, String.append(b, z))), LA.mnb.and_l(n, ModelName.sp_no_lf(t), hh), mnr.line_app(t, b, z, LA.mnb.and_r(n, ModelName.sp_no_lf(t), hh))))

def mnr.then_here(+a: String, +b: String, s: String, h: {M.then.at(M.strip(a, s), b) == True{} : Bool}) -> {M.then(a, b, s) == True{} : Bool}:
  match s:
    case SNil{}:
      h
    case SCon{+x, +t}:
      %Equal.sym(Bool, M.then.at(M.strip(a, SCon{x, t}), b), True{}, h) : {P.pm.or(_, u => M.then(a, b, t)) == True{} : Bool}
      {==}

def mnr.then_strip(+a: String, +b: String, +r: String, h: {M.line_part(b, r) == True{} : Bool}) -> {M.then.at(M.strip(a, String.append(a, r)), b) == True{} : Bool}:
  %Equal.sym(Maybe<&2, String>, M.strip(a, String.append(a, r)), Some{r}, LA.mnb.strip_app(a, r)) : {M.then.at(_, b) == True{} : Bool}
  h

# a, then b on the same line, anywhere: then holds
def mnr.then_app(x: String, +a: String, +b: String, +y: String, +z: String, h: {ModelName.sp_no_lf(y) == True{} : Bool}) -> {M.then(a, b, String.append(x, String.append(a, String.append(y, String.append(b, z))))) == True{} : Bool}:
  match x:
    case SNil{}:
      +r = String.append(y, String.append(b, z))
      mnr.then_here(a, b, String.append(a, r), mnr.then_strip(a, b, r, mnr.line_app(y, b, z, h)))
    case SCon{+c, +t}:
      LA.mnb.or_rl(M.then.at(M.strip(a, SCon{c, String.append(t, String.append(a, String.append(y, String.append(b, z))))}), b), M.then(a, b, String.append(t, String.append(a, String.append(y, String.append(b, z))))), mnr.then_app(t, a, b, y, z, h))
