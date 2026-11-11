# eukhe: lemmas of the R2/R4/R6 laws of area child_env: the keep list and
# the registry are read by String.eq (reflexive, sound), the upper case of
# a name is env_case_eq's, a secret pattern is read by String.contains
# (holds p between any texts, and only so), and the filter is a mask.
#
# A recursive proof takes the value it inspects as a parameter (Bend
# matches only parameters), with an equation that names it; a step that
# recurses gets the recursion as a function.

import Base
import ../../../bend/child_env.bend as Env
import ../../../laws/child_env.bend as ChildEnv
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../base.bend as LA

# Logic
# -----

def pcn.or_r(a: Bool, -b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def pcn.or_l_false(a: Bool, -b: Bool, ea: {a == False{} : Bool}, h: {Bool.or(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      LA.pce.absurd({b == True{} : Bool}, ea)
    case False{}:
      h

def pcn.MI(m: Maybe<&2, String>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# None is not Some
def pcn.none_some(-G: Type, -p: String, e: {None{} == Some{p} : Maybe<&2, String>}) -> G:
  %e : pcn.MI(_, G)
  Unit{}

def pcn.val(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      ""
    case Some{x}:
      x

# Some is injective
def pcn.some_eq(-q: String, -p: String, e: {Some{q} == Some{p} : Maybe<&2, String>}) -> {q == p : String}:
  Equal.cong(Maybe<&2, String>, String, m => pcn.val(m), Some{q}, Some{p}, e)

# Equality of chars and strings
# -----------------------------

def pcn.word_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match b:
            case True{}:
              %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, pcn.word_refl(p, t)) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
              {==}
            case False{}:
              %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, pcn.word_refl(p, t)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
              {==}

def pcn.u32_refl(x: U32) -> {U32.cmp(x, x) == EQ{} : Cmp}:
  match x:
    case U32{w}:
      pcn.word_refl(32n, w)

# a char is the char it is
def pcn.char_refl(c: Char) -> {Char.is_eq(c, c) == True{} : Bool}:
  match c:
    case Chr{x}:
      %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, pcn.u32_refl(x)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# Char.is_eq is equality
def pcn.char_sound(+c: Char, +d: Char, e: {Char.is_eq(c, d) == True{} : Bool}) -> {c == d : Char}:
  match c d:
    case Chr{+x} Chr{+y}:
      Equal.cong(U32, Char, u => Chr{u}, x, y, PWireBoolExact.wr_eq_sound(x, y, e))

def pcn.str_go_refl(a: String) -> {String.order.go(a, a, EQ{}) == EQ{} : Cmp}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      match h:
        case Chr{x}:
          %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, pcn.u32_refl(x)) : {String.order.go(t, t, _) == EQ{} : Cmp}
          pcn.str_go_refl(t)

# String.eq(a, a) holds
def pcn.str_refl(a: String) -> {String.eq(a, a) == True{} : Bool}:
  %Equal.sym(Cmp, String.order.go(a, a, EQ{}), EQ{}, pcn.str_go_refl(a)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

def pcn.go_lt(a: String, b: String) -> {String.order.go(a, b, LT{}) == LT{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      {==}
    case SCon{h, t} SNil{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      {==}

def pcn.go_gt(a: String, b: String) -> {String.order.go(a, b, GT{}) == GT{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      {==}
    case SCon{h, t} SNil{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      {==}

def pcn.cmp_fin(+x: U32, +y: U32, t1: String, t2: String, c: Cmp, ec: {U32.cmp(x, y) == c : Cmp},
  rec: {String.order.go(t1, t2, EQ{}) == EQ{} : Cmp} -> {t1 == t2 : String},
  e: {String.order.go(t1, t2, c) == EQ{} : Cmp}) -> {SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}:
  match c:
    case LT{}:
      LA.pce.absurdF({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, Equal.cong(Cmp, Bool, k => Cmp.is_eq(k), LT{}, EQ{}, Equal.trans(Cmp, LT{}, String.order.go(t1, t2, LT{}), EQ{}, Equal.sym(Cmp, String.order.go(t1, t2, LT{}), LT{}, pcn.go_lt(t1, t2)), e)))
    case EQ{}:
      +ex = PWireBoolExact.wr_cmp_eq(x, y)(ec)
      +et = rec(e)
      %ex : {SCon{Chr{x}, t1} == SCon{Chr{_}, t2} : String}
      %et : {SCon{Chr{x}, t1} == SCon{Chr{x}, _} : String}
      {==}
    case GT{}:
      LA.pce.absurdF({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, Equal.cong(Cmp, Bool, k => Cmp.is_eq(k), GT{}, EQ{}, Equal.trans(Cmp, GT{}, String.order.go(t1, t2, GT{}), EQ{}, Equal.sym(Cmp, String.order.go(t1, t2, GT{}), GT{}, pcn.go_gt(t1, t2)), e)))

def pcn.str_go_eq(+a: String, +b: String) -> {String.order.go(a, b, EQ{}) == EQ{} : Cmp} -> {a == b : String}:
  match a b:
    case SNil{} SNil{}:
      e => {==}
    case SNil{} SCon{h, t}:
      e => LA.pce.absurdF({SNil{} == SCon{h, t} : String}, Equal.cong(Cmp, Bool, k => Cmp.is_eq(k), LT{}, EQ{}, e))
    case SCon{h, t} SNil{}:
      e => LA.pce.absurdF({SCon{h, t} == SNil{} : String}, Equal.cong(Cmp, Bool, k => Cmp.is_eq(k), GT{}, EQ{}, e))
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      e => pcn.cmp_fin(x, y, t1, t2, U32.cmp(x, y), {==}, pcn.str_go_eq(t1, t2), e)

def pcn.str_fin(+a: String, +b: String, c: Cmp, ec: {String.order(a, b) == c : Cmp}, e: {Cmp.is_eq(c) == True{} : Bool}) -> {a == b : String}:
  match c:
    case LT{}:
      LA.pce.absurdF({a == b : String}, e)
    case EQ{}:
      pcn.str_go_eq(a, b)(ec)
    case GT{}:
      LA.pce.absurdF({a == b : String}, e)

# String.eq is equality
def pcn.str_sound(+a: String, +b: String, e: {String.eq(a, b) == True{} : Bool}) -> {a == b : String}:
  pcn.str_fin(a, b, String.order(a, b), {==}, e)

# The keep list and the registry (R2, R6)
# ---------------------------------------

def pcn.listed_step(b: Bool, -r: String, +rest: List<&2, String>, +u: String, ih: {Env.listed(rest, u) == True{} : Bool}) -> {Env.listed.go(r <> rest, u, b) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# a list that holds n lists it
def pcn.listed_name(xs: List<&2, String>, +n: String, +ys: List<&2, String>) -> {Env.listed(List.append(&2, String, xs, n <> ys), n) == True{} : Bool}:
  match xs:
    case Nil{}:
      %Equal.sym(Bool, String.eq(n, n), True{}, pcn.str_refl(n)) : {Env.listed.go(n <> ys, n, _) == True{} : Bool}
      {==}
    case +r <> +t:
      pcn.listed_step(String.eq(r, n), r, List.append(&2, String, t, n <> ys), n, pcn.listed_name(t, n, ys))

def pcn.Split(ns: List<&2, String>, u: String) -> Type:
  &xs: List<&2, String> -> &ys: List<&2, String> -> {ns == List.append(&2, String, xs, u <> ys) : List<&2, String>}

def pcn.split_cons(+r: String, -rest: List<&2, String>, -u: String, s: pcn.Split(rest, u)) -> pcn.Split(r <> rest, u):
  (xs, p) = s
  (ys, e) = p
  (r <> xs, (ys, Equal.cong(List<&2, String>, List<&2, String>, l => r <> l, rest, List.append(&2, String, xs, u <> ys), e)))

def pcn.listed_only_step(b: Bool, +r: String, +rest: List<&2, String>, +u: String, eb: {String.eq(r, u) == b : Bool}, h: {Env.listed.go(r <> rest, u, b) == True{} : Bool}, ih: {Env.listed(rest, u) == True{} : Bool} -> pcn.Split(rest, u)) -> pcn.Split(r <> rest, u):
  match b:
    case True{}:
      +e = pcn.str_sound(r, u, eb)
      (Nil{}, (rest, Equal.cong(String, List<&2, String>, x => x <> rest, r, u, e)))
    case False{}:
      pcn.split_cons(r, rest, u, ih(h))

# a list lists only names it holds
def pcn.listed_only(ns: List<&2, String>, +u: String, h: {Env.listed(ns, u) == True{} : Bool}) -> pcn.Split(ns, u):
  match ns:
    case Nil{}:
      LA.pce.absurdF(pcn.Split(Nil{}, u), h)
    case +r <> +rest:
      pcn.listed_only_step(String.eq(r, u), r, rest, u, {==}, h, x => pcn.listed_only(rest, u, x))

# a name in ASCII upper case is its upper case
def pcn.up_of(n: String, r: String, h: ChildEnv.env_case_eq(n, r)) -> {Env.up(n) == r : String}:
  match n r:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, u}:
      match h:
    case SCon{x, t} SNil{}:
      match h:
    case SCon{+x, +t} SCon{+y, +u}:
      (e1, e2) = h
      %e1 : {SCon{Char.to_upper(x), Env.up(t)} == SCon{_, u} : String}
      %pcn.up_of(t, u, e2) : {SCon{Char.to_upper(x), Env.up(t)} == SCon{Char.to_upper(x), _} : String}
      {==}

# the upper case of a name is the name in ASCII upper case
def pcn.case_up(n: String) -> ChildEnv.env_case_eq(n, Env.up(n)):
  match n:
    case SNil{}:
      Unit{}
    case SCon{x, t}:
      ({==}, pcn.case_up(t))

def pcn.case_of(+n: String, -r: String, e: {Env.up(n) == r : String}) -> ChildEnv.env_case_eq(n, r):
  %e : ChildEnv.env_case_eq(n, _)
  pcn.case_up(n)

# Secret patterns (R6)
# --------------------

# p starts p, then anything
def pcn.sw_self(p: String, +c: String) -> {String.starts_with.go(p, String.append(p, c)) == True{} : Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{x, pt}:
      %Equal.sym(Bool, Char.is_eq(x, x), True{}, pcn.char_refl(x)) : {String.starts_with.go.if(pt, String.append(pt, c), _) == True{} : Bool}
      pcn.sw_self(pt, c)

def pcn.contains_if(b: Bool, -s: String, -p: String, ih: {String.contains(s, p) == True{} : Bool}) -> {String.contains.if(s, p, b) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# p, then anything, holds p
def pcn.contains_start(p: String, +c: String) -> {String.contains(String.append(p, c), p) == True{} : Bool}:
  match p:
    case SNil{}:
      match c:
        case SNil{}:
          {==}
        case SCon{h, t}:
          {==}
    case SCon{+x, +pt}:
      %Equal.sym(Bool, String.starts_with.go(SCon{x, pt}, String.append(SCon{x, pt}, c)), True{}, pcn.sw_self(SCon{x, pt}, c)) : {String.contains.if(String.append(pt, c), SCon{x, pt}, _) == True{} : Bool}
      {==}

# any text, then p, then any text, holds p
def pcn.contains_mid(a: String, +p: String, +c: String) -> {String.contains(String.append(a, String.append(p, c)), p) == True{} : Bool}:
  match a:
    case SNil{}:
      pcn.contains_start(p, c)
    case SCon{+h, +t}:
      pcn.contains_if(String.starts_with(SCon{h, String.append(t, String.append(p, c))}, p), String.append(t, String.append(p, c)), p, pcn.contains_mid(t, p, c))

def pcn.matched_step(b: Bool, -q: String, +rest: List<&2, String>, +u: String, ih: {Env.matched(rest, u) == True{} : Bool}) -> {Env.matched.go(q <> rest, u, b) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# a text that holds the i-th pattern of ps matches ps
def pcn.matched_hit(ps: List<&2, String>, i: Nat, +p: String, +u: String, hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}, hc: {String.contains(u, p) == True{} : Bool}) -> {Env.matched(ps, u) == True{} : Bool}:
  match ps i:
    case Nil{} _:
      pcn.none_some({Env.matched(Nil{}, u) == True{} : Bool}, p, hp)
    case +q <> +rest 0n:
      +e = pcn.some_eq(q, p, hp)
      +hq = Equal.trans(Bool, String.contains(u, q), String.contains(u, p), True{}, Equal.cong(String, Bool, x => String.contains(u, x), q, p, e), hc)
      %Equal.sym(Bool, String.contains(u, q), True{}, hq) : {Env.matched.go(q <> rest, u, _) == True{} : Bool}
      {==}
    case +q <> +rest 1n+k:
      pcn.matched_step(String.contains(u, q), q, rest, u, pcn.matched_hit(rest, k, p, u, hp, hc))

def pcn.Hit(ps: List<&2, String>, u: String) -> Type:
  &i: Nat -> &p: String -> ({List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>} & {String.contains(u, p) == True{} : Bool})

def pcn.hit_cons(-q: String, -rest: List<&2, String>, -u: String, s: pcn.Hit(rest, u)) -> pcn.Hit(q <> rest, u):
  (i, r1) = s
  (p, r2) = r1
  (1n+i, (p, r2))

def pcn.matched_sound_step(b: Bool, +q: String, +rest: List<&2, String>, +u: String, eb: {String.contains(u, q) == b : Bool}, h: {Env.matched.go(q <> rest, u, b) == True{} : Bool}, ih: {Env.matched(rest, u) == True{} : Bool} -> pcn.Hit(rest, u)) -> pcn.Hit(q <> rest, u):
  match b:
    case True{}:
      (0n, (q, ({==}, eb)))
    case False{}:
      pcn.hit_cons(q, rest, u, ih(h))

# a text that matches ps holds one of its patterns
def pcn.matched_sound(ps: List<&2, String>, +u: String, h: {Env.matched(ps, u) == True{} : Bool}) -> pcn.Hit(ps, u):
  match ps:
    case Nil{}:
      LA.pce.absurdF(pcn.Hit(Nil{}, u), h)
    case +q <> +rest:
      pcn.matched_sound_step(String.contains(u, q), q, rest, u, {==}, h, x => pcn.matched_sound(rest, u, x))

def pcn.Starts(p: String, s: String) -> Type:
  &c: String -> {s == String.append(p, c) : String}

def pcn.cons_eq(+x: Char, -y: Char, -xt: String, -w: String, ey: {x == y : Char}, e: {xt == w : String}) -> {SCon{x, xt} == SCon{y, w} : String}:
  %ey : {SCon{x, xt} == SCon{_, w} : String}
  %e : {SCon{x, xt} == SCon{x, _} : String}
  {==}

def pcn.starts_cons(+x: Char, -y: Char, -yt: String, -xt: String, ey: {x == y : Char}, s: pcn.Starts(yt, xt)) -> pcn.Starts(SCon{y, yt}, SCon{x, xt}):
  (c, e) = s
  (c, pcn.cons_eq(x, y, xt, String.append(yt, c), ey, e))

def pcn.sw_sound_step(b: Bool, +y: Char, +yt: String, +x: Char, +xt: String, eb: {Char.is_eq(x, y) == b : Bool}, h: {String.starts_with.go.if(yt, xt, b) == True{} : Bool}, ih: {String.starts_with.go(yt, xt) == True{} : Bool} -> pcn.Starts(yt, xt)) -> pcn.Starts(SCon{y, yt}, SCon{x, xt}):
  match b:
    case True{}:
      pcn.starts_cons(x, y, yt, xt, pcn.char_sound(x, y, eb), ih(h))
    case False{}:
      LA.pce.absurdF(pcn.Starts(SCon{y, yt}, SCon{x, xt}), h)

# a text that starts with p is p, then a text
def pcn.sw_sound(p: String, +s: String, h: {String.starts_with.go(p, s) == True{} : Bool}) -> pcn.Starts(p, s):
  match p:
    case SNil{}:
      (s, {==})
    case SCon{+y, +yt}:
      match s:
        case SNil{}:
          LA.pce.absurdF(pcn.Starts(SCon{y, yt}, SNil{}), h)
        case SCon{+x, +xt}:
          pcn.sw_sound_step(Char.is_eq(x, y), y, yt, x, xt, {==}, h, z => pcn.sw_sound(yt, xt, z))

def pcn.Mid(p: String, s: String) -> Type:
  &a: String -> &c: String -> {s == String.append(a, String.append(p, c)) : String}

def pcn.mid_start(-p: String, -s: String, st: pcn.Starts(p, s)) -> pcn.Mid(p, s):
  (c, e) = st
  (SNil{}, (c, e))

def pcn.mid_cons(+x: Char, -t: String, -p: String, s: pcn.Mid(p, t)) -> pcn.Mid(p, SCon{x, t}):
  (a, r) = s
  (c, e) = r
  (SCon{x, a}, (c, Equal.cong(String, String, z => SCon{x, z}, t, String.append(a, String.append(p, c)), e)))

def pcn.contains_sound_step(b: Bool, +x: Char, +t: String, +p: String, eb: {String.starts_with(SCon{x, t}, p) == b : Bool}, h: {String.contains.if(t, p, b) == True{} : Bool}, ih: {String.contains(t, p) == True{} : Bool} -> pcn.Mid(p, t)) -> pcn.Mid(p, SCon{x, t}):
  match b:
    case True{}:
      pcn.mid_start(p, SCon{x, t}, pcn.sw_sound(p, SCon{x, t}, eb))
    case False{}:
      pcn.mid_cons(x, t, p, ih(h))

# a text that holds p is a text, then p, then a text
def pcn.contains_sound(s: String, +p: String, h: {String.contains(s, p) == True{} : Bool}) -> pcn.Mid(p, s):
  match s:
    case SNil{}:
      match p:
        case SNil{}:
          (SNil{}, (SNil{}, {==}))
        case SCon{y, yt}:
          LA.pce.absurdF(pcn.Mid(SCon{y, yt}, SNil{}), h)
    case SCon{+x, +t}:
      pcn.contains_sound_step(String.starts_with(SCon{x, t}, p), x, t, p, {==}, h, z => pcn.contains_sound(t, p, z))

# The order of the child (R4)
# ---------------------------

# the filter's own mask: each variable's pass test
def pcn.mask(+reg: List<&2, String>, +ks: List<&2, String>, xs: List<&2, Env.Var>) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      Nil{}
    case +v <> rest:
      Env.passes(reg, ks, Env.Var.name(v)) <> pcn.mask(reg, ks, rest)

def pcn.put_eq(b: Bool, v: Env.Var, r: List<&2, Env.Var>) -> {ChildEnv.env_pick.put(b, v, r) == Env.keep.put(b, v, r) : List<&2, Env.Var>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the mask picks the filter's list
def pcn.pick_keep(+reg: List<&2, String>, +ks: List<&2, String>, xs: List<&2, Env.Var>) -> {ChildEnv.env_pick(pcn.mask(reg, ks, xs), xs) == Env.keep(reg, ks, xs) : List<&2, Env.Var>}:
  match xs:
    case Nil{}:
      {==}
    case +v <> +rest:
      +b = Env.passes(reg, ks, Env.Var.name(v))
      Equal.trans(List<&2, Env.Var>, ChildEnv.env_pick.put(b, v, ChildEnv.env_pick(pcn.mask(reg, ks, rest), rest)), ChildEnv.env_pick.put(b, v, Env.keep(reg, ks, rest)), Env.keep.put(b, v, Env.keep(reg, ks, rest)), Equal.cong(List<&2, Env.Var>, List<&2, Env.Var>, r => ChildEnv.env_pick.put(b, v, r), ChildEnv.env_pick(pcn.mask(reg, ks, rest), rest), Env.keep(reg, ks, rest), pcn.pick_keep(reg, ks, rest)), pcn.put_eq(b, v, Env.keep(reg, ks, rest)))
