# eukhe: lemmas shared by the proofs of area model_name: logic and chars,
# the prefix strip (mnb.strip_app: a spelled prefix strips off; mnb.sp: a
# stripped prefix was there), the parts of a name (mnb.part_*), the lists
# of strings a rule tries (mnb.*_in: one hit of the list makes the list
# hit; mnb.*_sp: a hit of the list is a hit of one string of it).

import Base
import ../../bend/text_pat.bend as Tp
import ../../bend/phrase.bend as P
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ../wire/wire_bool_exact.bend as PWireBoolExact

# Logic
# -----

def mnb.BT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

def mnb.BF(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# True is not False
def mnb.absurd(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : mnb.BT(_, G)
  Unit{}

def mnb.absurd_f(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : mnb.BF(_, G)
  Unit{}

# a value that is True and False
def mnb.clash(-G: Type, -x: Bool, et: {x == True{} : Bool}, ef: {x == False{} : Bool}) -> G:
  mnb.absurd(G, Equal.trans(Bool, True{}, x, False{}, Equal.sym(Bool, x, True{}, et), ef))

# a lazy `or` whose right side is True is True
def mnb.or_rl(y: Bool, -z: Bool, ez: {z == True{} : Bool}) -> {P.pm.or(y, u => z) == True{} : Bool}:
  match y:
    case True{}:
      {==}
    case False{}:
      ez

def mnb.or_lazy(a: Bool, b: Bool) -> {P.pm.or(a, u => b) == Bool.or(a, b) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def mnb.and_lazy(a: Bool, b: Bool) -> {P.pm.and(a, u => b) == Bool.and(a, b) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def mnb.ite_lazy(a: Bool, b: Bool, c: Bool) -> {M.ite(a, u => b, v => c) == Bool.or(Bool.and(a, b), Bool.and(Bool.not(a), c)) : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

def mnb.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      mnb.absurd_f({False{} == True{} : Bool}, h)

def mnb.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      mnb.absurd_f({b == True{} : Bool}, h)

def mnb.and_t(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      mnb.absurd_f({Bool.and(False{}, b) == True{} : Bool}, ea)

def mnb.not_t(a: Bool, h: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      mnb.absurd_f({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def mnb.not_f(a: Bool, h: {a == False{} : Bool}) -> {Bool.not(a) == True{} : Bool}:
  match a:
    case True{}:
      mnb.absurd({Bool.not(True{}) == True{} : Bool}, h)
    case False{}:
      {==}

def mnb.or_fl(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      mnb.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def mnb.or_fr(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      mnb.absurd({b == False{} : Bool}, h)
    case False{}:
      h

def mnb.or_rt(a: Bool, -b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def mnb.or_false(y: Bool) -> {Bool.or(y, False{}) == y : Bool}:
  match y:
    case True{}:
      {==}
    case False{}:
      {==}

def mnb.and_false(d: Bool) -> {Bool.and(d, False{}) == False{} : Bool}:
  match d:
    case True{}:
      {==}
    case False{}:
      {==}

def mnb.and_true(d: Bool) -> {Bool.and(d, True{}) == d : Bool}:
  match d:
    case True{}:
      {==}
    case False{}:
      {==}

# a lazy `or` of two parts, each equal to a spec part, is the spec's `or`
def mnb.or2(+a: Bool, +b: Bool, +c: Bool, +d: Bool, e1: {a == c : Bool}, e2: {b == d : Bool}) -> {P.pm.or(a, u => b) == Bool.or(c, d) : Bool}:
  %Equal.sym(Bool, a, c, e1) : {P.pm.or(_, u => b) == Bool.or(c, d) : Bool}
  %Equal.sym(Bool, b, d, e2) : {P.pm.or(c, u => _) == Bool.or(c, d) : Bool}
  mnb.or_lazy(c, d)

def mnb.and2(+a: Bool, +b: Bool, +d: Bool, e2: {b == d : Bool}) -> {P.pm.and(a, u => b) == Bool.and(a, d) : Bool}:
  %Equal.sym(Bool, b, d, e2) : {P.pm.and(a, u => _) == Bool.and(a, d) : Bool}
  mnb.and_lazy(a, d)

# a lazy `and` of two True parts is True
def mnb.and_lt(n: Bool, -l: Bool, en: {n == True{} : Bool}, el: {l == True{} : Bool}) -> {P.pm.and(n, v => l) == True{} : Bool}:
  match n:
    case True{}:
      el
    case False{}:
      mnb.absurd_f({P.pm.and(False{}, v => l) == True{} : Bool}, en)

# Chars
# -----

def mnb.bool_cmp_refl(b: Bool) -> {Bool.cmp(b, b) == EQ{} : Cmp}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def mnb.word_cmp_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, mnb.word_cmp_refl(p, t)) : {Word.cmp.fin(b, b, _) == EQ{} : Cmp}
          mnb.bool_cmp_refl(b)

def mnb.u32_refl(x: U32) -> {U32.is_eq(x, x) == True{} : Bool}:
  match x:
    case U32{+w}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, mnb.word_cmp_refl(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# a char is the char it is
def mnb.char_refl(c: Char) -> {Char.is_eq(c, c) == True{} : Bool}:
  match c:
    case Chr{x}:
      mnb.u32_refl(x)

# Char.is_eq is equality
def mnb.char_sound(+c: Char, +d: Char, e: {Char.is_eq(c, d) == True{} : Bool}) -> {c == d : Char}:
  match c d:
    case Chr{+x} Chr{+y}:
      Equal.cong(U32, Char, u => Chr{u}, x, y, PWireBoolExact.wr_eq_sound(x, y, e))

# Texts
# -----

def mnb.app_nil(s: String) -> {String.append(s, SNil{}) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      Equal.cong(String, String, z => SCon{x, z}, String.append(t, SNil{}), t, mnb.app_nil(t))

def mnb.app_assoc(a: String, -b: String, -c: String) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      Equal.cong(String, String, z => SCon{x, z}, String.append(String.append(t, b), c), String.append(t, String.append(b, c)), mnb.app_assoc(t, b, c))

def mnb.cons_eq(+x: Char, -a: String, -b: String, e: {a == b : String}) -> {SCon{x, a} == SCon{x, b} : String}:
  Equal.cong(String, String, z => SCon{x, z}, a, b, e)

def mnb.lcons_eq(+q: String, -a: List<&2, String>, -b: List<&2, String>, e: {a == b : List<&2, String>}) -> {q <> a == q <> b : List<&2, String>}:
  Equal.cong(List<&2, String>, List<&2, String>, z => q <> z, a, b, e)

# Strip
# -----

# a spelled prefix strips off
def mnb.strip_app(p: String, -r: String) -> {M.strip(p, String.append(p, r)) == Some{r} : Maybe<&2, String>}:
  match p:
    case SNil{}:
      {==}
    case SCon{+c, pt}:
      %Equal.sym(Bool, Char.is_eq(c, c), True{}, mnb.char_refl(c)) : {M.strip.go(_, u => M.strip(pt, String.append(pt, r))) == Some{r} : Maybe<&2, String>}
      mnb.strip_app(pt, r)

def mnb.got_app(+p: String, -r: String) -> {M.got(M.strip(p, String.append(p, r))) == True{} : Bool}:
  %Equal.sym(Maybe<&2, String>, M.strip(p, String.append(p, r)), Some{r}, mnb.strip_app(p, r)) : {M.got(_) == True{} : Bool}
  {==}

# what strip answers says of s
def mnb.SP(p: String, s: String, m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{r}:
      {s == String.append(p, r) : String}

def mnb.sp_con(+c: Char, -pt: String, +x: Char, -st: String, e: {c == x : Char}, m: Maybe<&2, String>, ih: mnb.SP(pt, st, m)) -> mnb.SP(SCon{c, pt}, SCon{x, st}, m):
  match m:
    case None{}:
      Unit{}
    case Some{+r}:
      %Equal.sym(Char, c, x, e) : {SCon{x, st} == SCon{_, String.append(pt, r)} : String}
      mnb.cons_eq(x, st, String.append(pt, r), ih)

def mnb.sp_go(+c: Char, +pt: String, +x: Char, +st: String, b: Bool, eb: {Char.is_eq(c, x) == b : Bool}, ih: mnb.SP(pt, st, M.strip(pt, st))) -> mnb.SP(SCon{c, pt}, SCon{x, st}, M.strip.go(b, u => M.strip(pt, st))):
  match b:
    case True{}:
      mnb.sp_con(c, pt, x, st, mnb.char_sound(c, x, eb), M.strip(pt, st), ih)
    case False{}:
      Unit{}

# a stripped prefix was there
def mnb.sp(p: String, +s: String) -> mnb.SP(p, s, M.strip(p, s)):
  match p:
    case SNil{}:
      {==}
    case SCon{+c, +pt}:
      match s:
        case SNil{}:
          Unit{}
        case SCon{+x, +st}:
          mnb.sp_go(c, pt, x, st, Char.is_eq(c, x), {==}, mnb.sp(pt, st))

def mnb.strip_eq(p: String, +s: String, -r: String, h: {M.strip(p, s) == Some{r} : Maybe<&2, String>}) -> {s == String.append(p, r) : String}:
  %h : mnb.SP(p, s, _)
  mnb.sp(p, s)

# R1: parts
# ---------

def mnb.PartP(p: String, s: String, b: Bool) -> Type:
  match b:
    case True{}:
      Sigma<&1, &1, String, a => Sigma<&1, &1, String, c => {s == String.append(a, String.append(p, c)) : String}>>
    case False{}:
      Unit

# a stripped p at s: a part of s at its start
def mnb.part_at(+p: String, +s: String, m: Maybe<&2, String>, v: mnb.SP(p, s, m)) -> mnb.PartP(p, s, M.got(m)):
  match m:
    case None{}:
      Unit{}
    case Some{+r}:
      (SNil{}, (r, v))

def mnb.part_next(+x: Char, -t: String, -p: String, b: Bool, v: mnb.PartP(p, t, b)) -> mnb.PartP(p, SCon{x, t}, b):
  match b:
    case True{}:
      (+a, (+c, e)) = v
      (SCon{x, a}, (c, mnb.cons_eq(x, t, String.append(a, String.append(p, c)), e)))
    case False{}:
      Unit{}

def mnb.part_or(+x: Char, -t: String, -p: String, b1: Bool, v1: mnb.PartP(p, SCon{x, t}, b1), b2: Bool, v2: mnb.PartP(p, t, b2)) -> mnb.PartP(p, SCon{x, t}, P.pm.or(b1, u => b2)):
  match b1:
    case True{}:
      v1
    case False{}:
      mnb.part_next(x, t, p, b2, v2)

# a part found is a part of s
def mnb.part_sp(+p: String, s: String) -> mnb.PartP(p, s, M.part(p, s)):
  match s:
    case SNil{}:
      mnb.part_at(p, SNil{}, M.strip(p, SNil{}), mnb.sp(p, SNil{}))
    case SCon{+x, +t}:
      mnb.part_or(x, t, p, M.got(M.strip(p, SCon{x, t})), mnb.part_at(p, SCon{x, t}, M.strip(p, SCon{x, t}), mnb.sp(p, SCon{x, t})), M.part(p, t), mnb.part_sp(p, t))

def mnb.part_here(+p: String, s: String, h: {M.got(M.strip(p, s)) == True{} : Bool}) -> {M.part(p, s) == True{} : Bool}:
  match s:
    case SNil{}:
      h
    case SCon{+x, +t}:
      %Equal.sym(Bool, M.got(M.strip(p, SCon{x, t})), True{}, h) : {P.pm.or(_, u => M.part(p, t)) == True{} : Bool}
      {==}

# a part anywhere is found
def mnb.part_app(a: String, +p: String, +b: String) -> {M.part(p, String.append(a, String.append(p, b))) == True{} : Bool}:
  match a:
    case SNil{}:
      mnb.part_here(p, String.append(p, b), mnb.got_app(p, b))
    case SCon{+x, +t}:
      mnb.or_rl(M.got(M.strip(p, SCon{x, String.append(t, String.append(p, b))})), M.part(p, String.append(t, String.append(p, b))), mnb.part_app(t, p, b))

def mnb.PartsP(ps: List<&2, String>, s: String, b: Bool) -> Type:
  match b:
    case True{}:
      Sigma<&1, &1, List<&2, String>, pre => Sigma<&1, &1, String, p => Sigma<&1, &1, List<&2, String>, post => Sigma<&1, &1, String, a => Sigma<&1, &1, String, c => {ps == List.append(&2, String, pre, p <> post) : List<&2, String>} & {s == String.append(a, String.append(p, c)) : String}>>>>>
    case False{}:
      Unit

def mnb.parts_or(+q: String, +more: List<&2, String>, -s: String, b1: Bool, v1: mnb.PartP(q, s, b1), b2: Bool, v2: mnb.PartsP(more, s, b2)) -> mnb.PartsP(q <> more, s, P.pm.or(b1, u => b2)):
  match b1:
    case True{}:
      (+a, (+c, e)) = v1
      (Nil{}, (q, (more, (a, (c, ({==}, e))))))
    case False{}:
      match b2:
        case True{}:
          (+pre, (+p, (+post, (+a, (+c, (e1, e2)))))) = v2
          (q <> pre, (p, (post, (a, (c, (mnb.lcons_eq(q, more, List.append(&2, String, pre, p <> post), e1), e2))))))
        case False{}:
          Unit{}

# a list of parts found: one of them is a part of s
def mnb.parts_sp(ps: List<&2, String>, +s: String) -> mnb.PartsP(ps, s, M.parts(ps, s)):
  match ps:
    case Nil{}:
      Unit{}
    case +q <> +more:
      mnb.parts_or(q, more, s, M.part(q, s), mnb.part_sp(q, s), M.parts(more, s), mnb.parts_sp(more, s))

# one part of the list found: the list is found
def mnb.parts_in(pre: List<&2, String>, +p: String, +post: List<&2, String>, +s: String, h: {M.part(p, s) == True{} : Bool}) -> {M.parts(List.append(&2, String, pre, p <> post), s) == True{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, M.part(p, s), True{}, h) : {P.pm.or(_, u => M.parts(post, s)) == True{} : Bool}
      {==}
    case +q <> more:
      mnb.or_rl(M.part(q, s), M.parts(List.append(&2, String, more, p <> post), s), mnb.parts_in(more, p, post, s, h))
