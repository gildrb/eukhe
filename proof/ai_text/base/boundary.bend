# eukhe: lemmas of the R4 proofs (event_boundary): no boundary at a place
# exactly when the code's length there is 0 (aitb.zero_bnd); two breaks
# read whole have the code's length of the two (aitb.eq); a length the
# code finds is two breaks read whole (aitb.bnd_sound); the walk answers
# the first place with a length (aitb.first, aitb.none, aitb.sound).

import Base
import ../../../bend/ai_text.bend as T
import ../../../laws/ai_text.bend as AiText
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../../model_name/base.bend as LA
import ./dig.bend as LD

# Nat
# ---

def aitb.zero(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+k:
      False{}

def aitb.NZ(n: Nat, G: Type) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+k:
      G

# 0 is no successor
def aitb.zs(-G: Type, -j: Nat, e: {0n == 1n+j : Nat}) -> G:
  %e : aitb.NZ(_, G)
  Unit{}

def aitb.zero_t(n: Nat, h: {aitb.zero(n) == True{} : Bool}) -> {n == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      LA.mnb.absurd_f({1n+k == 0n : Nat}, h)

def aitb.zero_n(+n: Nat, -G: Type, e: {0n == n : Nat}, nz: {aitb.zero(n) == False{} : Bool}) -> G:
  LA.mnb.absurd(G, Equal.trans(Bool, True{}, aitb.zero(n), False{}, Equal.cong(Nat, Bool, z => aitb.zero(z), 0n, n, e), nz))

# Span
# ----

def aitb.st(m: Maybe<&2, T.Span>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{p}:
      match p:
        case T.Span{i, l}:
          i

def aitb.ln(m: Maybe<&2, T.Span>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{p}:
      match p:
        case T.Span{i, l}:
          l

def aitb.SI(m: Maybe<&2, T.Span>, i: Nat, l: Nat) -> Type:
  Sigma<&1, &1, Nat, k => {m == Some{T.Span{k, l}} : Maybe<&2, T.Span>} & {1n+k == i : Nat}>

# a shifted answer is an answer one char later
def aitb.shift_inv(m: Maybe<&2, T.Span>, +i: Nat, +l: Nat, h: {T.shift(m) == Some{T.Span{i, l}} : Maybe<&2, T.Span>}) -> aitb.SI(m, i, l):
  match m:
    case None{}:
      LD.aitd.none_some(T.Span, T.Span{i, l}, aitb.SI(None{}, i, l), h)
    case Some{p}:
      match p:
        case T.Span{+i0, +l0}:
          +hh = h
          (i0, (Equal.cong(Nat, Maybe<&2, T.Span>, z => Some{T.Span{i0, z}}, l0, l, Equal.cong(Maybe<&2, T.Span>, Nat, z => aitb.ln(z), Some{T.Span{1n+i0, l0}}, Some{T.Span{i, l}}, hh)), Equal.cong(Maybe<&2, T.Span>, Nat, z => aitb.st(z), Some{T.Span{1n+i0, l0}}, Some{T.Span{i, l}}, hh)))

# No boundary here, length 0
# --------------------------

def aitb.z6(b: Bool, k: Nat) -> {aitb.zero(T.bnd.second(1n+k, T.brk.lf(b))) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def aitb.z5(v: String, k: Nat) -> {aitb.zero(T.bnd.second(1n+k, T.brk.cr(v))) == False{} : Bool}:
  match v:
    case SNil{}:
      {==}
    case SCon{y, u}:
      aitb.z6(T.is_lf(y), k)

def aitb.z4(cr: Bool, lf: Bool, v: String, k: Nat) -> {aitb.zero(T.bnd.second(1n+k, T.brk.at(cr, lf, v))) == Bool.not(Bool.or(cr, lf)) : Bool}:
  match cr:
    case True{}:
      aitb.z5(v, k)
    case False{}:
      match lf:
        case True{}:
          {==}
        case False{}:
          {==}

def aitb.z3(w: String, k: Nat) -> {aitb.zero(T.bnd.second(1n+k, T.brk(w))) == Bool.not(AiText.sp_opens(w)) : Bool}:
  match w:
    case SNil{}:
      {==}
    case SCon{z, v}:
      match z:
        case Chr{+zc}:
          aitb.z4(U32.is_eq(zc, 13), U32.is_eq(zc, 10), v, k)

def aitb.z2(b: Bool, +yc: U32, +w: String) -> {aitb.zero(T.bnd.cr.at(b, SCon{Chr{yc}, w}, w)) == Bool.not(AiText.sp_bnd_on(AiText.sp_after.lf(b, Chr{yc}, w))) : Bool}:
  match b:
    case True{}:
      aitb.z3(w, 1n)
    case False{}:
      aitb.z3(SCon{Chr{yc}, w}, 0n)

def aitb.z1(cr: Bool, lf: Bool, t: String) -> {aitb.zero(T.bnd.at(cr, lf, t)) == Bool.not(AiText.sp_bnd_on(AiText.sp_after.at(cr, lf, t))) : Bool}:
  match cr:
    case True{}:
      match t:
        case SNil{}:
          {==}
        case SCon{y, +w}:
          match y:
            case Chr{+yc}:
              aitb.z2(U32.is_eq(yc, 10), yc, w)
    case False{}:
      match lf:
        case True{}:
          aitb.z3(t, 0n)
        case False{}:
          {==}

# the code's length at u is 0 exactly when no boundary starts at u
def aitb.zero_bnd(u: String) -> {aitb.zero(T.bnd(u)) == Bool.not(AiText.sp_bnd_at(u)) : Bool}:
  match u:
    case SNil{}:
      {==}
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          aitb.z1(U32.is_eq(xc, 13), U32.is_eq(xc, 10), t)

# no boundary starts at u: the code's length there is 0
def aitb.no_bnd(+u: String, h: {Bool.not(AiText.sp_bnd_at(u)) == True{} : Bool}) -> {T.bnd(u) == 0n : Nat}:
  aitb.zero_t(T.bnd(u), Equal.trans(Bool, aitb.zero(T.bnd(u)), Bool.not(AiText.sp_bnd_at(u)), True{}, aitb.zero_bnd(u), h))

# Two breaks read whole: their length
# -----------------------------------

def aitb.lf_one(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {T.brk.lf(b) == 1n : Nat}:
  match b:
    case True{}:
      LA.mnb.absurd_f({T.brk.lf(True{}) == 1n : Nat}, h)
    case False{}:
      {==}

# after a `\r`, no `\n`: the break is `\r` alone
def aitb.brk_cr_one(r: String, h: {AiText.sp_no_lf(r) == True{} : Bool}) -> {T.brk.cr(r) == 1n : Nat}:
  match r:
    case SNil{}:
      {==}
    case SCon{y, w}:
      match y:
        case Chr{+yc}:
          aitb.lf_one(U32.is_eq(yc, 10), h)

# two breaks read whole, at the start of a text: the code's length is the
# length of the two
def aitb.eq(j1: Nat, j2: Nat, +r: String, hw1: {AiText.sp_whole(j1, String.append(AiText.sp_brk(j2), r)) == True{} : Bool}, hw2: {AiText.sp_whole(j2, r) == True{} : Bool}) -> {T.bnd(String.append(AiText.sp_brk(j1), String.append(AiText.sp_brk(j2), r))) == AiText.sp_span_len(j1, j2) : Nat}:
  match j1:
    case 0n:
      match j2:
        case 0n:
          {==}
        case 1n:
          Equal.cong(Nat, Nat, z => T.bnd.second(2n, z), T.brk.cr(r), 1n, aitb.brk_cr_one(r, hw2))
        case 2n+k:
          {==}
    case 1n:
      match j2:
        case 0n:
          {==}
        case 1n:
          Equal.cong(Nat, Nat, z => T.bnd.second(1n, z), T.brk.cr(r), 1n, aitb.brk_cr_one(r, hw2))
        case 2n+k:
          LA.mnb.absurd_f({T.bnd(String.append("\r", String.append("\n", r))) == AiText.sp_span_len(1n, 2n+k) : Nat}, hw1)
    case 2n+i:
      match j2:
        case 0n:
          {==}
        case 1n:
          Equal.cong(Nat, Nat, z => T.bnd.second(1n, z), T.brk.cr(r), 1n, aitb.brk_cr_one(r, hw2))
        case 2n+k:
          {==}

# the length of two breaks is not 0
def aitb.span_nz(j1: Nat, -j2: Nat) -> {aitb.zero(AiText.sp_span_len(j1, j2)) == False{} : Bool}:
  match j1:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+k:
      {==}

# A length is two breaks read whole
# ---------------------------------

def aitb.KS(w: String, n: Nat) -> Type:
  Sigma<&1, &1, Nat, j => Sigma<&1, &1, String, r => {w == String.append(AiText.sp_brk(j), r) : String} & ({AiText.sp_whole(j, r) == True{} : Bool} & {String.length(AiText.sp_brk(j)) == n : Nat})>>

def aitb.brk_cr_s(b: Bool, +xc: U32, +yc: U32, +u: String, -k: Nat, ex: {SCon{Chr{xc}, SCon{Chr{yc}, u}} == SCon{Chr{13}, SCon{Chr{yc}, u}} : String}, eb: {U32.is_eq(yc, 10) == b : Bool}, e: {T.brk.lf(b) == 1n+k : Nat}) -> aitb.KS(SCon{Chr{xc}, SCon{Chr{yc}, u}}, 1n+k):
  match b:
    case True{}:
      (0n, (u, (Equal.trans(String, SCon{Chr{xc}, SCon{Chr{yc}, u}}, SCon{Chr{13}, SCon{Chr{yc}, u}}, SCon{Chr{13}, SCon{Chr{10}, u}}, ex, Equal.cong(U32, String, v => SCon{Chr{13}, SCon{Chr{v}, u}}, yc, 10, PWireBoolExact.wr_eq_sound(yc, 10, eb))), ({==}, e))))
    case False{}:
      (1n, (SCon{Chr{yc}, u}, (ex, (LA.mnb.not_f(U32.is_eq(yc, 10), eb), e))))

def aitb.brk_at_s(cr: Bool, lf: Bool, +xc: U32, +t: String, -k: Nat, ecr: {U32.is_eq(xc, 13) == cr : Bool}, elf: {U32.is_eq(xc, 10) == lf : Bool}, e: {T.brk.at(cr, lf, t) == 1n+k : Nat}) -> aitb.KS(SCon{Chr{xc}, t}, 1n+k):
  match cr:
    case True{}:
      match t:
        case SNil{}:
          (1n, (SNil{}, (Equal.cong(U32, String, v => SCon{Chr{v}, SNil{}}, xc, 13, PWireBoolExact.wr_eq_sound(xc, 13, ecr)), ({==}, e))))
        case SCon{y, +u}:
          match y:
            case Chr{+yc}:
              aitb.brk_cr_s(U32.is_eq(yc, 10), xc, yc, u, k, Equal.cong(U32, String, v => SCon{Chr{v}, SCon{Chr{yc}, u}}, xc, 13, PWireBoolExact.wr_eq_sound(xc, 13, ecr)), {==}, e)
    case False{}:
      match lf:
        case True{}:
          (2n, (t, (Equal.cong(U32, String, v => SCon{Chr{v}, t}, xc, 10, PWireBoolExact.wr_eq_sound(xc, 10, elf)), ({==}, e))))
        case False{}:
          aitb.zs(aitb.KS(SCon{Chr{xc}, t}, 1n+k), k, e)

# a break the code finds at the start of w, read whole, and its length
def aitb.brk_sound(w: String, -k: Nat, e: {T.brk(w) == 1n+k : Nat}) -> aitb.KS(w, 1n+k):
  match w:
    case SNil{}:
      aitb.zs(aitb.KS(SNil{}, 1n+k), k, e)
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          aitb.brk_at_s(U32.is_eq(xc, 13), U32.is_eq(xc, 10), xc, t, k, {==}, {==}, e)

def aitb.SV(k0: Nat, n: Nat, j: Nat) -> Type:
  Sigma<&1, &1, Nat, k => {n == 1n+k : Nat} & {Nat.add(1n+k0, 1n+k) == 1n+j : Nat}>

def aitb.second_inv(-k0: Nat, n: Nat, -j: Nat, e: {T.bnd.second(1n+k0, n) == 1n+j : Nat}) -> aitb.SV(k0, n, j):
  match n:
    case 0n:
      aitb.zs(aitb.SV(k0, 0n, j), j, e)
    case 1n+k:
      (k, ({==}, e))

def aitb.BS(u: String, n: Nat) -> Type:
  Sigma<&1, &1, Nat, j1 => Sigma<&1, &1, Nat, j2 => Sigma<&1, &1, String, r => {u == String.append(AiText.sp_brk(j1), String.append(AiText.sp_brk(j2), r)) : String} & ({AiText.sp_whole(j1, String.append(AiText.sp_brk(j2), r)) == True{} : Bool} & ({AiText.sp_whole(j2, r) == True{} : Bool} & {AiText.sp_span_len(j1, j2) == n : Nat}))>>>

# the first break is `\r\n`
def aitb.fin_crlf(-xc: U32, -yc: U32, +w: String, -j: Nat, -k: Nat, ex: {SCon{Chr{xc}, SCon{Chr{yc}, w}} == SCon{Chr{13}, SCon{Chr{10}, w}} : String}, es: {Nat.add(2n, 1n+k) == 1n+j : Nat}, ks: aitb.KS(w, 1n+k)) -> aitb.BS(SCon{Chr{xc}, SCon{Chr{yc}, w}}, 1n+j):
  (+j2, (+r, (ew, (w2, el)))) = ks
  +y = String.append(AiText.sp_brk(j2), r)
  (0n, (j2, (r, (Equal.trans(String, SCon{Chr{xc}, SCon{Chr{yc}, w}}, SCon{Chr{13}, SCon{Chr{10}, w}}, SCon{Chr{13}, SCon{Chr{10}, y}}, ex, Equal.cong(String, String, z => SCon{Chr{13}, SCon{Chr{10}, z}}, w, y, ew)), ({==}, (w2, Equal.trans(Nat, Nat.add(2n, String.length(AiText.sp_brk(j2))), Nat.add(2n, 1n+k), 1n+j, Equal.cong(Nat, Nat, z => Nat.add(2n, z), String.length(AiText.sp_brk(j2)), 1n+k, el), es)))))))

# the first break is one char c (13 `\r` or 10 `\n`), kind j1
def aitb.fin_one(+j1: Nat, -xc: U32, +c: U32, +w: String, -j: Nat, -k: Nat, ex: {SCon{Chr{xc}, w} == SCon{Chr{c}, w} : String}, eh: {String.append(AiText.sp_brk(j1), w) == SCon{Chr{c}, w} : String}, ew1: @y: String -> {w == y : String} -> {AiText.sp_whole(j1, y) == True{} : Bool}, el1: {String.length(AiText.sp_brk(j1)) == 1n : Nat}, es: {Nat.add(1n, 1n+k) == 1n+j : Nat}, ks: aitb.KS(w, 1n+k)) -> aitb.BS(SCon{Chr{xc}, w}, 1n+j):
  (+j2, (+r, (ew, (w2, el)))) = ks
  +y = String.append(AiText.sp_brk(j2), r)
  +ew2 = ew
  (j1, (j2, (r, (Equal.trans(String, SCon{Chr{xc}, w}, SCon{Chr{c}, w}, String.append(AiText.sp_brk(j1), y), ex, Equal.trans(String, SCon{Chr{c}, w}, String.append(AiText.sp_brk(j1), w), String.append(AiText.sp_brk(j1), y), Equal.sym(String, String.append(AiText.sp_brk(j1), w), SCon{Chr{c}, w}, eh), Equal.cong(String, String, z => String.append(AiText.sp_brk(j1), z), w, y, ew2))), (ew1(y, ew2), (w2, Equal.trans(Nat, Nat.add(String.length(AiText.sp_brk(j1)), String.length(AiText.sp_brk(j2))), Nat.add(1n, 1n+k), 1n+j, Equal.trans(Nat, Nat.add(String.length(AiText.sp_brk(j1)), String.length(AiText.sp_brk(j2))), Nat.add(1n, String.length(AiText.sp_brk(j2))), Nat.add(1n, 1n+k), Equal.cong(Nat, Nat, z => Nat.add(z, String.length(AiText.sp_brk(j2))), String.length(AiText.sp_brk(j1)), 1n, el1), Equal.cong(Nat, Nat, z => Nat.add(1n, z), String.length(AiText.sp_brk(j2)), 1n+k, el)), es)))))))

def aitb.fin_sv1(+j1: Nat, -xc: U32, +c: U32, +w: String, -j: Nat, ex: {SCon{Chr{xc}, w} == SCon{Chr{c}, w} : String}, eh: {String.append(AiText.sp_brk(j1), w) == SCon{Chr{c}, w} : String}, ew1: @y: String -> {w == y : String} -> {AiText.sp_whole(j1, y) == True{} : Bool}, el1: {String.length(AiText.sp_brk(j1)) == 1n : Nat}, sv: aitb.SV(0n, T.brk(w), j)) -> aitb.BS(SCon{Chr{xc}, w}, 1n+j):
  (+k, (ek, es)) = sv
  aitb.fin_one(j1, xc, c, w, j, k, ex, eh, ew1, el1, es, aitb.brk_sound(w, k, ek))

def aitb.fin_sv2(-xc: U32, -yc: U32, +w: String, -j: Nat, ex: {SCon{Chr{xc}, SCon{Chr{yc}, w}} == SCon{Chr{13}, SCon{Chr{10}, w}} : String}, sv: aitb.SV(1n, T.brk(w), j)) -> aitb.BS(SCon{Chr{xc}, SCon{Chr{yc}, w}}, 1n+j):
  (+k, (ek, es)) = sv
  aitb.fin_crlf(xc, yc, w, j, k, ex, es, aitb.brk_sound(w, k, ek))

# after `\r`, a char other than `\n`: the text after the `\r` is read
# whole as `\r`
def aitb.whole_cr(+yc: U32, -w: String, eb: {U32.is_eq(yc, 10) == False{} : Bool}, +y: String, e: {SCon{Chr{yc}, w} == y : String}) -> {AiText.sp_whole(1n, y) == True{} : Bool}:
  Equal.trans(Bool, AiText.sp_no_lf(y), AiText.sp_no_lf(SCon{Chr{yc}, w}), True{}, Equal.cong(String, Bool, z => AiText.sp_no_lf(z), y, SCon{Chr{yc}, w}, Equal.sym(String, SCon{Chr{yc}, w}, y, e)), LA.mnb.not_f(U32.is_eq(yc, 10), eb))

def aitb.bnd_cr_s(b: Bool, +xc: U32, +yc: U32, +w: String, -j: Nat, ex: {SCon{Chr{xc}, SCon{Chr{yc}, w}} == SCon{Chr{13}, SCon{Chr{yc}, w}} : String}, eb: {U32.is_eq(yc, 10) == b : Bool}, e: {T.bnd.cr.at(b, SCon{Chr{yc}, w}, w) == 1n+j : Nat}) -> aitb.BS(SCon{Chr{xc}, SCon{Chr{yc}, w}}, 1n+j):
  match b:
    case True{}:
      aitb.fin_sv2(xc, yc, w, j, Equal.trans(String, SCon{Chr{xc}, SCon{Chr{yc}, w}}, SCon{Chr{13}, SCon{Chr{yc}, w}}, SCon{Chr{13}, SCon{Chr{10}, w}}, ex, Equal.cong(U32, String, v => SCon{Chr{13}, SCon{Chr{v}, w}}, yc, 10, PWireBoolExact.wr_eq_sound(yc, 10, eb))), aitb.second_inv(1n, T.brk(w), j, e))
    case False{}:
      +eb2 = eb
      aitb.fin_sv1(1n, xc, 13, SCon{Chr{yc}, w}, j, ex, {==}, y => ey => aitb.whole_cr(yc, w, eb2, y, ey), {==}, aitb.second_inv(0n, T.brk(SCon{Chr{yc}, w}), j, e))

def aitb.bnd_at_s(cr: Bool, lf: Bool, +xc: U32, +t: String, -j: Nat, ecr: {U32.is_eq(xc, 13) == cr : Bool}, elf: {U32.is_eq(xc, 10) == lf : Bool}, e: {T.bnd.at(cr, lf, t) == 1n+j : Nat}) -> aitb.BS(SCon{Chr{xc}, t}, 1n+j):
  match cr:
    case True{}:
      match t:
        case SNil{}:
          aitb.zs(aitb.BS(SCon{Chr{xc}, SNil{}}, 1n+j), j, e)
        case SCon{y, +w}:
          match y:
            case Chr{+yc}:
              aitb.bnd_cr_s(U32.is_eq(yc, 10), xc, yc, w, j, Equal.cong(U32, String, v => SCon{Chr{v}, SCon{Chr{yc}, w}}, xc, 13, PWireBoolExact.wr_eq_sound(xc, 13, ecr)), {==}, e)
    case False{}:
      match lf:
        case True{}:
          aitb.fin_sv1(2n, xc, 10, t, j, Equal.cong(U32, String, v => SCon{Chr{v}, t}, xc, 10, PWireBoolExact.wr_eq_sound(xc, 10, elf)), {==}, y => ey => {==}, {==}, aitb.second_inv(0n, T.brk(t), j, e))
        case False{}:
          aitb.zs(aitb.BS(SCon{Chr{xc}, t}, 1n+j), j, e)

# a length the code finds at the start of u: two breaks read whole there
def aitb.bnd_sound(u: String, -j: Nat, e: {T.bnd(u) == 1n+j : Nat}) -> aitb.BS(u, 1n+j):
  match u:
    case SNil{}:
      aitb.zs(aitb.BS(SNil{}, 1n+j), j, e)
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          aitb.bnd_at_s(U32.is_eq(xc, 13), U32.is_eq(xc, 10), xc, t, j, {==}, {==}, e)

# The walk
# --------

def aitb.miss(b: Nat, rest: Unit -> Maybe<&2, T.Span>, eb: {b == 0n : Nat}) -> {T.boundary.at(b, rest) == T.shift(rest(Unit{})) : Maybe<&2, T.Span>}:
  match b:
    case 0n:
      {==}
    case 1n+j:
      aitb.zs({T.boundary.at(1n+j, rest) == T.shift(rest(Unit{})) : Maybe<&2, T.Span>}, j, Equal.sym(Nat, 1n+j, 0n, eb))

def aitb.hit(b: Nat, rest: Unit -> Maybe<&2, T.Span>, +n: Nat, eb: {b == n : Nat}, nz: {aitb.zero(n) == False{} : Bool}) -> {T.boundary.at(b, rest) == Some{T.Span{0n, n}} : Maybe<&2, T.Span>}:
  match b:
    case 0n:
      aitb.zero_n(n, {T.boundary.at(0n, rest) == Some{T.Span{0n, n}} : Maybe<&2, T.Span>}, eb, nz)
    case 1n+j:
      Equal.cong(Nat, Maybe<&2, T.Span>, z => Some{T.Span{0n, z}}, 1n+j, n, eb)

def aitb.hit_str(u: String, +n: Nat, eu: {T.bnd(u) == n : Nat}, nz: {aitb.zero(n) == False{} : Bool}) -> {T.event_boundary(u) == Some{T.Span{0n, n}} : Maybe<&2, T.Span>}:
  match u:
    case SNil{}:
      aitb.zero_n(n, {T.event_boundary(SNil{}) == Some{T.Span{0n, n}} : Maybe<&2, T.Span>}, eu, nz)
    case SCon{+x, +t}:
      aitb.hit(T.bnd(SCon{x, t}), v => T.event_boundary(t), n, eu, nz)

# no boundary before two breaks read whole: the walk answers them
def aitb.first(a: String, +j1: Nat, +j2: Nat, +r: String, hw1: {AiText.sp_whole(j1, String.append(AiText.sp_brk(j2), r)) == True{} : Bool}, hw2: {AiText.sp_whole(j2, r) == True{} : Bool}, ha: {AiText.sp_clear(a, String.append(AiText.sp_brk(j1), String.append(AiText.sp_brk(j2), r))) == True{} : Bool}) -> {T.event_boundary(String.append(a, String.append(AiText.sp_brk(j1), String.append(AiText.sp_brk(j2), r)))) == Some{T.Span{String.length(a), AiText.sp_span_len(j1, j2)}} : Maybe<&2, T.Span>}:
  match a:
    case SNil{}:
      aitb.hit_str(String.append(AiText.sp_brk(j1), String.append(AiText.sp_brk(j2), r)), AiText.sp_span_len(j1, j2), aitb.eq(j1, j2, r, hw1, hw2), aitb.span_nz(j1, j2))
    case SCon{+x, +rest}:
      +X = String.append(AiText.sp_brk(j1), String.append(AiText.sp_brk(j2), r))
      +u = String.append(rest, X)
      +hh = ha
      +n = AiText.sp_span_len(j1, j2)
      Equal.trans(Maybe<&2, T.Span>, T.event_boundary(SCon{x, u}), T.shift(T.event_boundary(u)), Some{T.Span{1n+String.length(rest), n}}, aitb.miss(T.bnd(SCon{x, u}), v => T.event_boundary(u), aitb.no_bnd(SCon{x, u}, LA.mnb.and_l(Bool.not(AiText.sp_bnd_at(SCon{x, u})), AiText.sp_clear(rest, X), hh))), Equal.cong(Maybe<&2, T.Span>, Maybe<&2, T.Span>, z => T.shift(z), T.event_boundary(u), Some{T.Span{String.length(rest), n}}, aitb.first(rest, j1, j2, r, hw1, hw2, LA.mnb.and_r(Bool.not(AiText.sp_bnd_at(SCon{x, u})), AiText.sp_clear(rest, X), hh))))

# no boundary at any place: the walk answers none
def aitb.none(s: String, h: {AiText.sp_clear(s, "") == True{} : Bool}) -> {T.event_boundary(s) == None{} : Maybe<&2, T.Span>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      +hh = h
      +hn = Equal.trans(Bool, Bool.not(AiText.sp_bnd_at(SCon{x, t})), Bool.not(AiText.sp_bnd_at(SCon{x, String.append(t, "")})), True{}, Equal.cong(String, Bool, z => Bool.not(AiText.sp_bnd_at(SCon{x, z})), t, String.append(t, ""), Equal.sym(String, String.append(t, ""), t, LA.mnb.app_nil(t))), LA.mnb.and_l(Bool.not(AiText.sp_bnd_at(SCon{x, String.append(t, "")})), AiText.sp_clear(t, ""), hh))
      Equal.trans(Maybe<&2, T.Span>, T.event_boundary(SCon{x, t}), T.shift(T.event_boundary(t)), None{}, aitb.miss(T.bnd(SCon{x, t}), v => T.event_boundary(t), aitb.no_bnd(SCon{x, t}, hn)), Equal.cong(Maybe<&2, T.Span>, Maybe<&2, T.Span>, z => T.shift(z), T.event_boundary(t), None{}, aitb.none(t, LA.mnb.and_r(Bool.not(AiText.sp_bnd_at(SCon{x, String.append(t, "")})), AiText.sp_clear(t, ""), hh))))

def aitb.GS(s: String, i: Nat, l: Nat) -> Type:
  Sigma<&1, &1, String, a => Sigma<&1, &1, Nat, j1 => Sigma<&1, &1, Nat, j2 => Sigma<&1, &1, String, r => {s == String.append(a, String.append(AiText.sp_brk(j1), String.append(AiText.sp_brk(j2), r))) : String} & ({AiText.sp_whole(j1, String.append(AiText.sp_brk(j2), r)) == True{} : Bool} & ({AiText.sp_whole(j2, r) == True{} : Bool} & ({AiText.sp_clear(a, String.append(AiText.sp_brk(j1), String.append(AiText.sp_brk(j2), r))) == True{} : Bool} & ({String.length(a) == i : Nat} & {AiText.sp_span_len(j1, j2) == l : Nat}))))>>>>

def aitb.hit_fin(-u: String, -j: Nat, +i: Nat, +l: Nat, h: {Some{T.Span{0n, 1n+j}} == Some{T.Span{i, l}} : Maybe<&2, T.Span>}, bs: aitb.BS(u, 1n+j)) -> aitb.GS(u, i, l):
  (+j1, (+j2, (+r, (e, (w1, (w2, es)))))) = bs
  +hh = h
  (SNil{}, (j1, (j2, (r, (e, (w1, (w2, ({==}, (Equal.cong(Maybe<&2, T.Span>, Nat, z => aitb.st(z), Some{T.Span{0n, 1n+j}}, Some{T.Span{i, l}}, hh), Equal.trans(Nat, AiText.sp_span_len(j1, j2), 1n+j, l, es, Equal.cong(Maybe<&2, T.Span>, Nat, z => aitb.ln(z), Some{T.Span{0n, 1n+j}}, Some{T.Span{i, l}}, hh)))))))))))

def aitb.next(+x: Char, +t: String, -k: Nat, -i: Nat, -l: Nat, eb: {T.bnd(SCon{x, t}) == 0n : Nat}, ei: {1n+k == i : Nat}, gs: aitb.GS(t, k, l)) -> aitb.GS(SCon{x, t}, i, l):
  (+a, (+j1, (+j2, (+r, (e, (w1, (w2, (cl, (ea, el))))))))) = gs
  +X = String.append(AiText.sp_brk(j1), String.append(AiText.sp_brk(j2), r))
  +y = String.append(a, X)
  +ee = e
  +nb = Equal.trans(Bool, Bool.not(AiText.sp_bnd_at(SCon{x, t})), aitb.zero(T.bnd(SCon{x, t})), True{}, Equal.sym(Bool, aitb.zero(T.bnd(SCon{x, t})), Bool.not(AiText.sp_bnd_at(SCon{x, t})), aitb.zero_bnd(SCon{x, t})), Equal.cong(Nat, Bool, z => aitb.zero(z), T.bnd(SCon{x, t}), 0n, eb))
  +mv = Equal.trans(Bool, Bool.not(AiText.sp_bnd_at(SCon{x, y})), Bool.not(AiText.sp_bnd_at(SCon{x, t})), True{}, Equal.cong(String, Bool, z => Bool.not(AiText.sp_bnd_at(SCon{x, z})), y, t, Equal.sym(String, t, y, ee)), nb)
  (SCon{x, a}, (j1, (j2, (r, (LA.mnb.cons_eq(x, t, y, ee), (w1, (w2, (LA.mnb.and_t(Bool.not(AiText.sp_bnd_at(SCon{x, y})), AiText.sp_clear(a, X), mv, cl), (Equal.trans(Nat, 1n+String.length(a), 1n+k, i, Equal.cong(Nat, Nat, z => 1n+z, String.length(a), k, ea), ei), el)))))))))

def aitb.miss_fin(+x: Char, +t: String, -i: Nat, +l: Nat, eb: {T.bnd(SCon{x, t}) == 0n : Nat}, si: aitb.SI(T.event_boundary(t), i, l), ih: @k: Nat -> {T.event_boundary(t) == Some{T.Span{k, l}} : Maybe<&2, T.Span>} -> aitb.GS(t, k, l)) -> aitb.GS(SCon{x, t}, i, l):
  (+k, (em, ei)) = si
  aitb.next(x, t, k, i, l, eb, ei, ih(k, em))

def aitb.sound_at(b: Nat, +x: Char, +t: String, +i: Nat, +l: Nat, eb: {T.bnd(SCon{x, t}) == b : Nat}, h: {T.boundary.at(b, v => T.event_boundary(t)) == Some{T.Span{i, l}} : Maybe<&2, T.Span>}, ih: @k: Nat -> {T.event_boundary(t) == Some{T.Span{k, l}} : Maybe<&2, T.Span>} -> aitb.GS(t, k, l)) -> aitb.GS(SCon{x, t}, i, l):
  match b:
    case 0n:
      aitb.miss_fin(x, t, i, l, eb, aitb.shift_inv(T.event_boundary(t), i, l, h), ih)
    case 1n+j:
      aitb.hit_fin(SCon{x, t}, j, i, l, h, aitb.bnd_sound(SCon{x, t}, j, eb))

# an answer of the walk: the first place with two breaks read whole
def aitb.sound(s: String, +i: Nat, +l: Nat, h: {T.event_boundary(s) == Some{T.Span{i, l}} : Maybe<&2, T.Span>}) -> aitb.GS(s, i, l):
  match s:
    case SNil{}:
      LD.aitd.none_some(T.Span, T.Span{i, l}, aitb.GS(SNil{}, i, l), h)
    case SCon{+x, +t}:
      aitb.sound_at(T.bnd(SCon{x, t}), x, t, i, l, {==}, h, k => e => aitb.sound(t, k, l, e))

def aitb.pair(+a: Nat, +b: Nat, +c: Nat, -d: Nat, e1: {a == c : Nat}, e2: {b == d : Nat}) -> {(a, b) == (c, d) : Nat & Nat}:
  Equal.trans(Nat & Nat, (a, b), (c, b), (c, d), Equal.cong(Nat, Nat & Nat, z => (z, b), a, c, e1), Equal.cong(Nat, Nat & Nat, z => (c, z), b, d, e2))

# the answer of the sound walk, start and length as one pair
def aitb.fin_law(-s: String, +i: Nat, -l: Nat, gs: aitb.GS(s, i, l)) -> Sigma<&1, &1, String, a => Sigma<&1, &1, Nat, j1 => Sigma<&1, &1, Nat, j2 => Sigma<&1, &1, String, r => {s == String.append(a, String.append(AiText.sp_brk(j1), String.append(AiText.sp_brk(j2), r))) : String} & ({AiText.sp_whole(j1, String.append(AiText.sp_brk(j2), r)) == True{} : Bool} & ({AiText.sp_whole(j2, r) == True{} : Bool} & ({AiText.sp_clear(a, String.append(AiText.sp_brk(j1), String.append(AiText.sp_brk(j2), r))) == True{} : Bool} & {(String.length(a), AiText.sp_span_len(j1, j2)) == (i, l) : Nat & Nat})))>>>>:
  (+a, (+j1, (+j2, (+r, (e, (w1, (w2, (cl, (ea, el))))))))) = gs
  (a, (j1, (j2, (r, (e, (w1, (w2, (cl, aitb.pair(String.length(a), AiText.sp_span_len(j1, j2), i, l, ea, el)))))))))
