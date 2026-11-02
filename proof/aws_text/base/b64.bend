# eukhe: lemmas of the aws_text proofs: R3 base64. The chunks are read as
# one text (awq.chunks: one pass over each chunk, in order, is one pass over
# their concatenation); the count of UTF-16 units modulo 4 and the phase
# (body, one `=`, two, invalid) are the spec's length and validity
# (awq.go); a valid text is base64 chars then "", "=" or "==" (awq.valid_*).

import Base
import ../../../bend/aws_text.bend as A
import ../../../laws/aws_text.bend as AwsText
import ../../model_name/base.bend as LA
import ../../wire/wire_bool_exact.bend as PWireBoolExact

# the count a state holds
def awq.qn(q: A.Q) -> Nat:
  match q:
    case A.Q0{}:
      0n
    case A.Q1{}:
      1n
    case A.Q2{}:
      2n
    case A.Q3{}:
      3n

# what the rest t of the text must be, from the phase p
def awq.ok(p: A.Ph, t: String) -> Bool:
  match p:
    case A.PB{}:
      AwsText.sp_valid(t)
    case A.P1{}:
      match t:
        case SNil{}:
          True{}
        case SCon{y, u}:
          Bool.and(AwsText.sp_eqc(y), String.is_empty(u))
    case A.P2{}:
      String.is_empty(t)
    case A.PX{}:
      False{}

# Steps
# -----

# a char of w units moves the count as the spec's length does
def awq.qstep(q: A.Q, w: Bool, -r: Nat) -> {AwsText.sp_mult4(Nat.add(awq.qn(A.q.add(q, w)), r)) == AwsText.sp_mult4(Nat.add(awq.qn(q), Nat.add(AwsText.sp_unit.at(w), r))) : Bool}:
  match q:
    case A.Q0{}:
      match w:
        case True{}:
          {==}
        case False{}:
          {==}
    case A.Q1{}:
      match w:
        case True{}:
          {==}
        case False{}:
          {==}
    case A.Q2{}:
      match w:
        case True{}:
          {==}
        case False{}:
          {==}
    case A.Q3{}:
      match w:
        case True{}:
          {==}
        case False{}:
          {==}

def awq.pb_pad(e: Bool, +xc: U32, t: String, ee: {U32.is_eq(xc, 61) == e : Bool}) -> {awq.ok(A.ph.body(False{}, e), t) == AwsText.sp_pad(SCon{Chr{xc}, t}) : Bool}:
  match e:
    case True{}:
      match t:
        case SNil{}:
          Equal.sym(Bool, U32.is_eq(xc, 61), True{}, ee)
        case SCon{y, u}:
          %Equal.sym(Bool, U32.is_eq(xc, 61), True{}, ee) : {Bool.and(AwsText.sp_eqc(y), String.is_empty(u)) == Bool.and(Bool.and(_, AwsText.sp_eqc(y)), String.is_empty(u)) : Bool}
          {==}
    case False{}:
      match t:
        case SNil{}:
          Equal.sym(Bool, U32.is_eq(xc, 61), False{}, ee)
        case SCon{y, u}:
          %Equal.sym(Bool, U32.is_eq(xc, 61), False{}, ee) : {False{} == Bool.and(Bool.and(_, AwsText.sp_eqc(y)), String.is_empty(u)) : Bool}
          {==}

def awq.pb(b: Bool, +xc: U32, +t: String) -> {awq.ok(A.ph.body(b, U32.is_eq(xc, 61)), t) == Bool.or(Bool.and(b, AwsText.sp_valid(t)), Bool.and(Bool.not(b), AwsText.sp_pad(SCon{Chr{xc}, t}))) : Bool}:
  match b:
    case True{}:
      Equal.sym(Bool, Bool.or(AwsText.sp_valid(t), False{}), AwsText.sp_valid(t), LA.mnb.or_false(AwsText.sp_valid(t)))
    case False{}:
      awq.pb_pad(U32.is_eq(xc, 61), xc, t, {==})

def awq.p1(e: Bool, -t: String) -> {awq.ok(A.ph.pad(e, A.P2{}), t) == Bool.and(e, String.is_empty(t)) : Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

# a char moves the phase as the spec reads the rest
def awq.pstep(p: A.Ph, c: Char, +t: String) -> {awq.ok(A.ph.step(p, c), t) == awq.ok(p, SCon{c, t}) : Bool}:
  match p:
    case A.PB{}:
      match c:
        case Chr{+xc}:
          awq.pb(A.is_b64(Chr{xc}), xc, t)
    case A.P1{}:
      match c:
        case Chr{+xc}:
          awq.p1(U32.is_eq(xc, 61), t)
    case A.P2{}:
      {==}
    case A.PX{}:
      {==}

# The pass
# --------

# the verdict after t, from q and p, is the spec's verdict of the count and
# the rest
def awq.go(t: String, +q: A.Q, +p: A.Ph) -> {A.b64.verdict(A.b64.go(t, q, p)) == AwsText.sp_b64_fin(AwsText.sp_mult4(Nat.add(awq.qn(q), AwsText.sp_units(t))), awq.ok(p, t)) : Nat}:
  match t:
    case SNil{}:
      match q:
        case A.Q0{}:
          match p:
            case A.PB{}:
              {==}
            case A.P1{}:
              {==}
            case A.P2{}:
              {==}
            case A.PX{}:
              {==}
        case A.Q1{}:
          {==}
        case A.Q2{}:
          {==}
        case A.Q3{}:
          {==}
    case SCon{c, +rest}:
      match c:
        case Chr{+xc}:
          +q2 = A.q.add(q, U32.is_lt(65535, xc))
          +p2 = A.ph.step(p, Chr{xc})
          +w = U32.is_lt(65535, xc)
          %Equal.sym(Nat, A.b64.verdict(A.b64.go(rest, q2, p2)), AwsText.sp_b64_fin(AwsText.sp_mult4(Nat.add(awq.qn(q2), AwsText.sp_units(rest))), awq.ok(p2, rest)), awq.go(rest, q2, p2)) : {_ == AwsText.sp_b64_fin(AwsText.sp_mult4(Nat.add(awq.qn(q), Nat.add(AwsText.sp_unit.at(w), AwsText.sp_units(rest)))), awq.ok(p, SCon{Chr{xc}, rest})) : Nat}
          %Equal.sym(Bool, AwsText.sp_mult4(Nat.add(awq.qn(q2), AwsText.sp_units(rest))), AwsText.sp_mult4(Nat.add(awq.qn(q), Nat.add(AwsText.sp_unit.at(w), AwsText.sp_units(rest)))), awq.qstep(q, w, AwsText.sp_units(rest))) : {AwsText.sp_b64_fin(_, awq.ok(p2, rest)) == AwsText.sp_b64_fin(AwsText.sp_mult4(Nat.add(awq.qn(q), Nat.add(AwsText.sp_unit.at(w), AwsText.sp_units(rest)))), awq.ok(p, SCon{Chr{xc}, rest})) : Nat}
          %Equal.sym(Bool, awq.ok(p2, rest), awq.ok(p, SCon{Chr{xc}, rest}), awq.pstep(p, Chr{xc}, rest)) : {AwsText.sp_b64_fin(AwsText.sp_mult4(Nat.add(awq.qn(q), Nat.add(AwsText.sp_unit.at(w), AwsText.sp_units(rest)))), _) == AwsText.sp_b64_fin(AwsText.sp_mult4(Nat.add(awq.qn(q), Nat.add(AwsText.sp_unit.at(w), AwsText.sp_units(rest)))), awq.ok(p, SCon{Chr{xc}, rest})) : Nat}
          {==}

# one pass over a then b is one pass over a ++ b
def awq.app(a: String, -b: String, st: A.St) -> {A.b64.go1(String.append(a, b), st) == A.b64.go1(b, A.b64.go1(a, st)) : A.St}:
  match a:
    case SNil{}:
      match st:
        case A.St{q, p}:
          {==}
    case SCon{+c, +a2}:
      match st:
        case A.St{+q, +p}:
          awq.app(a2, b, A.St{A.q.add(q, A.wide(c)), A.ph.step(p, c)})

# the chunks, one after the other, are their concatenation
def awq.chunks(cs: List<&2, String>, +st: A.St) -> {A.b64.chunks(cs, st) == A.b64.go1(AwsText.sp_cat(cs), st) : A.St}:
  match cs:
    case Nil{}:
      match st:
        case A.St{q, p}:
          {==}
    case +c <> +more:
      +st2 = A.b64.go1(c, st)
      Equal.trans(A.St, A.b64.chunks(more, st2), A.b64.go1(AwsText.sp_cat(more), st2), A.b64.go1(String.append(c, AwsText.sp_cat(more)), st), awq.chunks(more, st2), Equal.sym(A.St, A.b64.go1(String.append(c, AwsText.sp_cat(more)), st), A.b64.go1(AwsText.sp_cat(more), A.b64.go1(c, st)), awq.app(c, AwsText.sp_cat(more), st)))

# the code's verdict is the spec's verdict of the text the chunks make
def awq.decides(+cs: List<&2, String>) -> {A.base64(cs) == AwsText.sp_base64(AwsText.sp_cat(cs)) : Nat}:
  %Equal.sym(A.St, A.b64.chunks(cs, A.St{A.Q0{}, A.PB{}}), A.b64.go1(AwsText.sp_cat(cs), A.St{A.Q0{}, A.PB{}}), awq.chunks(cs, A.St{A.Q0{}, A.PB{}})) : {A.b64.verdict(_) == AwsText.sp_base64(AwsText.sp_cat(cs)) : Nat}
  awq.go(AwsText.sp_cat(cs), A.Q0{}, A.PB{})

# Valid texts
# -----------

def awq.or_and(g: Bool, v: Bool, -z: Bool, eg: {g == True{} : Bool}, ev: {v == True{} : Bool}) -> {Bool.or(Bool.and(g, v), z) == True{} : Bool}:
  match g:
    case True{}:
      match v:
        case True{}:
          {==}
        case False{}:
          LA.mnb.absurd_f({Bool.or(False{}, z) == True{} : Bool}, ev)
    case False{}:
      LA.mnb.absurd_f({Bool.or(Bool.and(False{}, v), z) == True{} : Bool}, eg)

def awq.pad_eq(+xc: U32, t: String, he: {AwsText.sp_pad(SCon{Chr{xc}, t}) == True{} : Bool}) -> {U32.is_eq(xc, 61) == True{} : Bool}:
  match t:
    case SNil{}:
      he
    case SCon{+y, +u}:
      +hh = he
      LA.mnb.and_l(U32.is_eq(xc, 61), AwsText.sp_eqc(y), LA.mnb.and_l(Bool.and(U32.is_eq(xc, 61), AwsText.sp_eqc(y)), String.is_empty(u), hh))

# the padding alone is valid
def awq.valid_pad(e: String, he: {AwsText.sp_pad(e) == True{} : Bool}) -> {AwsText.sp_valid(e) == True{} : Bool}:
  match e:
    case SNil{}:
      {==}
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +hh = he
          +e61 = PWireBoolExact.wr_eq_sound(xc, 61, awq.pad_eq(xc, t, hh))
          +h61 = Equal.trans(Bool, AwsText.sp_pad(SCon{Chr{61}, t}), AwsText.sp_pad(SCon{Chr{xc}, t}), True{}, Equal.cong(U32, Bool, z => AwsText.sp_pad(SCon{Chr{z}, t}), 61, xc, Equal.sym(U32, xc, 61, e61)), hh)
          %Equal.sym(U32, xc, 61, e61) : {AwsText.sp_valid(SCon{Chr{_}, t}) == True{} : Bool}
          h61

# base64 chars, then the padding, are valid
def awq.valid_app(b: String, +e: String, hb: {AwsText.sp_all_b64(b) == True{} : Bool}, he: {AwsText.sp_pad(e) == True{} : Bool}) -> {AwsText.sp_valid(String.append(b, e)) == True{} : Bool}:
  match b:
    case SNil{}:
      awq.valid_pad(e, he)
    case SCon{+x, +t}:
      +hh = hb
      awq.or_and(AwsText.sp_b64c(x), AwsText.sp_valid(String.append(t, e)), Bool.and(Bool.not(AwsText.sp_b64c(x)), AwsText.sp_pad(SCon{x, String.append(t, e)})), LA.mnb.and_l(AwsText.sp_b64c(x), AwsText.sp_all_b64(t), hh), awq.valid_app(t, e, LA.mnb.and_r(AwsText.sp_b64c(x), AwsText.sp_all_b64(t), hh), he))

def awq.VP(t: String, v: Bool) -> Type:
  match v:
    case True{}:
      Sigma<&1, &1, String, b => Sigma<&1, &1, String, e => {t == String.append(b, e) : String} & ({AwsText.sp_all_b64(b) == True{} : Bool} & {AwsText.sp_pad(e) == True{} : Bool})>>
    case False{}:
      Unit

def awq.vs_pad(+x: Char, +rest: String, pv: Bool, epv: {AwsText.sp_pad(SCon{x, rest}) == pv : Bool}) -> awq.VP(SCon{x, rest}, pv):
  match pv:
    case True{}:
      (SNil{}, (SCon{x, rest}, ({==}, ({==}, epv))))
    case False{}:
      Unit{}

def awq.vs(+x: Char, +rest: String, g: Bool, eg: {AwsText.sp_b64c(x) == g : Bool}, v: Bool, ih: awq.VP(rest, v)) -> awq.VP(SCon{x, rest}, Bool.or(Bool.and(g, v), Bool.and(Bool.not(g), AwsText.sp_pad(SCon{x, rest})))):
  match g:
    case True{}:
      match v:
        case True{}:
          (+b, (+e, (eq, (ab, pe)))) = ih
          (SCon{x, b}, (e, (LA.mnb.cons_eq(x, rest, String.append(b, e), eq), (LA.mnb.and_t(AwsText.sp_b64c(x), AwsText.sp_all_b64(b), eg, ab), pe))))
        case False{}:
          Unit{}
    case False{}:
      awq.vs_pad(x, rest, AwsText.sp_pad(SCon{x, rest}), {==})

# a valid text is base64 chars, then the padding
def awq.valid_sp(t: String) -> awq.VP(t, AwsText.sp_valid(t)):
  match t:
    case SNil{}:
      (SNil{}, (SNil{}, ({==}, ({==}, {==}))))
    case SCon{+x, +rest}:
      awq.vs(x, rest, AwsText.sp_b64c(x), {==}, AwsText.sp_valid(rest), awq.valid_sp(rest))

def awq.BN(n: Nat, G: Type) -> Type:
  match n:
    case 0n:
      G
    case 1n+k:
      Unit

def awq.nat_absurd(-G: Type, -k: Nat, e: {1n+k == 0n : Nat}) -> G:
  %e : awq.BN(_, G)
  Unit{}

# a verdict 0: the length is a multiple of 4 and the text is valid
def awq.fin0(m: Bool, v: Bool, h: {AwsText.sp_b64_fin(m, v) == 0n : Nat}) -> {m == True{} : Bool} & {v == True{} : Bool}:
  match m:
    case True{}:
      match v:
        case True{}:
          ({==}, {==})
        case False{}:
          awq.nat_absurd({True{} == True{} : Bool} & {False{} == True{} : Bool}, 1n, h)
    case False{}:
      awq.nat_absurd({False{} == True{} : Bool} & {v == True{} : Bool}, 0n, h)
