# eukhe: lemmas of the model_name proofs: R5 number against its split
# (name = p ++ z ++ d ++ r). drop0 takes off exactly the leading zeros
# (mnn.drop0_sp, mnn.drop0_app); num.first / num.second / num.rest accept
# exactly a passing run of digits and a rest that ends it (mnn.*_sp,
# mnn.*_app).

import Base
import ../../../bend/text_pat.bend as Tp
import ../../../bend/phrase.bend as P
import ../../../bend/model_name.bend as M
import ../../../laws/model_name.bend as ModelName
import ../base.bend as LA

# s opens with no `0`
def mnn.nz(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{x, t}:
      Bool.not(ModelName.sp_zero(x))

# Leading zeros
# -------------

def mnn.DP(s: String, u: String) -> Type:
  Sigma<&1, &1, String, z => {s == String.append(z, u) : String} & ({ModelName.sp_zeros(z) == True{} : Bool} & {mnn.nz(u) == True{} : Bool})>

def mnn.drop0_at(+xc: U32, +t: String, b: Bool, eb: {U32.is_eq(xc, 48) == b : Bool}, ih: mnn.DP(t, M.drop0(t))) -> mnn.DP(SCon{Chr{xc}, t}, M.drop0.at(b, SCon{Chr{xc}, t}, u => M.drop0(t))):
  match b:
    case True{}:
      (+z, (e, (zs, n))) = ih
      (SCon{Chr{xc}, z}, (LA.mnb.cons_eq(Chr{xc}, t, String.append(z, M.drop0(t)), e), (LA.mnb.and_t(U32.is_eq(xc, 48), ModelName.sp_zeros(z), eb, zs), n)))
    case False{}:
      (SNil{}, ({==}, ({==}, LA.mnb.not_f(U32.is_eq(xc, 48), eb))))

# drop0 takes off leading zeros, and what is left opens with no `0`
def mnn.drop0_sp(s: String) -> mnn.DP(s, M.drop0(s)):
  match s:
    case SNil{}:
      (SNil{}, ({==}, ({==}, {==})))
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          mnn.drop0_at(xc, t, U32.is_eq(xc, 48), {==}, mnn.drop0_sp(t))

def mnn.drop0_nz(u: String, h: {mnn.nz(u) == True{} : Bool}) -> {M.drop0(u) == u : String}:
  match u:
    case SNil{}:
      {==}
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          %Equal.sym(Bool, U32.is_eq(xc, 48), False{}, LA.mnb.not_t(U32.is_eq(xc, 48), h)) : {M.drop0.at(_, SCon{Chr{xc}, t}, v => M.drop0(t)) == SCon{Chr{xc}, t} : String}
          {==}

# leading zeros before a text that opens with no `0` are dropped
def mnn.drop0_app(z: String, +u: String, hz: {ModelName.sp_zeros(z) == True{} : Bool}, hu: {mnn.nz(u) == True{} : Bool}) -> {M.drop0(String.append(z, u)) == u : String}:
  match z:
    case SNil{}:
      mnn.drop0_nz(u, hu)
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +h2 = hz
          %Equal.sym(Bool, U32.is_eq(xc, 48), True{}, LA.mnb.and_l(U32.is_eq(xc, 48), ModelName.sp_zeros(t), h2)) : {M.drop0.at(_, SCon{Chr{xc}, String.append(t, u)}, v => M.drop0(String.append(t, u))) == u : String}
          mnn.drop0_app(t, u, LA.mnb.and_r(U32.is_eq(xc, 48), ModelName.sp_zeros(t), h2), hu)

# The run of digits, sound
# ------------------------

def mnn.RP(s: String, w: Bool, v: Bool) -> Type:
  match v:
    case True{}:
      Sigma<&1, &1, String, d => Sigma<&1, &1, String, r => {s == String.append(d, r) : String} & ({ModelName.sp_digits(d) == True{} : Bool} & {ModelName.sp_after(w, r) == True{} : Bool})>>
    case False{}:
      Unit

# the end of a run: no digit at x, the rest after it as it is
def mnn.end_ok(w: Bool, +xc: U32, -t: String, eg: {Tp.is_dig(Chr{xc}) == False{} : Bool}, e2: {M.num.end(w, Chr{xc}) == True{} : Bool}) -> {ModelName.sp_after(w, SCon{Chr{xc}, t}) == True{} : Bool}:
  match w:
    case True{}:
      %Equal.sym(Bool, Tp.is_dig(Chr{xc}), False{}, eg) : {Bool.and(Bool.not(_), U32.is_eq(xc, 45)) == True{} : Bool}
      e2
    case False{}:
      %Equal.sym(Bool, Tp.is_dig(Chr{xc}), False{}, eg) : {Bool.and(Bool.not(_), True{}) == True{} : Bool}
      {==}

def mnn.rest_dig(+xc: U32, -t: String, -w: Bool, eg: {Tp.is_dig(Chr{xc}) == True{} : Bool}, v: Bool, ih: mnn.RP(t, w, v)) -> mnn.RP(SCon{Chr{xc}, t}, w, v):
  match v:
    case True{}:
      (+d, (+r, (e, (dg, af)))) = ih
      (SCon{Chr{xc}, d}, (r, (LA.mnb.cons_eq(Chr{xc}, t, String.append(d, r), e), (LA.mnb.and_t(Tp.is_dig(Chr{xc}), ModelName.sp_digits(d), eg, dg), af))))
    case False{}:
      Unit{}

def mnn.rest_end(+xc: U32, +t: String, +w: Bool, eg: {Tp.is_dig(Chr{xc}) == False{} : Bool}, v: Bool, ev: {M.num.end(w, Chr{xc}) == v : Bool}) -> mnn.RP(SCon{Chr{xc}, t}, w, v):
  match v:
    case True{}:
      (SNil{}, (SCon{Chr{xc}, t}, ({==}, ({==}, mnn.end_ok(w, xc, t, eg, ev)))))
    case False{}:
      Unit{}

def mnn.rest_at(+xc: U32, +t: String, +w: Bool, g: Bool, eg: {Tp.is_dig(Chr{xc}) == g : Bool}, ih: mnn.RP(t, w, M.num.rest(t, w))) -> mnn.RP(SCon{Chr{xc}, t}, w, M.ite(g, u => M.num.rest(t, w), v => M.num.end(w, Chr{xc}))):
  match g:
    case True{}:
      mnn.rest_dig(xc, t, w, eg, M.num.rest(t, w), ih)
    case False{}:
      mnn.rest_end(xc, t, w, eg, M.num.end(w, Chr{xc}), {==})

# num.rest accepts digits, then a rest that ends the run
def mnn.rest_sp(s: String, +w: Bool) -> mnn.RP(s, w, M.num.rest(s, w)):
  match s:
    case SNil{}:
      (SNil{}, (SNil{}, ({==}, ({==}, {==}))))
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          mnn.rest_at(xc, t, w, Tp.is_dig(Chr{xc}), {==}, mnn.rest_sp(t, w))

def mnn.SecP(s: String, ok: Bool, w: Bool, v: Bool) -> Type:
  match v:
    case True{}:
      Sigma<&1, &1, String, d => Sigma<&1, &1, String, r => {s == String.append(d, r) : String} & ({ModelName.sp_digits(d) == True{} : Bool} & ({Bool.or(Bool.not(String.is_empty(d)), ok) == True{} : Bool} & {ModelName.sp_after(w, r) == True{} : Bool}))>>
    case False{}:
      Unit

def mnn.sec_dig(+xc: U32, -t: String, -ok: Bool, -w: Bool, eg: {Tp.is_dig(Chr{xc}) == True{} : Bool}, v: Bool, rp: mnn.RP(t, w, v)) -> mnn.SecP(SCon{Chr{xc}, t}, ok, w, v):
  match v:
    case True{}:
      (+d, (+r, (e, (dg, af)))) = rp
      (SCon{Chr{xc}, d}, (r, (LA.mnb.cons_eq(Chr{xc}, t, String.append(d, r), e), (LA.mnb.and_t(Tp.is_dig(Chr{xc}), ModelName.sp_digits(d), eg, dg), ({==}, af)))))
    case False{}:
      Unit{}

def mnn.sec_end(+xc: U32, +t: String, +ok: Bool, +w: Bool, eg: {Tp.is_dig(Chr{xc}) == False{} : Bool}, v: Bool, ev: {Bool.and(ok, M.num.end(w, Chr{xc})) == v : Bool}) -> mnn.SecP(SCon{Chr{xc}, t}, ok, w, v):
  match v:
    case True{}:
      +e = ev
      (SNil{}, (SCon{Chr{xc}, t}, ({==}, ({==}, (LA.mnb.and_l(ok, M.num.end(w, Chr{xc}), e), mnn.end_ok(w, xc, t, eg, LA.mnb.and_r(ok, M.num.end(w, Chr{xc}), e)))))))
    case False{}:
      Unit{}

def mnn.sec_at(+xc: U32, +t: String, +ok: Bool, +w: Bool, g: Bool, eg: {Tp.is_dig(Chr{xc}) == g : Bool}) -> mnn.SecP(SCon{Chr{xc}, t}, ok, w, M.ite(g, u => M.num.rest(t, w), v => Bool.and(ok, M.num.end(w, Chr{xc})))):
  match g:
    case True{}:
      mnn.sec_dig(xc, t, ok, w, eg, M.num.rest(t, w), mnn.rest_sp(t, w))
    case False{}:
      mnn.sec_end(xc, t, ok, w, eg, Bool.and(ok, M.num.end(w, Chr{xc})), {==})

def mnn.sec_nil(ok: Bool, -w: Bool) -> mnn.SecP(SNil{}, ok, w, ok):
  match ok:
    case True{}:
      (SNil{}, (SNil{}, ({==}, ({==}, ({==}, {==})))))
    case False{}:
      Unit{}

# num.second accepts digits (none only when ok), then a rest that ends the
# run
def mnn.sec_sp(s: String, +ok: Bool, +w: Bool) -> mnn.SecP(s, ok, w, M.num.second(s, ok, w)):
  match s:
    case SNil{}:
      mnn.sec_nil(ok, w)
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          mnn.sec_at(xc, t, ok, w, Tp.is_dig(Chr{xc}), {==})

def mnn.FP(s: String, n: Nat, w: Bool, v: Bool) -> Type:
  match v:
    case True{}:
      Sigma<&1, &1, String, d => Sigma<&1, &1, String, r => {s == String.append(d, r) : String} & ({ModelName.sp_sig(d, n) == True{} : Bool} & {ModelName.sp_after(w, r) == True{} : Bool})>>
    case False{}:
      Unit

def mnn.first_dig(+xc: U32, -t: String, +n: Nat, -w: Bool, eg: {Tp.is_dig(Chr{xc}) == True{} : Bool}, hz: {Bool.not(U32.is_eq(xc, 48)) == True{} : Bool}, v: Bool, sp: mnn.SecP(t, Nat.is_le(n, M.digit(Chr{xc})), w, v)) -> mnn.FP(SCon{Chr{xc}, t}, n, w, v):
  match v:
    case True{}:
      (+d, (+r, (e, (dg, (ne, af))))) = sp
      (SCon{Chr{xc}, d}, (r, (LA.mnb.cons_eq(Chr{xc}, t, String.append(d, r), e), (LA.mnb.and_t(Bool.and(Tp.is_dig(Chr{xc}), Bool.not(U32.is_eq(xc, 48))), Bool.and(ModelName.sp_digits(d), Bool.or(Bool.not(String.is_empty(d)), Nat.is_le(n, M.digit(Chr{xc})))), LA.mnb.and_t(Tp.is_dig(Chr{xc}), Bool.not(U32.is_eq(xc, 48)), eg, hz), LA.mnb.and_t(ModelName.sp_digits(d), Bool.or(Bool.not(String.is_empty(d)), Nat.is_le(n, M.digit(Chr{xc}))), dg, ne)), af))))
    case False{}:
      Unit{}

def mnn.first_at(+xc: U32, +t: String, +n: Nat, +w: Bool, hz: {Bool.not(U32.is_eq(xc, 48)) == True{} : Bool}, g: Bool, eg: {Tp.is_dig(Chr{xc}) == g : Bool}) -> mnn.FP(SCon{Chr{xc}, t}, n, w, M.ite(g, u => M.num.second(t, Nat.is_le(n, M.digit(Chr{xc})), w), v => False{})):
  match g:
    case True{}:
      mnn.first_dig(xc, t, n, w, eg, hz, M.num.second(t, Nat.is_le(n, M.digit(Chr{xc})), w), mnn.sec_sp(t, Nat.is_le(n, M.digit(Chr{xc})), w))
    case False{}:
      Unit{}

# num.first, on a text that opens with no `0`, accepts a passing run and a
# rest that ends it
def mnn.first_sp(s: String, +n: Nat, +w: Bool, hz: {mnn.nz(s) == True{} : Bool}) -> mnn.FP(s, n, w, M.num.first(s, n, w)):
  match s:
    case SNil{}:
      Unit{}
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          mnn.first_at(xc, t, n, w, hz, Tp.is_dig(Chr{xc}), {==})

def mnn.NumsP(ps: List<&2, String>, s: String, n: Nat, w: Bool, b: Bool) -> Type:
  match b:
    case True{}:
      Sigma<&1, &1, List<&2, String>, pre => Sigma<&1, &1, String, p => Sigma<&1, &1, List<&2, String>, post => Sigma<&1, &1, String, z => Sigma<&1, &1, String, d => Sigma<&1, &1, String, r => {ps == List.append(&2, String, pre, p <> post) : List<&2, String>} & ({s == String.append(p, String.append(z, String.append(d, r))) : String} & ({ModelName.sp_zeros(z) == True{} : Bool} & ({ModelName.sp_sig(d, n) == True{} : Bool} & {ModelName.sp_after(w, r) == True{} : Bool})))>>>>>>
    case False{}:
      Unit

def mnn.nums_next(+q: String, +more: List<&2, String>, -s: String, -n: Nat, -w: Bool, b2: Bool, v2: mnn.NumsP(more, s, n, w, b2)) -> mnn.NumsP(q <> more, s, n, w, b2):
  match b2:
    case True{}:
      (+pre, (+p, (+post, (+z, (+d, (+r, (e1, e2))))))) = v2
      (q <> pre, (p, (post, (z, (d, (r, (LA.mnb.lcons_eq(q, more, List.append(&2, String, pre, p <> post), e1), e2)))))))
    case False{}:
      Unit{}

def mnn.nums_hit(+q: String, +more: List<&2, String>, -s: String, +n: Nat, +w: Bool, +r0: String, v: {s == String.append(q, r0) : String}, +z: String, ez: {r0 == String.append(z, M.drop0(r0)) : String}, zs: {ModelName.sp_zeros(z) == True{} : Bool}, c: Bool, fp: mnn.FP(M.drop0(r0), n, w, c), b2: Bool, v2: mnn.NumsP(more, s, n, w, b2)) -> mnn.NumsP(q <> more, s, n, w, P.pm.or(c, u => b2)):
  match c:
    case True{}:
      (+d, (+r, (e, (sg, af)))) = fp
      +e1 = Equal.trans(String, r0, String.append(z, M.drop0(r0)), String.append(z, String.append(d, r)), ez, Equal.cong(String, String, y => String.append(z, y), M.drop0(r0), String.append(d, r), e))
      +e2 = Equal.trans(String, s, String.append(q, r0), String.append(q, String.append(z, String.append(d, r))), v, Equal.cong(String, String, y => String.append(q, y), r0, String.append(z, String.append(d, r)), e1))
      (Nil{}, (q, (more, (z, (d, (r, ({==}, (e2, (zs, (sg, af))))))))))
    case False{}:
      mnn.nums_next(q, more, s, n, w, b2, v2)

def mnn.nums_dp(+q: String, +more: List<&2, String>, -s: String, +n: Nat, +w: Bool, +r0: String, v: {s == String.append(q, r0) : String}, dp: mnn.DP(r0, M.drop0(r0)), b2: Bool, v2: mnn.NumsP(more, s, n, w, b2)) -> mnn.NumsP(q <> more, s, n, w, P.pm.or(M.num.first(M.drop0(r0), n, w), u => b2)):
  (+z, (ez, (zs, nzd))) = dp
  mnn.nums_hit(q, more, s, n, w, r0, v, z, ez, zs, M.num.first(M.drop0(r0), n, w), mnn.first_sp(M.drop0(r0), n, w, nzd), b2, v2)

def mnn.nums_some(+q: String, +more: List<&2, String>, -s: String, +n: Nat, +w: Bool, +r0: String, v: {s == String.append(q, r0) : String}, b2: Bool, v2: mnn.NumsP(more, s, n, w, b2)) -> mnn.NumsP(q <> more, s, n, w, P.pm.or(M.num.first(M.drop0(r0), n, w), u => b2)):
  mnn.nums_dp(q, more, s, n, w, r0, v, mnn.drop0_sp(r0), b2, v2)

def mnn.nums_at(+q: String, +more: List<&2, String>, -s: String, +n: Nat, +w: Bool, m: Maybe<&2, String>, v: LA.mnb.SP(q, s, m), b2: Bool, v2: mnn.NumsP(more, s, n, w, b2)) -> mnn.NumsP(q <> more, s, n, w, P.pm.or(M.num.on(m, n, w), u => b2)):
  match m:
    case None{}:
      mnn.nums_next(q, more, s, n, w, b2, v2)
    case Some{+r0}:
      mnn.nums_some(q, more, s, n, w, r0, v, b2, v2)

# a number found after one of ps: its split
def mnn.nums_sp(ps: List<&2, String>, +s: String, +n: Nat, +w: Bool) -> mnn.NumsP(ps, s, n, w, M.nums(ps, s, n, w)):
  match ps:
    case Nil{}:
      Unit{}
    case +q <> +more:
      mnn.nums_at(q, more, s, n, w, M.strip(q, s), LA.mnb.sp(q, s), M.nums(more, s, n, w), mnn.nums_sp(more, s, n, w))

# The run of digits, complete
# ---------------------------

def mnn.end_eq(w: Bool, +xc: U32, h: {ModelName.sp_ends(w, Chr{xc}) == True{} : Bool}) -> {M.num.end(w, Chr{xc}) == True{} : Bool}:
  match w:
    case True{}:
      h
    case False{}:
      {==}

def mnn.end_at(+w: Bool, +x: Char, -t: String, h: {ModelName.sp_after(w, SCon{x, t}) == True{} : Bool}) -> {M.ite(Tp.is_dig(x), u => M.num.rest(t, w), v => M.num.end(w, x)) == True{} : Bool}:
  match x:
    case Chr{+xc}:
      +hh = h
      %Equal.sym(Bool, Tp.is_dig(Chr{xc}), False{}, LA.mnb.not_t(Tp.is_dig(Chr{xc}), LA.mnb.and_l(Bool.not(Tp.is_dig(Chr{xc})), ModelName.sp_ends(w, Chr{xc}), hh))) : {M.ite(_, u => M.num.rest(t, w), v => M.num.end(w, Chr{xc})) == True{} : Bool}
      mnn.end_eq(w, xc, LA.mnb.and_r(Bool.not(Tp.is_dig(Chr{xc})), ModelName.sp_ends(w, Chr{xc}), hh))

def mnn.rest_end_app(+w: Bool, r: String, hr: {ModelName.sp_after(w, r) == True{} : Bool}) -> {M.num.rest(r, w) == True{} : Bool}:
  match r:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      mnn.end_at(w, x, t, hr)

# digits, then a rest that ends the run: num.rest accepts
def mnn.rest_app(d: String, +r: String, +w: Bool, hd: {ModelName.sp_digits(d) == True{} : Bool}, hr: {ModelName.sp_after(w, r) == True{} : Bool}) -> {M.num.rest(String.append(d, r), w) == True{} : Bool}:
  match d:
    case SNil{}:
      mnn.rest_end_app(w, r, hr)
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +hh = hd
          %Equal.sym(Bool, Tp.is_dig(Chr{xc}), True{}, LA.mnb.and_l(Tp.is_dig(Chr{xc}), ModelName.sp_digits(t), hh)) : {M.ite(_, u => M.num.rest(String.append(t, r), w), v => M.num.end(w, Chr{xc})) == True{} : Bool}
          mnn.rest_app(t, r, w, LA.mnb.and_r(Tp.is_dig(Chr{xc}), ModelName.sp_digits(t), hh), hr)

def mnn.sec_end_app(+ok: Bool, +w: Bool, r: String, ho: {ok == True{} : Bool}, hr: {ModelName.sp_after(w, r) == True{} : Bool}) -> {M.num.second(r, ok, w) == True{} : Bool}:
  match r:
    case SNil{}:
      ho
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +hh = hr
          %Equal.sym(Bool, Tp.is_dig(Chr{xc}), False{}, LA.mnb.not_t(Tp.is_dig(Chr{xc}), LA.mnb.and_l(Bool.not(Tp.is_dig(Chr{xc})), ModelName.sp_ends(w, Chr{xc}), hh))) : {M.ite(_, u => M.num.rest(t, w), v => Bool.and(ok, M.num.end(w, Chr{xc}))) == True{} : Bool}
          LA.mnb.and_t(ok, M.num.end(w, Chr{xc}), ho, mnn.end_eq(w, xc, LA.mnb.and_r(Bool.not(Tp.is_dig(Chr{xc})), ModelName.sp_ends(w, Chr{xc}), hh)))

# digits (none only when ok), then a rest that ends the run: num.second
# accepts
def mnn.sec_app(d: String, +ok: Bool, +r: String, +w: Bool, hd: {ModelName.sp_digits(d) == True{} : Bool}, ho: {Bool.or(Bool.not(String.is_empty(d)), ok) == True{} : Bool}, hr: {ModelName.sp_after(w, r) == True{} : Bool}) -> {M.num.second(String.append(d, r), ok, w) == True{} : Bool}:
  match d:
    case SNil{}:
      mnn.sec_end_app(ok, w, r, ho, hr)
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +hh = hd
          %Equal.sym(Bool, Tp.is_dig(Chr{xc}), True{}, LA.mnb.and_l(Tp.is_dig(Chr{xc}), ModelName.sp_digits(t), hh)) : {M.ite(_, u => M.num.rest(String.append(t, r), w), v => Bool.and(ok, M.num.end(w, Chr{xc}))) == True{} : Bool}
          mnn.rest_app(t, r, w, LA.mnb.and_r(Tp.is_dig(Chr{xc}), ModelName.sp_digits(t), hh), hr)

# a passing run, then a rest that ends it: num.first accepts
def mnn.first_app(d: String, +n: Nat, +r: String, +w: Bool, hd: {ModelName.sp_sig(d, n) == True{} : Bool}, hr: {ModelName.sp_after(w, r) == True{} : Bool}) -> {M.num.first(String.append(d, r), n, w) == True{} : Bool}:
  match d:
    case SNil{}:
      LA.mnb.absurd_f({M.num.first(String.append(SNil{}, r), n, w) == True{} : Bool}, hd)
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +hh = hd
          +a = Bool.and(Tp.is_dig(Chr{xc}), Bool.not(U32.is_eq(xc, 48)))
          +b = Bool.and(ModelName.sp_digits(t), Bool.or(Bool.not(String.is_empty(t)), Nat.is_le(n, M.digit(Chr{xc}))))
          +ha = LA.mnb.and_l(a, b, hh)
          +hb = LA.mnb.and_r(a, b, hh)
          %Equal.sym(Bool, Tp.is_dig(Chr{xc}), True{}, LA.mnb.and_l(Tp.is_dig(Chr{xc}), Bool.not(U32.is_eq(xc, 48)), ha)) : {M.ite(_, u => M.num.second(String.append(t, r), Nat.is_le(n, M.digit(Chr{xc})), w), v => False{}) == True{} : Bool}
          mnn.sec_app(t, Nat.is_le(n, M.digit(Chr{xc})), r, w, LA.mnb.and_l(ModelName.sp_digits(t), Bool.or(Bool.not(String.is_empty(t)), Nat.is_le(n, M.digit(Chr{xc}))), hb), LA.mnb.and_r(ModelName.sp_digits(t), Bool.or(Bool.not(String.is_empty(t)), Nat.is_le(n, M.digit(Chr{xc}))), hb), hr)

# a passing run opens with no `0`
def mnn.sig_nz(d: String, -r: String, -n: Nat, hd: {ModelName.sp_sig(d, n) == True{} : Bool}) -> {mnn.nz(String.append(d, r)) == True{} : Bool}:
  match d:
    case SNil{}:
      LA.mnb.absurd_f({mnn.nz(String.append(SNil{}, r)) == True{} : Bool}, hd)
    case SCon{+x, +t}:
      +hh = hd
      +a = Bool.and(ModelName.sp_digit(x), Bool.not(ModelName.sp_zero(x)))
      LA.mnb.and_r(ModelName.sp_digit(x), Bool.not(ModelName.sp_zero(x)), LA.mnb.and_l(a, Bool.and(ModelName.sp_digits(t), Bool.or(Bool.not(String.is_empty(t)), Nat.is_le(n, ModelName.sp_value(x)))), hh))

def mnn.nums_in(pre: List<&2, String>, +p: String, +post: List<&2, String>, +s: String, +n: Nat, +w: Bool, h: {M.num.on(M.strip(p, s), n, w) == True{} : Bool}) -> {M.nums(List.append(&2, String, pre, p <> post), s, n, w) == True{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, M.num.on(M.strip(p, s), n, w), True{}, h) : {P.pm.or(_, u => M.nums(post, s, n, w)) == True{} : Bool}
      {==}
    case +q <> more:
      LA.mnb.or_rl(M.num.on(M.strip(q, s), n, w), M.nums(List.append(&2, String, more, p <> post), s, n, w), mnn.nums_in(more, p, post, s, n, w, h))

# p, zeros, a passing run and a rest that ends it: num.on accepts
def mnn.on_app(+p: String, +z: String, +d: String, +r: String, +n: Nat, +w: Bool, hz: {ModelName.sp_zeros(z) == True{} : Bool}, hd: {ModelName.sp_sig(d, n) == True{} : Bool}, hr: {ModelName.sp_after(w, r) == True{} : Bool}) -> {M.num.on(M.strip(p, String.append(p, String.append(z, String.append(d, r)))), n, w) == True{} : Bool}:
  +hd2 = hd
  %Equal.sym(Maybe<&2, String>, M.strip(p, String.append(p, String.append(z, String.append(d, r)))), Some{String.append(z, String.append(d, r))}, LA.mnb.strip_app(p, String.append(z, String.append(d, r)))) : {M.num.on(_, n, w) == True{} : Bool}
  %Equal.sym(String, M.drop0(String.append(z, String.append(d, r))), String.append(d, r), mnn.drop0_app(z, String.append(d, r), hz, mnn.sig_nz(d, r, n, hd2))) : {M.num.first(_, n, w) == True{} : Bool}
  mnn.first_app(d, n, r, w, hd2, hr)
