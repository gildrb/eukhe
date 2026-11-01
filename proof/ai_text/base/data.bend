# eukhe: lemmas of the R3 proofs (data_url): the chunks are one pass over
# the text they make (aitr.chunks); a data URL runs the reading to the data
# state with its mime's length (aitr.data_run); and what the reading
# accepts from each state is the rest of a data URL (aitr.pre_s,
# aitr.mime_s, aitr.mark_s, aitr.data_s).

import Base
import ../../../bend/ai_text.bend as T
import ../../../laws/ai_text.bend as AiText
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../../model_name/base.bend as LA
import ./dig.bend as LD

# Nat
# ---

def aitr.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(k, 0n), k, aitr.add_zero(k))

def aitr.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+k:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(k, 1n+b), 1n+Nat.add(k, b), aitr.add_succ(k, b))

# One pass
# --------

def aitr.go_app(a: String, -b: String, st: T.Du) -> {T.du.go(String.append(a, b), st) == T.du.go(b, T.du.go(a, st)) : T.Du}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, t}:
      aitr.go_app(t, b, T.du.step(st, c))

# the chunks, in order, are one pass over the text they make
def aitr.chunks(cs: List<&2, String>, +st: T.Du) -> {T.du.chunks(cs, st) == T.du.go(AiText.sp_cat(cs), st) : T.Du}:
  match cs:
    case Nil{}:
      {==}
    case +c <> more:
      Equal.trans(T.Du, T.du.chunks(more, T.du.go(c, st)), T.du.go(AiText.sp_cat(more), T.du.go(c, st)), T.du.go(String.append(c, AiText.sp_cat(more)), st), aitr.chunks(more, T.du.go(c, st)), Equal.sym(T.Du, T.du.go(String.append(c, AiText.sp_cat(more)), st), T.du.go(AiText.sp_cat(more), T.du.go(c, st)), aitr.go_app(c, AiText.sp_cat(more), st)))

# a failed reading stays failed
def aitr.fail_go(s: String) -> {T.du.go(s, T.DFail{}) == T.DFail{} : T.Du}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      aitr.fail_go(t)

def aitr.fail_absurd(+s: String, -n: Nat, -G: Type, h: {T.du.verdict(T.du.go(s, T.DFail{})) == Some{n} : Maybe<&2, Nat>}) -> G:
  LD.aitd.none_some(Nat, n, G, Equal.trans(Maybe<&2, Nat>, None{}, T.du.verdict(T.du.go(s, T.DFail{})), Some{n}, Equal.cong(T.Du, Maybe<&2, Nat>, z => T.du.verdict(z), T.DFail{}, T.du.go(s, T.DFail{}), Equal.sym(T.Du, T.du.go(s, T.DFail{}), T.DFail{}, aitr.fail_go(s))), h))

# Complete
# --------

def aitr.data_c(b: Bool, -t: String, +k: Nat, -any: Bool, eb: {b == False{} : Bool}, ih: {T.du.go(t, T.DData{k, True{}}) == T.DData{k, True{}} : T.Du}) -> {T.du.go(t, T.du.data(b, k)) == T.DData{k, True{}} : T.Du}:
  match b:
    case True{}:
      LA.mnb.absurd({T.du.go(t, T.du.data(True{}, k)) == T.DData{k, True{}} : T.Du}, eb)
    case False{}:
      ih

# data with no line terminator keeps the data state
def aitr.nolt_run(d: String, +k: Nat, hd: {AiText.sp_no_lt(d) == True{} : Bool}) -> {T.du.go(d, T.DData{k, True{}}) == T.DData{k, True{}} : T.Du}:
  match d:
    case SNil{}:
      {==}
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +hh = hd
          aitr.data_c(T.is_lt(Chr{xc}), t, k, True{}, LA.mnb.not_t(T.is_lt(Chr{xc}), LA.mnb.and_l(Bool.not(T.is_lt(Chr{xc})), AiText.sp_no_lt(t), hh)), aitr.nolt_run(t, k, LA.mnb.and_r(Bool.not(T.is_lt(Chr{xc})), AiText.sp_no_lt(t), hh)))

# data of one or more chars, none a line terminator, ends in the data
# state with a data char read
def aitr.body_run(d: String, +k: Nat, any: Bool, hd: {AiText.sp_body(d) == True{} : Bool}) -> {T.du.go(d, T.DData{k, any}) == T.DData{k, True{}} : T.Du}:
  match d:
    case SNil{}:
      LA.mnb.absurd_f({T.du.go(SNil{}, T.DData{k, any}) == T.DData{k, True{}} : T.Du}, hd)
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +hh = hd
          aitr.data_c(T.is_lt(Chr{xc}), t, k, any, LA.mnb.not_t(T.is_lt(Chr{xc}), LA.mnb.and_l(Bool.not(T.is_lt(Chr{xc})), AiText.sp_no_lt(t), hh)), aitr.nolt_run(t, k, LA.mnb.and_r(Bool.not(T.is_lt(Chr{xc})), AiText.sp_no_lt(t), hh)))

def aitr.mime_c(b: Bool, -t: String, -y: String, +k: Nat, -G: T.Du, eb: {b == False{} : Bool}, ih: {T.du.go(String.append(t, y), T.DMime{1n+k}) == G : T.Du}) -> {T.du.go(String.append(t, y), T.du.mime(b, k)) == G : T.Du}:
  match b:
    case True{}:
      LA.mnb.absurd({T.du.go(String.append(t, y), T.du.mime(True{}, k)) == G : T.Du}, eb)
    case False{}:
      ih

# a mime with no `;` counts its chars
def aitr.mime_run(m: String, +y: String, +k: Nat, hm: {AiText.sp_no_semi(m) == True{} : Bool}) -> {T.du.go(String.append(m, y), T.DMime{k}) == T.du.go(y, T.DMime{Nat.add(k, String.length(m))}) : T.Du}:
  match m:
    case SNil{}:
      Equal.cong(Nat, T.Du, z => T.du.go(y, T.DMime{z}), k, Nat.add(k, 0n), Equal.sym(Nat, Nat.add(k, 0n), k, aitr.add_zero(k)))
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +hh = hm
          +lt = {String.length(t) : Nat}
          aitr.mime_c(U32.is_eq(xc, 59), t, y, k, T.du.go(y, T.DMime{Nat.add(k, 1n+lt)}), LA.mnb.not_t(U32.is_eq(xc, 59), LA.mnb.and_l(Bool.not(U32.is_eq(xc, 59)), AiText.sp_no_semi(t), hh)), Equal.trans(T.Du, T.du.go(String.append(t, y), T.DMime{1n+k}), T.du.go(y, T.DMime{1n+Nat.add(k, lt)}), T.du.go(y, T.DMime{Nat.add(k, 1n+lt)}), aitr.mime_run(t, y, 1n+k, LA.mnb.and_r(Bool.not(U32.is_eq(xc, 59)), AiText.sp_no_semi(t), hh)), Equal.cong(Nat, T.Du, z => T.du.go(y, T.DMime{z}), 1n+Nat.add(k, lt), Nat.add(k, 1n+lt), Equal.sym(Nat, Nat.add(k, 1n+lt), 1n+Nat.add(k, lt), aitr.add_succ(k, lt)))))

# a data URL runs to the data state, its mime's length counted
def aitr.data_run(m: String, +d: String, hm: {AiText.sp_mime(m) == True{} : Bool}, hd: {AiText.sp_body(d) == True{} : Bool}) -> {T.du.go(AiText.sp_data(m, d), T.DPre{"data:"}) == T.DData{String.length(m), True{}} : T.Du}:
  match m:
    case SNil{}:
      LA.mnb.absurd_f({T.du.go(AiText.sp_data(SNil{}, d), T.DPre{"data:"}) == T.DData{String.length(SNil{}), True{}} : T.Du}, hm)
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +hh = hm
          +y = String.append(";base64,", d)
          +n = {1n+String.length(t) : Nat}
          aitr.mime_c(U32.is_eq(xc, 59), t, y, 0n, T.DData{n, True{}}, LA.mnb.not_t(U32.is_eq(xc, 59), LA.mnb.and_l(Bool.not(U32.is_eq(xc, 59)), AiText.sp_no_semi(t), hh)), Equal.trans(T.Du, T.du.go(String.append(t, y), T.DMime{1n}), T.du.go(y, T.DMime{n}), T.DData{n, True{}}, aitr.mime_run(t, y, 1n, LA.mnb.and_r(Bool.not(U32.is_eq(xc, 59)), AiText.sp_no_semi(t), hh)), aitr.body_run(d, n, False{}, hd)))

# Sound
# -----

# from the data state: no line terminator, a data char read, the length
def aitr.DS(s: String, k: Nat, any: Bool, n: Nat) -> Type:
  {AiText.sp_no_lt(s) == True{} : Bool} & ({Bool.or(any, Bool.not(String.is_empty(s))) == True{} : Bool} & {k == n : Nat})

def aitr.data_fin(+xc: U32, -t: String, -k: Nat, any: Bool, -n: Nat, eb: {T.is_lt(Chr{xc}) == False{} : Bool}, ds: aitr.DS(t, k, True{}, n)) -> aitr.DS(SCon{Chr{xc}, t}, k, any, n):
  (nl, (o, ek)) = ds
  (LA.mnb.and_t(Bool.not(T.is_lt(Chr{xc})), AiText.sp_no_lt(t), LA.mnb.not_f(T.is_lt(Chr{xc}), eb), nl), (LA.mnb.or_rt(any, True{}, {==}), ek))

def aitr.data_sc(b: Bool, +xc: U32, +t: String, +k: Nat, any: Bool, -n: Nat, eb: {T.is_lt(Chr{xc}) == b : Bool}, h: {T.du.verdict(T.du.go(t, T.du.data(b, k))) == Some{n} : Maybe<&2, Nat>}, ih: {T.du.verdict(T.du.go(t, T.DData{k, True{}})) == Some{n} : Maybe<&2, Nat>} -> aitr.DS(t, k, True{}, n)) -> aitr.DS(SCon{Chr{xc}, t}, k, any, n):
  match b:
    case True{}:
      aitr.fail_absurd(t, n, aitr.DS(SCon{Chr{xc}, t}, k, any, n), h)
    case False{}:
      aitr.data_fin(xc, t, k, any, n, eb, ih(h))

def aitr.data_s(s: String, +k: Nat, any: Bool, -n: Nat, h: {T.du.verdict(T.du.go(s, T.DData{k, any})) == Some{n} : Maybe<&2, Nat>}) -> aitr.DS(s, k, any, n):
  match s:
    case SNil{}:
      match any:
        case True{}:
          ({==}, ({==}, LD.aitd.some_inj(Nat, k, n, h)))
        case False{}:
          LD.aitd.none_some(Nat, n, aitr.DS(SNil{}, k, False{}, n), h)
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          aitr.data_sc(T.is_lt(Chr{xc}), xc, t, k, any, n, {==}, h, e => aitr.data_s(t, k, True{}, n, e))

# one or more chars with no line terminator
def aitr.body_of(t: String, nl: {AiText.sp_no_lt(t) == True{} : Bool}, ne: {Bool.or(False{}, Bool.not(String.is_empty(t))) == True{} : Bool}) -> {AiText.sp_body(t) == True{} : Bool}:
  match t:
    case SNil{}:
      LA.mnb.absurd_f({AiText.sp_body(SNil{}) == True{} : Bool}, ne)
    case SCon{x, u}:
      nl

# from a mark state: the rest of the mark, then data
def aitr.KS(s: String, k: Nat, left: String, n: Nat) -> Type:
  Sigma<&1, &1, String, d => {s == String.append(left, d) : String} & ({AiText.sp_body(d) == True{} : Bool} & {k == n : Nat})>

def aitr.mark_end(+c: Char, +t: String, -k: Nat, +y: Char, -n: Nat, ey: {y == c : Char}, ds: aitr.DS(t, k, False{}, n)) -> aitr.KS(SCon{c, t}, k, SCon{y, SNil{}}, n):
  (nl, (ne, ek)) = ds
  (t, (Equal.cong(Char, String, z => SCon{z, t}, c, y, Equal.sym(Char, y, c, ey)), (aitr.body_of(t, nl, ne), ek)))

def aitr.mark_more(+c: Char, +t: String, -k: Nat, +y: Char, +l: String, -n: Nat, ey: {y == c : Char}, ks: aitr.KS(t, k, l, n)) -> aitr.KS(SCon{c, t}, k, SCon{y, l}, n):
  (+d, (e, (hd, ek))) = ks
  (d, (Equal.trans(String, SCon{c, t}, SCon{y, t}, SCon{y, String.append(l, d)}, Equal.cong(Char, String, z => SCon{z, t}, c, y, Equal.sym(Char, y, c, ey)), LA.mnb.cons_eq(y, t, String.append(l, d), e)), (hd, ek)))

def aitr.mark_c(b: Bool, +c: Char, +t: String, +k: Nat, +y: Char, lt: String, -n: Nat, eb: {Char.is_eq(y, c) == b : Bool}, h: {T.du.verdict(T.du.go(t, T.du.mark(b, k, lt))) == Some{n} : Maybe<&2, Nat>}, ih: @l: String -> {T.du.verdict(T.du.go(t, T.DMark{k, l})) == Some{n} : Maybe<&2, Nat>} -> aitr.KS(t, k, l, n)) -> aitr.KS(SCon{c, t}, k, SCon{y, lt}, n):
  match b:
    case True{}:
      match lt:
        case SNil{}:
          aitr.mark_end(c, t, k, y, n, LA.mnb.char_sound(y, c, eb), aitr.data_s(t, k, False{}, n, h))
        case SCon{+y2, +u}:
          aitr.mark_more(c, t, k, y, SCon{y2, u}, n, LA.mnb.char_sound(y, c, eb), ih(SCon{y2, u}, h))
    case False{}:
      aitr.fail_absurd(t, n, aitr.KS(SCon{c, t}, k, SCon{y, lt}, n), h)

def aitr.mark_s(s: String, +k: Nat, left: String, -n: Nat, h: {T.du.verdict(T.du.go(s, T.DMark{k, left})) == Some{n} : Maybe<&2, Nat>}) -> aitr.KS(s, k, left, n):
  match s:
    case SNil{}:
      LD.aitd.none_some(Nat, n, aitr.KS(SNil{}, k, left, n), h)
    case SCon{+c, +t}:
      match left:
        case SNil{}:
          aitr.fail_absurd(t, n, aitr.KS(SCon{c, t}, k, SNil{}, n), h)
        case SCon{+y, lt}:
          aitr.mark_c(Char.is_eq(y, c), c, t, k, y, lt, n, {==}, h, l => e => aitr.mark_s(t, k, l, n, e))

# the mime read from a mime state of length k: when k is 0 one or more
# chars, else zero or more, none `;`
def aitr.mime_at(k: Nat, m: String) -> Bool:
  match k:
    case 0n:
      AiText.sp_mime(m)
    case 1n+j:
      AiText.sp_no_semi(m)

# from a mime state: the rest of the mime, the mark, then data
def aitr.MS(s: String, k: Nat, n: Nat) -> Type:
  Sigma<&1, &1, String, m => Sigma<&1, &1, String, d => {s == String.append(m, String.append(";base64,", d)) : String} & ({aitr.mime_at(k, m) == True{} : Bool} & ({AiText.sp_body(d) == True{} : Bool} & {Nat.add(k, String.length(m)) == n : Nat}))>>

def aitr.mime_semi(+xc: U32, +t: String, +j: Nat, -n: Nat, eb: {U32.is_eq(xc, 59) == True{} : Bool}, ks: aitr.KS(t, 1n+j, "base64,", n)) -> aitr.MS(SCon{Chr{xc}, t}, 1n+j, n):
  (+d, (e, (hd, ek))) = ks
  (SNil{}, (d, (Equal.trans(String, SCon{Chr{xc}, t}, SCon{Chr{59}, t}, SCon{Chr{59}, String.append("base64,", d)}, Equal.cong(U32, String, v => SCon{Chr{v}, t}, xc, 59, PWireBoolExact.wr_eq_sound(xc, 59, eb)), LA.mnb.cons_eq(Chr{59}, t, String.append("base64,", d), e)), ({==}, (hd, Equal.trans(Nat, Nat.add(1n+j, 0n), 1n+j, n, aitr.add_zero(1n+j), ek))))))

def aitr.mime_at_cons(k: Nat, +xc: U32, -m: String, eb: {U32.is_eq(xc, 59) == False{} : Bool}, hm: {AiText.sp_no_semi(m) == True{} : Bool}) -> {aitr.mime_at(k, SCon{Chr{xc}, m}) == True{} : Bool}:
  match k:
    case 0n:
      LA.mnb.and_t(Bool.not(U32.is_eq(xc, 59)), AiText.sp_no_semi(m), LA.mnb.not_f(U32.is_eq(xc, 59), eb), hm)
    case 1n+j:
      LA.mnb.and_t(Bool.not(U32.is_eq(xc, 59)), AiText.sp_no_semi(m), LA.mnb.not_f(U32.is_eq(xc, 59), eb), hm)

def aitr.mime_next(+xc: U32, -t: String, +k: Nat, -n: Nat, eb: {U32.is_eq(xc, 59) == False{} : Bool}, ms: aitr.MS(t, 1n+k, n)) -> aitr.MS(SCon{Chr{xc}, t}, k, n):
  (+m, (+d, (e, (hm, (hd, hl))))) = ms
  (SCon{Chr{xc}, m}, (d, (LA.mnb.cons_eq(Chr{xc}, t, String.append(m, String.append(";base64,", d)), e), (aitr.mime_at_cons(k, xc, m, eb, hm), (hd, Equal.trans(Nat, Nat.add(k, 1n+String.length(m)), 1n+Nat.add(k, String.length(m)), n, aitr.add_succ(k, String.length(m)), hl))))))

def aitr.mime_sc(b: Bool, +xc: U32, +t: String, k: Nat, -n: Nat, eb: {U32.is_eq(xc, 59) == b : Bool}, h: {T.du.verdict(T.du.go(t, T.du.mime(b, k))) == Some{n} : Maybe<&2, Nat>}, ih: {T.du.verdict(T.du.go(t, T.DMime{1n+k})) == Some{n} : Maybe<&2, Nat>} -> aitr.MS(t, 1n+k, n)) -> aitr.MS(SCon{Chr{xc}, t}, k, n):
  match b:
    case True{}:
      match k:
        case 0n:
          aitr.fail_absurd(t, n, aitr.MS(SCon{Chr{xc}, t}, 0n, n), h)
        case 1n++j:
          aitr.mime_semi(xc, t, j, n, eb, aitr.mark_s(t, 1n+j, "base64,", n, h))
    case False{}:
      aitr.mime_next(xc, t, k, n, eb, ih(h))

def aitr.mime_s(s: String, +k: Nat, -n: Nat, h: {T.du.verdict(T.du.go(s, T.DMime{k})) == Some{n} : Maybe<&2, Nat>}) -> aitr.MS(s, k, n):
  match s:
    case SNil{}:
      LD.aitd.none_some(Nat, n, aitr.MS(SNil{}, k, n), h)
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          aitr.mime_sc(U32.is_eq(xc, 59), xc, t, k, n, {==}, h, e => aitr.mime_s(t, 1n+k, n, e))

# from a prefix state: the rest of the prefix, then a mime state of 0
def aitr.PS(s: String, left: String, n: Nat) -> Type:
  Sigma<&1, &1, String, r => {s == String.append(left, r) : String} & {T.du.verdict(T.du.go(r, T.DMime{0n})) == Some{n} : Maybe<&2, Nat>}>

def aitr.pre_more(+c: Char, +t: String, +y: Char, +l: String, -n: Nat, ey: {y == c : Char}, ps: aitr.PS(t, l, n)) -> aitr.PS(SCon{c, t}, SCon{y, l}, n):
  (+r, (e, hr)) = ps
  (r, (Equal.trans(String, SCon{c, t}, SCon{y, t}, SCon{y, String.append(l, r)}, Equal.cong(Char, String, z => SCon{z, t}, c, y, Equal.sym(Char, y, c, ey)), LA.mnb.cons_eq(y, t, String.append(l, r), e)), hr))

def aitr.pre_c(b: Bool, +c: Char, +t: String, +y: Char, lt: String, -n: Nat, eb: {Char.is_eq(y, c) == b : Bool}, h: {T.du.verdict(T.du.go(t, T.du.pre(b, lt))) == Some{n} : Maybe<&2, Nat>}, ih: @l: String -> {T.du.verdict(T.du.go(t, T.DPre{l})) == Some{n} : Maybe<&2, Nat>} -> aitr.PS(t, l, n)) -> aitr.PS(SCon{c, t}, SCon{y, lt}, n):
  match b:
    case True{}:
      match lt:
        case SNil{}:
          (t, (Equal.cong(Char, String, z => SCon{z, t}, c, y, Equal.sym(Char, y, c, LA.mnb.char_sound(y, c, eb))), h))
        case SCon{+y2, +u}:
          aitr.pre_more(c, t, y, SCon{y2, u}, n, LA.mnb.char_sound(y, c, eb), ih(SCon{y2, u}, h))
    case False{}:
      aitr.fail_absurd(t, n, aitr.PS(SCon{c, t}, SCon{y, lt}, n), h)

def aitr.pre_s(s: String, left: String, -n: Nat, h: {T.du.verdict(T.du.go(s, T.DPre{left})) == Some{n} : Maybe<&2, Nat>}) -> aitr.PS(s, left, n):
  match s:
    case SNil{}:
      LD.aitd.none_some(Nat, n, aitr.PS(SNil{}, left, n), h)
    case SCon{+c, +t}:
      match left:
        case SNil{}:
          aitr.fail_absurd(t, n, aitr.PS(SCon{c, t}, SNil{}, n), h)
        case SCon{+y, lt}:
          aitr.pre_c(Char.is_eq(y, c), c, t, y, lt, n, {==}, h, l => e => aitr.pre_s(t, l, n, e))

def aitr.SG(s: String, n: Nat) -> Type:
  Sigma<&1, &1, String, m => Sigma<&1, &1, String, d => {s == AiText.sp_data(m, d) : String} & ({AiText.sp_mime(m) == True{} : Bool} & ({AiText.sp_body(d) == True{} : Bool} & {String.length(m) == n : Nat}))>>

def aitr.sound_ms(-s: String, -r: String, -n: Nat, e: {s == String.append("data:", r) : String}, ms: aitr.MS(r, 0n, n)) -> aitr.SG(s, n):
  (+m, (+d, (er, (hm, (hd, hl))))) = ms
  (m, (d, (Equal.trans(String, s, String.append("data:", r), String.append("data:", String.append(m, String.append(";base64,", d))), e, Equal.cong(String, String, z => String.append("data:", z), r, String.append(m, String.append(";base64,", d)), er)), (hm, (hd, hl)))))

def aitr.sound_ps(-s: String, -n: Nat, ps: aitr.PS(s, "data:", n)) -> aitr.SG(s, n):
  (+r, (e, hr)) = ps
  aitr.sound_ms(s, r, n, e, aitr.mime_s(r, 0n, n, hr))

# a text the reading accepts from the start is a data URL
def aitr.sound(+s: String, -n: Nat, h: {T.du.verdict(T.du.go(s, T.DPre{"data:"})) == Some{n} : Maybe<&2, Nat>}) -> aitr.SG(s, n):
  aitr.sound_ps(s, n, aitr.pre_s(s, "data:", n, h))
