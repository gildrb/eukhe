# eukhe: lemmas of the proofs of area redirect_input: logic, chars, the
# list facts of append and reverse, and what the model's cleaning, cutting
# and decoding do to texts of known chars (rt.*).

import Base
import ../../../bend/redirect_input.bend as Ri
import ../../../bend/gateway_answer.bend as Ga
import ../../../laws/redirect_input.bend as RedirectInput

# Logic
# -----

def rt.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def rt.absurd(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : rt.BD(_, Unit, G)
  Unit{}

def rt.absurdF(-G: Type, e: {False{} == True{} : Bool}) -> G:
  rt.absurd(G, Equal.sym(Bool, False{}, True{}, e))

def rt.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def rt.and_r(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      rt.absurdF({b == True{} : Bool}, e)

def rt.and_t(+a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def rt.or_fl(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      {==}

def rt.or_fr(a: Bool, b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      rt.absurd({b == False{} : Bool}, e)
    case False{}:
      e

def rt.not_t(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      rt.absurdF({True{} == False{} : Bool}, e)
    case False{}:
      {==}

def rt.not_f(b: Bool, e: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case True{}:
      rt.absurd({Bool.not(True{}) == True{} : Bool}, e)
    case False{}:
      {==}

def rt.MI(m: Maybe<&2, Ri.Cut>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

# Strings
# -------

def rt.app_nil(s: String) -> {String.append(s, SNil{}) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Equal.cong(String, String, z => SCon{c, z}, String.append(t, SNil{}), t, rt.app_nil(t))

def rt.app_assoc(a: String, +b: String, +c: String) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      Equal.cong(String, String, z => SCon{x, z}, String.append(String.append(t, b), c), String.append(t, String.append(b, c)), rt.app_assoc(t, b, c))

# reverse.go keeps what is after its accumulator
def rt.rev_go(s: String, +a: String, +b: String) -> {String.reverse.go(s, String.append(a, b)) == String.append(String.reverse.go(s, a), b) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      rt.rev_go(t, SCon{h, a}, b)

def rt.rev_acc(+s: String, +a: String) -> {String.reverse.go(s, a) == String.append(String.reverse(s), a) : String}:
  rt.rev_go(s, SNil{}, a)

def rt.rev_snoc(s: String, +w: Char, +a: String) -> {String.reverse.go(String.append(s, SCon{w, SNil{}}), a) == SCon{w, String.reverse.go(s, a)} : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      rt.rev_snoc(t, w, SCon{h, a})

def rt.rev_rev(s: String) -> {String.reverse(String.reverse(s)) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(String, String.reverse.go(t, SCon{h, SNil{}}), String.append(String.reverse(t), SCon{h, SNil{}}), rt.rev_acc(t, SCon{h, SNil{}})) : {String.reverse(_) == SCon{h, t} : String}
      %Equal.sym(String, String.reverse.go(String.append(String.reverse(t), SCon{h, SNil{}}), SNil{}), SCon{h, String.reverse(String.reverse(t))}, rt.rev_snoc(String.reverse(t), h, SNil{})) : {_ == SCon{h, t} : String}
      Equal.cong(String, String, z => SCon{h, z}, String.reverse(String.reverse(t)), t, rt.rev_rev(t))

# the reverse of a then b is the reverse of b then that of a
def rt.rev_app(a: String, +b: String, +acc: String) -> {String.reverse.go(String.append(a, b), acc) == String.reverse.go(b, String.reverse.go(a, acc)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      rt.rev_app(t, b, SCon{h, acc})

# Chars of a text
# ---------------

# no char of s is dropped or trimmed: none is noise or a wrapping char
def rt.calm(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, t}:
      Bool.and(Bool.not(Bool.or(RedirectInput.ri_noise(c), RedirectInput.ri_wrapper(c))), rt.calm(t))

def rt.calm_app(a: String, +b: String, ha: {rt.calm(a) == True{} : Bool}, hb: {rt.calm(b) == True{} : Bool}) -> {rt.calm(String.append(a, b)) == True{} : Bool}:
  match a:
    case SNil{}:
      hb
    case SCon{+c, +t}:
      +h0 = ha
      rt.and_t(Bool.not(Bool.or(RedirectInput.ri_noise(c), RedirectInput.ri_wrapper(c))), rt.calm(String.append(t, b)), rt.and_l(Bool.not(Bool.or(RedirectInput.ri_noise(c), RedirectInput.ri_wrapper(c))), rt.calm(t), h0), rt.calm_app(t, b, rt.and_r(Bool.not(Bool.or(RedirectInput.ri_noise(c), RedirectInput.ri_wrapper(c))), rt.calm(t), h0), hb))

# a plain char is no noise, no wrapping char, none of the marks
def rt.pc_rest(+c: Char, h: {RedirectInput.ri_plain_char(c) == True{} : Bool}) -> {Bool.or(RedirectInput.ri_noise(c), Bool.or(RedirectInput.ri_wrapper(c), RedirectInput.ri_in(Char.to_u32(c), RedirectInput.ri_marks()))) == False{} : Bool}:
  rt.not_t(Bool.or(RedirectInput.ri_noise(c), Bool.or(RedirectInput.ri_wrapper(c), RedirectInput.ri_in(Char.to_u32(c), RedirectInput.ri_marks()))), h)

def rt.pc_noise(+c: Char, h: {RedirectInput.ri_plain_char(c) == True{} : Bool}) -> {RedirectInput.ri_noise(c) == False{} : Bool}:
  rt.or_fl(RedirectInput.ri_noise(c), Bool.or(RedirectInput.ri_wrapper(c), RedirectInput.ri_in(Char.to_u32(c), RedirectInput.ri_marks())), rt.pc_rest(c, h))

def rt.pc_wnm(+c: Char, h: {RedirectInput.ri_plain_char(c) == True{} : Bool}) -> {Bool.or(RedirectInput.ri_wrapper(c), RedirectInput.ri_in(Char.to_u32(c), RedirectInput.ri_marks())) == False{} : Bool}:
  rt.or_fr(RedirectInput.ri_noise(c), Bool.or(RedirectInput.ri_wrapper(c), RedirectInput.ri_in(Char.to_u32(c), RedirectInput.ri_marks())), rt.pc_rest(c, h))

def rt.pc_wrap(+c: Char, h: {RedirectInput.ri_plain_char(c) == True{} : Bool}) -> {RedirectInput.ri_wrapper(c) == False{} : Bool}:
  rt.or_fl(RedirectInput.ri_wrapper(c), RedirectInput.ri_in(Char.to_u32(c), RedirectInput.ri_marks()), rt.pc_wnm(c, h))

def rt.pc_marks(+c: Char, h: {RedirectInput.ri_plain_char(c) == True{} : Bool}) -> {RedirectInput.ri_in(Char.to_u32(c), RedirectInput.ri_marks()) == False{} : Bool}:
  rt.or_fr(RedirectInput.ri_wrapper(c), RedirectInput.ri_in(Char.to_u32(c), RedirectInput.ri_marks()), rt.pc_wnm(c, h))

# the marks, one by one: % + & = # ? /
def rt.pm(+c: Char, h: {RedirectInput.ri_plain_char(c) == True{} : Bool}) -> {Char.is_eq(c, '%') == False{} : Bool} & ({Char.is_eq(c, '+') == False{} : Bool} & ({Char.is_eq(c, '&') == False{} : Bool} & ({Char.is_eq(c, '=') == False{} : Bool} & ({Char.is_eq(c, '#') == False{} : Bool} & ({Char.is_eq(c, '?') == False{} : Bool} & {Char.is_eq(c, '/') == False{} : Bool}))))):
  match c:
    case Chr{+x}:
      +m0 = rt.pc_marks(Chr{x}, h)
      +m1 = rt.or_fr(U32.is_eq(x, 37), RedirectInput.ri_in(x, [43, 38, 61, 35, 63, 47]), m0)
      +m2 = rt.or_fr(U32.is_eq(x, 43), RedirectInput.ri_in(x, [38, 61, 35, 63, 47]), m1)
      +m3 = rt.or_fr(U32.is_eq(x, 38), RedirectInput.ri_in(x, [61, 35, 63, 47]), m2)
      +m4 = rt.or_fr(U32.is_eq(x, 61), RedirectInput.ri_in(x, [35, 63, 47]), m3)
      +m5 = rt.or_fr(U32.is_eq(x, 35), RedirectInput.ri_in(x, [63, 47]), m4)
      +m6 = rt.or_fr(U32.is_eq(x, 63), RedirectInput.ri_in(x, [47]), m5)
      (rt.or_fl(U32.is_eq(x, 37), RedirectInput.ri_in(x, [43, 38, 61, 35, 63, 47]), m0),
       (rt.or_fl(U32.is_eq(x, 43), RedirectInput.ri_in(x, [38, 61, 35, 63, 47]), m1),
        (rt.or_fl(U32.is_eq(x, 38), RedirectInput.ri_in(x, [61, 35, 63, 47]), m2),
         (rt.or_fl(U32.is_eq(x, 61), RedirectInput.ri_in(x, [35, 63, 47]), m3),
          (rt.or_fl(U32.is_eq(x, 35), RedirectInput.ri_in(x, [63, 47]), m4),
           (rt.or_fl(U32.is_eq(x, 63), RedirectInput.ri_in(x, [47]), m5),
            rt.or_fl(U32.is_eq(x, 47), False{}, m6)))))))

# a plain char is calm
def rt.pc_calm(+c: Char, h: {RedirectInput.ri_plain_char(c) == True{} : Bool}) -> {Bool.not(Bool.or(RedirectInput.ri_noise(c), RedirectInput.ri_wrapper(c))) == True{} : Bool}:
  +hh = h
  %Equal.sym(Bool, RedirectInput.ri_noise(c), False{}, rt.pc_noise(c, hh)) : {Bool.not(Bool.or(_, RedirectInput.ri_wrapper(c))) == True{} : Bool}
  %Equal.sym(Bool, RedirectInput.ri_wrapper(c), False{}, rt.pc_wrap(c, hh)) : {Bool.not(Bool.or(False{}, _)) == True{} : Bool}
  {==}

# a plain text is calm
def rt.plain_calm(s: String, h: {RedirectInput.ri_plain(s) == True{} : Bool}) -> {rt.calm(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +h0 = h
      rt.and_t(Bool.not(Bool.or(RedirectInput.ri_noise(c), RedirectInput.ri_wrapper(c))), rt.calm(t), rt.pc_calm(c, rt.and_l(RedirectInput.ri_plain_char(c), RedirectInput.ri_plain(t), h0)), rt.plain_calm(t, rt.and_r(RedirectInput.ri_plain_char(c), RedirectInput.ri_plain(t), h0)))

# slashes are calm
def rt.slash_calm(n: Nat) -> {rt.calm(RedirectInput.ri_slashes(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      rt.slash_calm(m)

# s holds no char c with Char.is_eq(c, k)
def rt.lacks(s: String, +k: Char) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(Bool.not(Char.is_eq(c, k)), rt.lacks(t, k))

def rt.lacks_app(a: String, +b: String, +k: Char, ha: {rt.lacks(a, k) == True{} : Bool}, hb: {rt.lacks(b, k) == True{} : Bool}) -> {rt.lacks(String.append(a, b), k) == True{} : Bool}:
  match a:
    case SNil{}:
      hb
    case SCon{+c, +t}:
      +h0 = ha
      rt.and_t(Bool.not(Char.is_eq(c, k)), rt.lacks(String.append(t, b), k), rt.and_l(Bool.not(Char.is_eq(c, k)), rt.lacks(t, k), h0), rt.lacks_app(t, b, k, rt.and_r(Bool.not(Char.is_eq(c, k)), rt.lacks(t, k), h0), hb))

# the laws' lacks by code is lacks by char
def rt.lacks_code(s: String, +x: U32, h: {RedirectInput.ri_lacks(s, x) == True{} : Bool}) -> {rt.lacks(s, Chr{x}) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      match c:
        case Chr{+y}:
          +h0 = h
          rt.and_t(Bool.not(U32.is_eq(y, x)), rt.lacks(t, Chr{x}), rt.and_l(Bool.not(U32.is_eq(y, x)), RedirectInput.ri_lacks(t, x), h0), rt.lacks_code(t, x, rt.and_r(Bool.not(U32.is_eq(y, x)), RedirectInput.ri_lacks(t, x), h0)))

# the marks by number: % + & = # ? /
def rt.mark(n: Nat) -> Char:
  match n:
    case 0n:
      '%'
    case 1n:
      '+'
    case 2n:
      '&'
    case 3n:
      '='
    case 4n:
      '#'
    case 5n:
      '?'
    case 6n+p:
      '/'

def rt.pm_sel(n: Nat, -c: Char, t: {Char.is_eq(c, '%') == False{} : Bool} & ({Char.is_eq(c, '+') == False{} : Bool} & ({Char.is_eq(c, '&') == False{} : Bool} & ({Char.is_eq(c, '=') == False{} : Bool} & ({Char.is_eq(c, '#') == False{} : Bool} & ({Char.is_eq(c, '?') == False{} : Bool} & {Char.is_eq(c, '/') == False{} : Bool})))))) -> {Char.is_eq(c, rt.mark(n)) == False{} : Bool}:
  match n:
    case 0n:
      (t0, r0) = t
      t0
    case 1n:
      (t0, r0) = t
      (t1, r1) = r0
      t1
    case 2n:
      (t0, r0) = t
      (t1, r1) = r0
      (t2, r2) = r1
      t2
    case 3n:
      (t0, r0) = t
      (t1, r1) = r0
      (t2, r2) = r1
      (t3, r3) = r2
      t3
    case 4n:
      (t0, r0) = t
      (t1, r1) = r0
      (t2, r2) = r1
      (t3, r3) = r2
      (t4, r4) = r3
      t4
    case 5n:
      (t0, r0) = t
      (t1, r1) = r0
      (t2, r2) = r1
      (t3, r3) = r2
      (t4, r4) = r3
      (t5, t6) = r4
      t5
    case 6n+p:
      (t0, r0) = t
      (t1, r1) = r0
      (t2, r2) = r1
      (t3, r3) = r2
      (t4, r4) = r3
      (t5, t6) = r4
      t6

# a plain char is none of the marks
def rt.pc_mark(n: Nat, +c: Char, h: {RedirectInput.ri_plain_char(c) == True{} : Bool}) -> {Char.is_eq(c, rt.mark(n)) == False{} : Bool}:
  rt.pm_sel(n, c, rt.pm(c, h))

# a plain text lacks every mark
def rt.plain_lacks(s: String, +n: Nat, h: {RedirectInput.ri_plain(s) == True{} : Bool}) -> {rt.lacks(s, rt.mark(n)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +h0 = h
      rt.and_t(Bool.not(Char.is_eq(c, rt.mark(n))), rt.lacks(t, rt.mark(n)), rt.not_f(Char.is_eq(c, rt.mark(n)), rt.pc_mark(n, c, rt.and_l(RedirectInput.ri_plain_char(c), RedirectInput.ri_plain(t), h0))), rt.plain_lacks(t, n, rt.and_r(RedirectInput.ri_plain_char(c), RedirectInput.ri_plain(t), h0)))

# Cleaning
# --------

def rt.calm_head(+c: Char, -t: String, h: {rt.calm(SCon{c, t}) == True{} : Bool}) -> {Bool.or(RedirectInput.ri_noise(c), RedirectInput.ri_wrapper(c)) == False{} : Bool}:
  rt.not_t(Bool.or(RedirectInput.ri_noise(c), RedirectInput.ri_wrapper(c)), rt.and_l(Bool.not(Bool.or(RedirectInput.ri_noise(c), RedirectInput.ri_wrapper(c))), rt.calm(t), h))

def rt.calm_tail(+c: Char, t: String, h: {rt.calm(SCon{c, t}) == True{} : Bool}) -> {rt.calm(t) == True{} : Bool}:
  rt.and_r(Bool.not(Bool.or(RedirectInput.ri_noise(c), RedirectInput.ri_wrapper(c))), rt.calm(t), h)

def rt.calm_nn(+c: Char, -t: String, h: {rt.calm(SCon{c, t}) == True{} : Bool}) -> {RedirectInput.ri_noise(c) == False{} : Bool}:
  rt.or_fl(RedirectInput.ri_noise(c), RedirectInput.ri_wrapper(c), rt.calm_head(c, t, h))

def rt.calm_nw(+c: Char, -t: String, h: {rt.calm(SCon{c, t}) == True{} : Bool}) -> {RedirectInput.ri_wrapper(c) == False{} : Bool}:
  rt.or_fr(RedirectInput.ri_noise(c), RedirectInput.ri_wrapper(c), rt.calm_head(c, t, h))

# a noise char anywhere is dropped
def rt.compact_drop(a: String, +x: Char, +b: String, n: {RedirectInput.ri_noise(x) == True{} : Bool}) -> {Ri.compact(String.append(a, SCon{x, b})) == Ri.compact(String.append(a, b)) : String}:
  match a:
    case SNil{}:
      %Equal.sym(Bool, RedirectInput.ri_noise(x), True{}, n) : {Ri.compact.at(_, x, Ri.compact(b)) == Ri.compact(b) : String}
      {==}
    case SCon{+c, +t}:
      Equal.cong(String, String, z => Ri.compact.at(Bool.or(Ga.space(c), Ri.zero_width(c)), c, z), Ri.compact(String.append(t, SCon{x, b})), Ri.compact(String.append(t, b)), rt.compact_drop(t, x, b, n))

# a char that is no noise is kept
def rt.compact_keep(+w: Char, +s: String, nn: {RedirectInput.ri_noise(w) == False{} : Bool}) -> {Ri.compact(SCon{w, s}) == SCon{w, Ri.compact(s)} : String}:
  %Equal.sym(Bool, RedirectInput.ri_noise(w), False{}, nn) : {Ri.compact.at(_, w, Ri.compact(s)) == SCon{w, Ri.compact(s)} : String}
  {==}

def rt.cat_at(g: Bool, +c: Char, +r: String, +q: String) -> {Ri.compact.at(g, c, String.append(r, q)) == String.append(Ri.compact.at(g, c, r), q) : String}:
  match g:
    case True{}:
      {==}
    case False{}:
      {==}

def rt.compact_app(a: String, +b: String) -> {Ri.compact(String.append(a, b)) == String.append(Ri.compact(a), Ri.compact(b)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Ri.compact(String.append(t, b)), String.append(Ri.compact(t), Ri.compact(b)), rt.compact_app(t, b)) : {Ri.compact.at(Bool.or(Ga.space(c), Ri.zero_width(c)), c, _) == String.append(Ri.compact.at(Bool.or(Ga.space(c), Ri.zero_width(c)), c, Ri.compact(t)), Ri.compact(b)) : String}
      rt.cat_at(Bool.or(Ga.space(c), Ri.zero_width(c)), c, Ri.compact(t), Ri.compact(b))

# a calm text is kept whole
def rt.compact_calm(s: String, h: {rt.calm(s) == True{} : Bool}) -> {Ri.compact(s) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +h0 = h
      Equal.trans(String, Ri.compact(SCon{c, t}), SCon{c, Ri.compact(t)}, SCon{c, t}, rt.compact_keep(c, t, rt.calm_nn(c, t, h0)), Equal.cong(String, String, z => SCon{c, z}, Ri.compact(t), t, rt.compact_calm(t, rt.calm_tail(c, t, h0))))

def rt.uw_at(b: Bool, +c: Char, +r: String, +y: String, ih: {Ri.unwrap(String.append(r, y)) == String.append(Ri.unwrap(r), y) : String}) -> {Ri.unwrap.at(b, c, String.append(r, y), Ri.unwrap(String.append(r, y))) == String.append(Ri.unwrap.at(b, c, r, Ri.unwrap(r)), y) : String}:
  match b:
    case True{}:
      ih
    case False{}:
      {==}

# leading wrappers of x then a text that starts with no wrapper
def rt.unwrap_app(x: String, +z: Char, +t: String, nz: {RedirectInput.ri_wrapper(z) == False{} : Bool}) -> {Ri.unwrap(String.append(x, SCon{z, t})) == String.append(Ri.unwrap(x), SCon{z, t}) : String}:
  match x:
    case SNil{}:
      %Equal.sym(Bool, RedirectInput.ri_wrapper(z), False{}, nz) : {Ri.unwrap.at(_, z, t, Ri.unwrap(t)) == SCon{z, t} : String}
      {==}
    case SCon{+c, +r}:
      rt.uw_at(Ri.wrapper(c), c, r, SCon{z, t}, rt.unwrap_app(r, z, t, nz))

# a calm text starts with no wrapper
def rt.unwrap_head(r: String, +y: String, h: {rt.calm(r) == True{} : Bool}, ne: {String.is_empty(r) == False{} : Bool}) -> {Ri.unwrap(String.append(r, y)) == String.append(r, y) : String}:
  match r:
    case SNil{}:
      rt.absurd({Ri.unwrap(y) == y : String}, ne)
    case SCon{+q, +qs}:
      %Equal.sym(Bool, RedirectInput.ri_wrapper(q), False{}, rt.calm_nw(q, qs, h)) : {Ri.unwrap.at(_, q, String.append(qs, y), Ri.unwrap(String.append(qs, y))) == SCon{q, String.append(qs, y)} : String}
      {==}

def rt.calm_rev(s: String, +acc: String, ha: {rt.calm(acc) == True{} : Bool}, h: {rt.calm(s) == True{} : Bool}) -> {rt.calm(String.reverse.go(s, acc)) == True{} : Bool}:
  match s:
    case SNil{}:
      ha
    case SCon{+c, +t}:
      +h0 = h
      rt.calm_rev(t, SCon{c, acc}, rt.and_t(Bool.not(Bool.or(RedirectInput.ri_noise(c), RedirectInput.ri_wrapper(c))), rt.calm(acc), rt.and_l(Bool.not(Bool.or(RedirectInput.ri_noise(c), RedirectInput.ri_wrapper(c))), rt.calm(t), h0), ha), rt.calm_tail(c, t, h0))

def rt.ne_app(x: String, +z: Char, -t: String) -> {String.is_empty(String.append(x, SCon{z, t})) == False{} : Bool}:
  match x:
    case SNil{}:
      {==}
    case SCon{c, r}:
      {==}

# the reverse of a text with a char is no empty text
def rt.rev_ne(+z: Char, +t: String) -> {String.is_empty(String.reverse(SCon{z, t})) == False{} : Bool}:
  %Equal.sym(String, String.reverse.go(t, SCon{z, SNil{}}), String.append(String.reverse(t), SCon{z, SNil{}}), rt.rev_acc(t, SCon{z, SNil{}})) : {String.is_empty(_) == False{} : Bool}
  rt.ne_app(String.reverse(t), z, SNil{})

# a paste b then a calm text: cleaning trims and drops in b only
def rt.clean_tail(+b: String, +z: Char, +t: String, hc: {rt.calm(SCon{z, t}) == True{} : Bool}) -> {Ri.clean(String.append(b, SCon{z, t})) == String.append(Ri.unwrap(Ri.compact(b)), SCon{z, t}) : String}:
  +h0 = hc
  +T = {SCon{z, t} : String}
  +Y = Ri.unwrap(Ri.compact(b))
  +e1 = Equal.trans(String, Ri.compact(String.append(b, T)), String.append(Ri.compact(b), Ri.compact(T)), String.append(Ri.compact(b), T), rt.compact_app(b, T), Equal.cong(String, String, x => String.append(Ri.compact(b), x), Ri.compact(T), T, rt.compact_calm(T, h0)))
  +e2 = Equal.trans(String, Ri.unwrap(Ri.compact(String.append(b, T))), Ri.unwrap(String.append(Ri.compact(b), T)), String.append(Y, T), Equal.cong(String, String, x => Ri.unwrap(x), Ri.compact(String.append(b, T)), String.append(Ri.compact(b), T), e1), rt.unwrap_app(Ri.compact(b), z, t, rt.calm_nw(z, t, h0)))
  %Equal.sym(String, Ri.unwrap(Ri.compact(String.append(b, T))), String.append(Y, T), e2) : {String.reverse(Ri.unwrap(String.reverse(_))) == String.append(Y, T) : String}
  %Equal.sym(String, String.reverse.go(String.append(Y, T), SNil{}), String.reverse.go(T, String.reverse(Y)), rt.rev_app(Y, T, SNil{})) : {String.reverse(Ri.unwrap(_)) == String.append(Y, T) : String}
  %Equal.sym(String, String.reverse.go(T, String.reverse(Y)), String.append(String.reverse(T), String.reverse(Y)), rt.rev_acc(T, String.reverse(Y))) : {String.reverse(Ri.unwrap(_)) == String.append(Y, T) : String}
  %Equal.sym(String, Ri.unwrap(String.append(String.reverse(T), String.reverse(Y))), String.append(String.reverse(T), String.reverse(Y)), rt.unwrap_head(String.reverse(T), String.reverse(Y), rt.calm_rev(T, SNil{}, {==}, h0), rt.rev_ne(z, t))) : {String.reverse(_) == String.append(Y, T) : String}
  %Equal.sym(String, String.reverse.go(String.append(String.reverse(T), String.reverse(Y)), SNil{}), String.reverse.go(String.reverse(Y), String.reverse(String.reverse(T))), rt.rev_app(String.reverse(T), String.reverse(Y), SNil{})) : {_ == String.append(Y, T) : String}
  %Equal.sym(String, String.reverse(String.reverse(T)), T, rt.rev_rev(T)) : {String.reverse.go(String.reverse(Y), _) == String.append(Y, T) : String}
  %Equal.sym(String, String.reverse.go(String.reverse(Y), T), String.append(String.reverse(String.reverse(Y)), T), rt.rev_acc(String.reverse(Y), T)) : {_ == String.append(Y, T) : String}
  %Equal.sym(String, String.reverse(String.reverse(Y)), Y, rt.rev_rev(Y)) : {String.append(_, T) == String.append(Y, T) : String}
  {==}
