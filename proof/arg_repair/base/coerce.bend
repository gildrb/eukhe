# eukhe: lemmas of the R7 proofs of area arg_repair (laws/arg_repair/coerce.bend):
# the spec's White_Space is the code's (ac.white); `str::trim` of a text
# with White_Space only around a bare text, or of a text with none, is
# that text (ac.trim, ac.trim_self, ac.trim_clean: reversal lemmas
# ac.rev_*); the code's ASCII lower case and words are the spec's
# (ac.lower, ac.word); digits, zeros and the sign as the integer reading
# sees them (ac.dig_*, ac.digits_*, ac.canon_*).

import Base
import ../../../bend/arg_repair.bend as Ar
import ../../../laws/arg_repair/coerce.bend as ArgRepairCoerce
import ../base.bend as AB

# Logic
# -----

def ac.or_false(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ac.not_t(a: Bool, h: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      AB.ab.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def ac.and2(a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      AB.ab.absurd({Bool.and(False{}, b) == True{} : Bool}, ha)

# White_Space
# -----------

# the spec's White_Space (PropList.txt) is the code's
def ac.white(c: Char) -> {ArgRepairCoerce.sp_white(c) == Ar.ws(c) : Bool}:
  match c:
    case Chr{+x}:
      Equal.cong(Bool, Bool, z => Bool.or(Bool.and(U32.is_ge(x, 9), U32.is_le(x, 13)), Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 133), Bool.or(U32.is_eq(x, 160), Bool.or(U32.is_eq(x, 5760), Bool.or(Bool.and(U32.is_ge(x, 8192), U32.is_le(x, 8202)), Bool.or(U32.is_eq(x, 8232), Bool.or(U32.is_eq(x, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), z)))))))))), Bool.or(U32.is_eq(x, 12288), False{}), U32.is_eq(x, 12288), ac.or_false(U32.is_eq(x, 12288)))

def ac.ws_t(+c: Char, h: {ArgRepairCoerce.sp_white(c) == True{} : Bool}) -> {Ar.ws(c) == True{} : Bool}:
  Equal.trans(Bool, Ar.ws(c), ArgRepairCoerce.sp_white(c), True{}, Equal.sym(Bool, ArgRepairCoerce.sp_white(c), Ar.ws(c), ac.white(c)), h)

def ac.ws_f(+c: Char, h: {ArgRepairCoerce.sp_white(c) == False{} : Bool}) -> {Ar.ws(c) == False{} : Bool}:
  Equal.trans(Bool, Ar.ws(c), ArgRepairCoerce.sp_white(c), False{}, Equal.sym(Bool, ArgRepairCoerce.sp_white(c), Ar.ws(c), ac.white(c)), h)

# Reversal
# --------

def ac.app_nil(s: String) -> {String.append(s, SNil{}) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(String, String, z => SCon{h, z}, String.append(t, SNil{}), t, ac.app_nil(t))

# reversing p then s onto acc
def ac.rev_app(p: String, -s: String, -acc: String) -> {String.reverse.go(String.append(p, s), acc) == String.reverse.go(s, String.reverse.go(p, acc)) : String}:
  match p:
    case SNil{}:
      {==}
    case SCon{h, t}:
      ac.rev_app(t, s, SCon{h, acc})

# reversing x onto b then acc is reversing it onto b, then acc
def ac.rev_onto(x: String, -b: String, -acc: String) -> {String.reverse.go(x, String.append(b, acc)) == String.append(String.reverse.go(x, b), acc) : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{h, t}:
      ac.rev_onto(t, SCon{h, b}, acc)

# reversing onto acc, then reversing that, gives acc reversed onto s
def ac.rev_rev(s: String, -acc: String) -> {String.reverse.go(String.reverse.go(s, acc), SNil{}) == String.reverse.go(acc, s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      ac.rev_rev(t, SCon{h, acc})

def ac.white_rev(x: String, +acc: String, +hx: {ArgRepairCoerce.sp_all_white(x) == True{} : Bool}, ha: {ArgRepairCoerce.sp_all_white(acc) == True{} : Bool}) -> {ArgRepairCoerce.sp_all_white(String.reverse.go(x, acc)) == True{} : Bool}:
  match x:
    case SNil{}:
      ha
    case SCon{+h, +t}:
      +h1 = AB.ab.and_l(ArgRepairCoerce.sp_white(h), ArgRepairCoerce.sp_all_white(t), hx)
      +h2 = AB.ab.and_r(ArgRepairCoerce.sp_white(h), ArgRepairCoerce.sp_all_white(t), hx)
      ac.white_rev(t, SCon{h, acc}, h2, ac.and2(ArgRepairCoerce.sp_white(h), ArgRepairCoerce.sp_all_white(acc), h1, ha))

# Trimming
# --------

# leading White_Space goes
def ac.lstrip_white(a: String, +r: String, +h: {ArgRepairCoerce.sp_all_white(a) == True{} : Bool}) -> {Ar.lstrip(String.append(a, r)) == Ar.lstrip(r) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +hw = ac.ws_t(c, AB.ab.and_l(ArgRepairCoerce.sp_white(c), ArgRepairCoerce.sp_all_white(t), h))
      %Equal.sym(Bool, Ar.ws(c), True{}, hw) : {Ar.lstrip.at(_, c, String.append(t, r), Ar.lstrip(String.append(t, r))) == Ar.lstrip(r) : String}
      ac.lstrip_white(t, r, AB.ab.and_r(ArgRepairCoerce.sp_white(c), ArgRepairCoerce.sp_all_white(t), h))

# a text whose first char is no White_Space is kept
def ac.lstrip_keep(+c: Char, +t: String, h: {Ar.ws(c) == False{} : Bool}) -> {Ar.lstrip(SCon{c, t}) == SCon{c, t} : String}:
  %Equal.sym(Bool, Ar.ws(c), False{}, h) : {Ar.lstrip.at(_, c, t, Ar.lstrip(t)) == SCon{c, t} : String}
  {==}

# a text of White_Space only goes whole
def ac.lstrip_all(+b: String, h: {ArgRepairCoerce.sp_all_white(b) == True{} : Bool}) -> {Ar.lstrip(b) == SNil{} : String}:
  Equal.trans(String, Ar.lstrip(b), Ar.lstrip(String.append(b, SNil{})), SNil{}, Equal.cong(String, String, z => Ar.lstrip(z), b, String.append(b, SNil{}), Equal.sym(String, String.append(b, SNil{}), b, ac.app_nil(b))), ac.lstrip_white(b, SNil{}, h))

# t reversed onto c then acc, the last char c of c then t no White_Space:
# no leading White_Space
def ac.lrev(t: String, +c: Char, +acc: String, h: {ArgRepairCoerce.sp_ends_white(t, c) == False{} : Bool}) -> {Ar.lstrip(String.reverse.go(t, SCon{c, acc})) == String.reverse.go(t, SCon{c, acc}) : String}:
  match t:
    case SNil{}:
      ac.lstrip_keep(c, acc, ac.ws_f(c, h))
    case SCon{+d, +u}:
      ac.lrev(u, d, SCon{c, acc}, h)

# `str::trim` of White_Space a, a bare text u, then White_Space b is u
def ac.trim(+a: String, u: String, +b: String, ha: {ArgRepairCoerce.sp_all_white(a) == True{} : Bool}, hb: {ArgRepairCoerce.sp_all_white(b) == True{} : Bool}, +hu: {ArgRepairCoerce.sp_bare(u) == True{} : Bool}) -> {Ar.trim(String.append(a, String.append(u, b))) == u : String}:
  match u:
    case SNil{}:
      +e1 = Equal.trans(String, Ar.lstrip(String.append(a, b)), Ar.lstrip(b), SNil{}, ac.lstrip_white(a, b, ha), ac.lstrip_all(b, hb))
      %Equal.sym(String, Ar.lstrip(String.append(a, b)), SNil{}, e1) : {String.reverse(Ar.lstrip(String.reverse(_))) == SNil{} : String}
      {==}
    case SCon{+c, +t}:
      +nw = Bool.not(ArgRepairCoerce.sp_white(c))
      +ne = Bool.not(ArgRepairCoerce.sp_ends_white(t, c))
      +hc = ac.ws_f(c, ac.not_t(ArgRepairCoerce.sp_white(c), AB.ab.and_l(nw, ne, hu)))
      +he = ac.not_t(ArgRepairCoerce.sp_ends_white(t, c), AB.ab.and_r(nw, ne, hu))
      +tb = String.append(t, b)
      +x = String.append(a, SCon{c, tb})
      +e1 = Equal.trans(String, Ar.lstrip(x), Ar.lstrip(SCon{c, tb}), SCon{c, tb}, ac.lstrip_white(a, SCon{c, tb}, ha), ac.lstrip_keep(c, tb, hc))
      +r = String.reverse.go(t, SCon{c, SNil{}})
      +rb = String.reverse.go(b, SNil{})
      +e2 = Equal.trans(String, String.reverse.go(tb, SCon{c, SNil{}}), String.reverse.go(b, r), String.append(rb, r), ac.rev_app(t, b, SCon{c, SNil{}}), ac.rev_onto(b, SNil{}, r))
      +e3 = ac.lstrip_white(rb, r, ac.white_rev(b, SNil{}, hb, {==}))
      +e4 = ac.lrev(t, c, SNil{}, he)
      %Equal.sym(String, Ar.lstrip(x), SCon{c, tb}, e1) : {String.reverse(Ar.lstrip(String.reverse(_))) == SCon{c, t} : String}
      %Equal.sym(String, String.reverse.go(tb, SCon{c, SNil{}}), String.append(rb, r), e2) : {String.reverse(Ar.lstrip(_)) == SCon{c, t} : String}
      %Equal.sym(String, Ar.lstrip(String.append(rb, r)), Ar.lstrip(r), e3) : {String.reverse(_) == SCon{c, t} : String}
      %Equal.sym(String, Ar.lstrip(r), r, e4) : {String.reverse(_) == SCon{c, t} : String}
      ac.rev_rev(t, SCon{c, SNil{}})

# `str::trim` of a bare text is that text
def ac.trim_self(+u: String, hu: {ArgRepairCoerce.sp_bare(u) == True{} : Bool}) -> {Ar.trim(u) == u : String}:
  Equal.trans(String, Ar.trim(u), Ar.trim(String.append(u, SNil{})), u, Equal.cong(String, String, z => Ar.trim(z), u, String.append(u, SNil{}), Equal.sym(String, String.append(u, SNil{}), u, ac.app_nil(u))), ac.trim(SNil{}, u, SNil{}, {==}, {==}, hu))

# no char of s is White_Space
def ac.clean(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(Bool.not(Ar.ws(c)), ac.clean(t))

def ac.clean_app(x: String, +y: String, +hx: {ac.clean(x) == True{} : Bool}, hy: {ac.clean(y) == True{} : Bool}) -> {ac.clean(String.append(x, y)) == True{} : Bool}:
  match x:
    case SNil{}:
      hy
    case SCon{+c, +t}:
      +n = Bool.not(Ar.ws(c))
      ac.and2(n, ac.clean(String.append(t, y)), AB.ab.and_l(n, ac.clean(t), hx), ac.clean_app(t, y, AB.ab.and_r(n, ac.clean(t), hx), hy))

def ac.clean_rev(x: String, +acc: String, +hx: {ac.clean(x) == True{} : Bool}, ha: {ac.clean(acc) == True{} : Bool}) -> {ac.clean(String.reverse.go(x, acc)) == True{} : Bool}:
  match x:
    case SNil{}:
      ha
    case SCon{+c, +t}:
      +n = Bool.not(Ar.ws(c))
      ac.clean_rev(t, SCon{c, acc}, AB.ab.and_r(n, ac.clean(t), hx), ac.and2(n, ac.clean(acc), AB.ab.and_l(n, ac.clean(t), hx), ha))

# two texts with one `str::trim` are read alike, for every declared type
def ac.spell_eq(k: Ar.Ty, -it: Maybe<&2, String>, +x: String, +y: String, -n: Maybe<&2, String>, -sh: Ar.Shape, e: {Ar.trim(x) == Ar.trim(y) : String}) -> {Ar.spell(k, it, Some{x}, n, sh) == Ar.spell(k, it, Some{y}, n, sh) : Maybe<&2, Ar.To>}:
  match k:
    case Ar.KString{}:
      {==}
    case Ar.KBoolean{}:
      Equal.cong(String, Maybe<&2, Ar.To>, z => Ar.word(Ar.lower(z)), Ar.trim(x), Ar.trim(y), e)
    case Ar.KInteger{}:
      Equal.cong(String, Maybe<&2, Ar.To>, z => Ar.int(z), Ar.trim(x), Ar.trim(y), e)
    case Ar.KNumber{}:
      {==}
    case Ar.KObject{}:
      {==}
    case Ar.KArray{}:
      {==}
    case Ar.KOther{}:
      {==}

def ac.lstrip_clean(s: String, h: {ac.clean(s) == True{} : Bool}) -> {Ar.lstrip(s) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +n = Bool.not(Ar.ws(c))
      ac.lstrip_keep(c, t, ac.not_t(Ar.ws(c), AB.ab.and_l(n, ac.clean(t), h)))

# `str::trim` of a text with no White_Space is that text
def ac.trim_clean(+s: String, +h: {ac.clean(s) == True{} : Bool}) -> {Ar.trim(s) == s : String}:
  %Equal.sym(String, Ar.lstrip(s), s, ac.lstrip_clean(s, h)) : {String.reverse(Ar.lstrip(String.reverse(_))) == s : String}
  %Equal.sym(String, Ar.lstrip(String.reverse(s)), String.reverse(s), ac.lstrip_clean(String.reverse(s), ac.clean_rev(s, SNil{}, h, {==}))) : {String.reverse(_) == s : String}
  ac.rev_rev(s, SNil{})

# Words
# -----

def ac.lower_at(b: Bool, x: U32) -> {Ar.lower.at(b, x) == ArgRepairCoerce.sp_lower.at(b, x) : U32}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the code's ASCII lower case is Rust's `to_ascii_lowercase`
def ac.lower(s: String) -> {Ar.lower(s) == ArgRepairCoerce.sp_lower(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          %ac.lower(t) : {SCon{Chr{Ar.lower.code(x)}, Ar.lower(t)} == SCon{Chr{ArgRepairCoerce.sp_lower.at(Bool.and(U32.is_ge(x, 65), U32.is_le(x, 90)), x)}, _} : String}
          %ac.lower_at(Bool.and(U32.is_ge(x, 65), U32.is_le(x, 90)), x) : {SCon{Chr{Ar.lower.code(x)}, Ar.lower(t)} == SCon{Chr{_}, Ar.lower(t)} : String}
          {==}

# omp's word order, then the code's
def ac.perm(a: Bool, b: Bool, c: Bool, d: Bool) -> {Bool.or(a, Bool.or(d, Bool.or(b, Bool.or(c, False{})))) == Bool.or(a, Bool.or(b, Bool.or(c, d))) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      match b:
        case True{}:
          match d:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match c:
            case True{}:
              match d:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match d:
                case True{}:
                  {==}
                case False{}:
                  {==}

def ac.word_of(t: Bool, f: Bool) -> {Ar.word.of(t, f) == ArgRepairCoerce.sp_bool.of(t, f) : Maybe<&2, Ar.To>}:
  match t:
    case True{}:
      {==}
    case False{}:
      match f:
        case True{}:
          {==}
        case False{}:
          {==}

# the code's words are omp's
def ac.word(+w: String) -> {Ar.word(w) == ArgRepairCoerce.sp_bool.word(w) : Maybe<&2, Ar.To>}:
  +t = Bool.or(String.eq(w, "true"), Bool.or(String.eq(w, "1"), Bool.or(String.eq(w, "yes"), Bool.or(String.eq(w, "on"), False{}))))
  %ac.perm(String.eq(w, "true"), String.eq(w, "yes"), String.eq(w, "on"), String.eq(w, "1")) : {Ar.word.of(_, Bool.or(String.eq(w, "false"), Bool.or(String.eq(w, "no"), Bool.or(String.eq(w, "off"), String.eq(w, "0"))))) == ArgRepairCoerce.sp_bool.word(w) : Maybe<&2, Ar.To>}
  %ac.perm(String.eq(w, "false"), String.eq(w, "no"), String.eq(w, "off"), String.eq(w, "0")) : {Ar.word.of(t, _) == ArgRepairCoerce.sp_bool.word(w) : Maybe<&2, Ar.To>}
  ac.word_of(t, Bool.or(String.eq(w, "false"), Bool.or(String.eq(w, "0"), Bool.or(String.eq(w, "no"), Bool.or(String.eq(w, "off"), False{})))))

# Integers
# --------

def ac.dig_digit(d: ArgRepairCoerce.Dig) -> {Ar.is_digit(ArgRepairCoerce.sp_dig(d)) == True{} : Bool}:
  match d:
    case ArgRepairCoerce.D0{}:
      {==}
    case ArgRepairCoerce.D1{}:
      {==}
    case ArgRepairCoerce.D2{}:
      {==}
    case ArgRepairCoerce.D3{}:
      {==}
    case ArgRepairCoerce.D4{}:
      {==}
    case ArgRepairCoerce.D5{}:
      {==}
    case ArgRepairCoerce.D6{}:
      {==}
    case ArgRepairCoerce.D7{}:
      {==}
    case ArgRepairCoerce.D8{}:
      {==}
    case ArgRepairCoerce.D9{}:
      {==}

def ac.dig_ws(d: ArgRepairCoerce.Dig) -> {Bool.not(Ar.ws(ArgRepairCoerce.sp_dig(d))) == True{} : Bool}:
  match d:
    case ArgRepairCoerce.D0{}:
      {==}
    case ArgRepairCoerce.D1{}:
      {==}
    case ArgRepairCoerce.D2{}:
      {==}
    case ArgRepairCoerce.D3{}:
      {==}
    case ArgRepairCoerce.D4{}:
      {==}
    case ArgRepairCoerce.D5{}:
      {==}
    case ArgRepairCoerce.D6{}:
      {==}
    case ArgRepairCoerce.D7{}:
      {==}
    case ArgRepairCoerce.D8{}:
      {==}
    case ArgRepairCoerce.D9{}:
      {==}

def ac.dig_minus(d: ArgRepairCoerce.Dig) -> {Char.is_eq(ArgRepairCoerce.sp_dig(d), '-') == False{} : Bool}:
  match d:
    case ArgRepairCoerce.D0{}:
      {==}
    case ArgRepairCoerce.D1{}:
      {==}
    case ArgRepairCoerce.D2{}:
      {==}
    case ArgRepairCoerce.D3{}:
      {==}
    case ArgRepairCoerce.D4{}:
      {==}
    case ArgRepairCoerce.D5{}:
      {==}
    case ArgRepairCoerce.D6{}:
      {==}
    case ArgRepairCoerce.D7{}:
      {==}
    case ArgRepairCoerce.D8{}:
      {==}
    case ArgRepairCoerce.D9{}:
      {==}

def ac.dig_plus(d: ArgRepairCoerce.Dig) -> {Char.is_eq(ArgRepairCoerce.sp_dig(d), '+') == False{} : Bool}:
  match d:
    case ArgRepairCoerce.D0{}:
      {==}
    case ArgRepairCoerce.D1{}:
      {==}
    case ArgRepairCoerce.D2{}:
      {==}
    case ArgRepairCoerce.D3{}:
      {==}
    case ArgRepairCoerce.D4{}:
      {==}
    case ArgRepairCoerce.D5{}:
      {==}
    case ArgRepairCoerce.D6{}:
      {==}
    case ArgRepairCoerce.D7{}:
      {==}
    case ArgRepairCoerce.D8{}:
      {==}
    case ArgRepairCoerce.D9{}:
      {==}

def ac.dig_zero(d: ArgRepairCoerce.Dig) -> {Char.is_eq(ArgRepairCoerce.sp_dig(d), '0') == ArgRepairCoerce.sp_zero(d) : Bool}:
  match d:
    case ArgRepairCoerce.D0{}:
      {==}
    case ArgRepairCoerce.D1{}:
      {==}
    case ArgRepairCoerce.D2{}:
      {==}
    case ArgRepairCoerce.D3{}:
      {==}
    case ArgRepairCoerce.D4{}:
      {==}
    case ArgRepairCoerce.D5{}:
      {==}
    case ArgRepairCoerce.D6{}:
      {==}
    case ArgRepairCoerce.D7{}:
      {==}
    case ArgRepairCoerce.D8{}:
      {==}
    case ArgRepairCoerce.D9{}:
      {==}

# a text past "0" in the order (its first char past `0`) is not "0"
def ac.gt_ne(x: String) -> {Cmp.is_eq(String.order.go(x, SNil{}, GT{})) == False{} : Bool}:
  match x:
    case SNil{}:
      {==}
    case SCon{h, t}:
      match h:
        case Chr{y}:
          {==}

def ac.nz_text(d: ArgRepairCoerce.Dig, +x: String, nz: {ArgRepairCoerce.sp_zero(d) == False{} : Bool}) -> {String.eq(SCon{ArgRepairCoerce.sp_dig(d), x}, "0") == False{} : Bool}:
  match d:
    case ArgRepairCoerce.D0{}:
      AB.ab.absurd_tf({String.eq(SCon{'0', x}, "0") == False{} : Bool}, nz)
    case ArgRepairCoerce.D1{}:
      ac.gt_ne(x)
    case ArgRepairCoerce.D2{}:
      ac.gt_ne(x)
    case ArgRepairCoerce.D3{}:
      ac.gt_ne(x)
    case ArgRepairCoerce.D4{}:
      ac.gt_ne(x)
    case ArgRepairCoerce.D5{}:
      ac.gt_ne(x)
    case ArgRepairCoerce.D6{}:
      ac.gt_ne(x)
    case ArgRepairCoerce.D7{}:
      ac.gt_ne(x)
    case ArgRepairCoerce.D8{}:
      ac.gt_ne(x)
    case ArgRepairCoerce.D9{}:
      ac.gt_ne(x)

def ac.digs_digits(ds: List<&2, ArgRepairCoerce.Dig>) -> {Ar.digits(ArgRepairCoerce.sp_digs(ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case +d <> +t:
      %Equal.sym(Bool, Ar.is_digit(ArgRepairCoerce.sp_dig(d)), True{}, ac.dig_digit(d)) : {Bool.and(_, Ar.digits(ArgRepairCoerce.sp_digs(t))) == True{} : Bool}
      ac.digs_digits(t)

def ac.zeros_digits(z: Nat) -> {Ar.digits(ArgRepairCoerce.sp_zeros(z)) == True{} : Bool}:
  match z:
    case 0n:
      {==}
    case 1n+p:
      ac.zeros_digits(p)

def ac.digits_app(x: String, +y: String, +hx: {Ar.digits(x) == True{} : Bool}, hy: {Ar.digits(y) == True{} : Bool}) -> {Ar.digits(String.append(x, y)) == True{} : Bool}:
  match x:
    case SNil{}:
      hy
    case SCon{+c, +t}:
      ac.and2(Ar.is_digit(c), Ar.digits(String.append(t, y)), AB.ab.and_l(Ar.is_digit(c), Ar.digits(t), hx), ac.digits_app(t, y, AB.ab.and_r(Ar.is_digit(c), Ar.digits(t), hx), hy))

# the spec's ASCII digits are the code's
def ac.digits_eq(s: String) -> {ArgRepairCoerce.sp_all_digits(s) == Ar.digits(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          %Equal.sym(Bool, ArgRepairCoerce.sp_all_digits(t), Ar.digits(t), ac.digits_eq(t)) : {Bool.and(Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)), _) == Bool.and(Ar.is_digit(Chr{x}), Ar.digits(t)) : Bool}
          {==}

def ac.clean_zeros(z: Nat) -> {ac.clean(ArgRepairCoerce.sp_zeros(z)) == True{} : Bool}:
  match z:
    case 0n:
      {==}
    case 1n+p:
      ac.clean_zeros(p)

def ac.clean_digs(ds: List<&2, ArgRepairCoerce.Dig>) -> {ac.clean(ArgRepairCoerce.sp_digs(ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case +d <> +t:
      ac.and2(Bool.not(Ar.ws(ArgRepairCoerce.sp_dig(d))), ac.clean(ArgRepairCoerce.sp_digs(t)), ac.dig_ws(d), ac.clean_digs(t))

def ac.clean_sign(s: ArgRepairCoerce.Sign) -> {ac.clean(ArgRepairCoerce.sp_sign(s)) == True{} : Bool}:
  match s:
    case ArgRepairCoerce.SgNone{}:
      {==}
    case ArgRepairCoerce.SgPlus{}:
      {==}
    case ArgRepairCoerce.SgMinus{}:
      {==}

def ac.unzero_zeros(z: Nat, +s: String) -> {Ar.unzero(String.append(ArgRepairCoerce.sp_zeros(z), s)) == Ar.unzero(s) : String}:
  match z:
    case 0n:
      {==}
    case 1n+p:
      ac.unzero_zeros(p, s)

def ac.unzero_all(z: Nat) -> {Ar.unzero(ArgRepairCoerce.sp_zeros(z)) == SNil{} : String}:
  match z:
    case 0n:
      {==}
    case 1n+p:
      ac.unzero_all(p)

# digits that open with no zero lose nothing
def ac.unzero_lead(+d: ArgRepairCoerce.Dig, +ds: List<&2, ArgRepairCoerce.Dig>, nz: {ArgRepairCoerce.sp_zero(d) == False{} : Bool}) -> {Ar.unzero(ArgRepairCoerce.sp_digs(d <> ds)) == ArgRepairCoerce.sp_digs(d <> ds) : String}:
  +x = ArgRepairCoerce.sp_digs(ds)
  +e = Equal.trans(Bool, Char.is_eq(ArgRepairCoerce.sp_dig(d), '0'), ArgRepairCoerce.sp_zero(d), False{}, ac.dig_zero(d), nz)
  %Equal.sym(Bool, Char.is_eq(ArgRepairCoerce.sp_dig(d), '0'), False{}, e) : {Ar.unzero.at(_, ArgRepairCoerce.sp_dig(d), x, Ar.unzero(x)) == SCon{ArgRepairCoerce.sp_dig(d), x} : String}
  {==}

# zeros then digits that open with no zero: those digits
def ac.canon_lead(+z: Nat, +d: ArgRepairCoerce.Dig, +ds: List<&2, ArgRepairCoerce.Dig>, nz: {ArgRepairCoerce.sp_zero(d) == False{} : Bool}) -> {Ar.canon(String.append(ArgRepairCoerce.sp_zeros(z), ArgRepairCoerce.sp_digs(d <> ds))) == ArgRepairCoerce.sp_digs(d <> ds) : String}:
  +y = ArgRepairCoerce.sp_digs(d <> ds)
  +e = Equal.trans(String, Ar.unzero(String.append(ArgRepairCoerce.sp_zeros(z), y)), Ar.unzero(y), y, ac.unzero_zeros(z, y), ac.unzero_lead(d, ds, nz))
  %Equal.sym(String, Ar.unzero(String.append(ArgRepairCoerce.sp_zeros(z), y)), y, e) : {Ar.canon.fin(_) == y : String}
  {==}

# one or more zeros: "0"
def ac.canon_zero(+z: Nat) -> {Ar.canon(SCon{'0', ArgRepairCoerce.sp_zeros(z)}) == "0" : String}:
  %Equal.sym(String, Ar.unzero(ArgRepairCoerce.sp_zeros(z)), SNil{}, ac.unzero_all(z)) : {Ar.canon.fin(_) == "0" : String}
  {==}

def ac.nonempty(z: Nat, +d: ArgRepairCoerce.Dig, +ds: List<&2, ArgRepairCoerce.Dig>) -> {String.is_empty(String.append(ArgRepairCoerce.sp_zeros(z), ArgRepairCoerce.sp_digs(d <> ds))) == False{} : Bool}:
  match z:
    case 0n:
      {==}
    case 1n+p:
      {==}

# digits read: the sign and the canonical digits
def ac.digits_ok(+neg: Bool, +s: String, hn: {String.is_empty(s) == False{} : Bool}, hd: {Ar.digits(s) == True{} : Bool}) -> {Ar.int.digits(neg, s) == Ar.int.sign(neg, Ar.canon(s)) : Maybe<&2, Ar.To>}:
  %Equal.sym(Bool, String.is_empty(s), False{}, hn) : {Ar.int.digits.at(Bool.and(Bool.not(_), Ar.digits(s)), neg, s) == Ar.int.sign(neg, Ar.canon(s)) : Maybe<&2, Ar.To>}
  %Equal.sym(Bool, Ar.digits(s), True{}, hd) : {Ar.int.digits.at(Bool.and(True{}, _), neg, s) == Ar.int.sign(neg, Ar.canon(s)) : Maybe<&2, Ar.To>}
  {==}

def ac.fit(b: Bool, -x: String) -> {Ar.int.fit(b, x) == ArgRepairCoerce.sp_when(b, Ar.TNum{x}) : Maybe<&2, Ar.To>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}
