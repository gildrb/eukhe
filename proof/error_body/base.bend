# eukhe: lemmas shared by the proofs of area error_body: the order of
# 32-bit words (ebw.*: a code past U+FFFF, the pair U+2028/U+2029 as a
# range), each char test the spec's (ebc.*), the trims, the units, the
# prefix and the cut the spec's (ebt.*), the body (ebb.*) and the display
# string (ebs.*) the spec's

import Base
import ../../bend/error_body.bend as Eb
import ../../laws/error_body.bend as ErrorBody
import ../base/staging.bend as LStg

# Words
# -----

# the bits of a U32
def ebw.bits(x: U32) -> Word(32n):
  match x:
    case U32{w}:
      w

# whether every bit of w is set
def ebw.max(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          Bool.and(b, ebw.max(p, t))

def ebw.flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

def ebw.fin_flip(c: Cmp, a: Bool, b: Bool) -> {Word.cmp.fin(a, b, ebw.flip(c)) == ebw.flip(Word.cmp.fin(b, a, c)) : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      match a b:
        case True{} True{}:
          {==}
        case True{} False{}:
          {==}
        case False{} True{}:
          {==}
        case False{} False{}:
          {==}
    case GT{}:
      {==}

# a word's order is the flip of the order the other way
def ebw.anti(n: Nat, a: Word(n), b: Word(n)) -> {Word.cmp(n, a, b) == ebw.flip(Word.cmp(n, b, a)) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          %Equal.sym(Cmp, Word.cmp(p, at, bt), ebw.flip(Word.cmp(p, bt, at)), ebw.anti(p, at, bt)) : {Word.cmp.fin(ab, bb, _) == ebw.flip(Word.cmp.fin(bb, ab, Word.cmp(p, bt, at))) : Cmp}
          ebw.fin_flip(Word.cmp(p, bt, at), ab, bb)

def ebw.lt_le_fin(c: Cmp, x0: Bool) -> {Cmp.is_lt(Word.cmp.fin(False{}, x0, c)) == Cmp.is_le(Word.cmp.fin(True{}, x0, c)) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      match x0:
        case True{}:
          {==}
        case False{}:
          {==}
    case GT{}:
      {==}

def ebw.lt_fin_t(c: Cmp, x0: Bool) -> {Cmp.is_lt(Word.cmp.fin(True{}, x0, c)) == Cmp.is_lt(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      match x0:
        case True{}:
          {==}
        case False{}:
          {==}
    case GT{}:
      {==}

def ebw.le_fin_f(c: Cmp, x0: Bool) -> {Cmp.is_le(Word.cmp.fin(False{}, x0, c)) == Cmp.is_le(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      match x0:
        case True{}:
          {==}
        case False{}:
          {==}
    case GT{}:
      {==}

def ebw.lt_inc.at(a0: Bool, +p: Nat, +at: Word(p), +x0: Bool, +xt: Word(p), ih: {Cmp.is_lt(Word.cmp(p, at, xt)) == Bool.and(Bool.not(ebw.max(p, at)), Cmp.is_le(Word.cmp(p, Word.inc(p, at), xt))) : Bool}) -> {Cmp.is_lt(Word.cmp(1n+p, WCon{a0, at}, WCon{x0, xt})) == Bool.and(Bool.not(ebw.max(1n+p, WCon{a0, at})), Cmp.is_le(Word.cmp(1n+p, Word.inc(1n+p, WCon{a0, at}), WCon{x0, xt}))) : Bool}:
  match a0:
    case False{}:
      ebw.lt_le_fin(Word.cmp(p, at, xt), x0)
    case True{}:
      %Equal.sym(Bool, Cmp.is_lt(Word.cmp.fin(True{}, x0, Word.cmp(p, at, xt))), Cmp.is_lt(Word.cmp(p, at, xt)), ebw.lt_fin_t(Word.cmp(p, at, xt), x0)) : {_ == Bool.and(Bool.not(ebw.max(p, at)), Cmp.is_le(Word.cmp.fin(False{}, x0, Word.cmp(p, Word.inc(p, at), xt)))) : Bool}
      %Equal.sym(Bool, Cmp.is_le(Word.cmp.fin(False{}, x0, Word.cmp(p, Word.inc(p, at), xt))), Cmp.is_le(Word.cmp(p, Word.inc(p, at), xt)), ebw.le_fin_f(Word.cmp(p, Word.inc(p, at), xt), x0)) : {Cmp.is_lt(Word.cmp(p, at, xt)) == Bool.and(Bool.not(ebw.max(p, at)), _) : Bool}
      ih

# a < x exactly when a + 1 <= x, unless a + 1 wraps
def ebw.lt_inc(n: Nat, a: Word(n), x: Word(n)) -> {Cmp.is_lt(Word.cmp(n, a, x)) == Bool.and(Bool.not(ebw.max(n, a)), Cmp.is_le(Word.cmp(n, Word.inc(n, a), x))) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match a x:
        case WCon{a0, +at} WCon{+x0, +xt}:
          ebw.lt_inc.at(a0, p, at, x0, xt, ebw.lt_inc(p, at, xt))

# a code past U+FFFF: 65536 <= x is 65535 < x
def ebw.astral(x: U32) -> {U32.is_le(65536, x) == U32.is_lt(65535, x) : Bool}:
  match x:
    case U32{+w}:
      Equal.sym(Bool, U32.is_lt(65535, U32{w}), U32.is_le(65536, U32{w}), ebw.lt_inc(32n, ebw.bits(65535), w))

def ebw.pair_fin(c: Cmp, x0: Bool) -> {Bool.or(Cmp.is_eq(Word.cmp.fin(x0, False{}, c)), Cmp.is_eq(Word.cmp.fin(x0, True{}, c))) == Bool.and(Cmp.is_le(Word.cmp.fin(False{}, x0, ebw.flip(c))), Cmp.is_le(Word.cmp.fin(x0, True{}, c))) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      match x0:
        case True{}:
          {==}
        case False{}:
          {==}
    case GT{}:
      {==}

# the tail of the bits of a U32
def ebw.tail(x: U32) -> Word(31n):
  match x:
    case U32{w}:
      match w:
        case WCon{b, t}:
          t

# x is U+2028 or U+2029 exactly when it is in the range of the two
def ebw.pair(x: U32) -> {Bool.or(U32.is_eq(x, 8232), U32.is_eq(x, 8233)) == Bool.and(U32.is_le(8232, x), U32.is_le(x, 8233)) : Bool}:
  match x:
    case U32{w}:
      match w:
        case WCon{+x0, +xt}:
          %Equal.sym(Cmp, Word.cmp(31n, ebw.tail(8232), xt), ebw.flip(Word.cmp(31n, xt, ebw.tail(8232))), ebw.anti(31n, ebw.tail(8232), xt)) : {Bool.or(U32.is_eq(U32{WCon{x0, xt}}, 8232), U32.is_eq(U32{WCon{x0, xt}}, 8233)) == Bool.and(Cmp.is_le(Word.cmp.fin(False{}, x0, _)), U32.is_le(U32{WCon{x0, xt}}, 8233)) : Bool}
          ebw.pair_fin(Word.cmp(31n, xt, ebw.tail(8232)), x0)

# Chars
# -----

def ebc.or_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def ebc.ws_tail(+x: U32) -> {Bool.or(U32.is_eq(x, 8232), Bool.or(U32.is_eq(x, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), Bool.or(U32.is_eq(x, 12288), U32.is_eq(x, 65279)))))) == Bool.or(ErrorBody.sp_in(x, 8232, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), Bool.or(U32.is_eq(x, 12288), U32.is_eq(x, 65279))))) : Bool}:
  +r = Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), Bool.or(U32.is_eq(x, 12288), U32.is_eq(x, 65279))))
  Equal.trans(Bool, Bool.or(U32.is_eq(x, 8232), Bool.or(U32.is_eq(x, 8233), r)), Bool.or(Bool.or(U32.is_eq(x, 8232), U32.is_eq(x, 8233)), r), Bool.or(ErrorBody.sp_in(x, 8232, 8233), r), ebc.or_assoc(U32.is_eq(x, 8232), U32.is_eq(x, 8233), r), Equal.cong(Bool, Bool, z => Bool.or(z, r), Bool.or(U32.is_eq(x, 8232), U32.is_eq(x, 8233)), ErrorBody.sp_in(x, 8232, 8233), ebw.pair(x)))

# the code's white space is the spec's
def ebc.ws(c: Char) -> {Eb.is_ws(c) == ErrorBody.sp_ws(c) : Bool}:
  match c:
    case Chr{+x}:
      Equal.cong(Bool, Bool, z => Bool.or(Bool.and(U32.is_le(9, x), U32.is_le(x, 13)), Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 160), Bool.or(U32.is_eq(x, 5760), Bool.or(Bool.and(U32.is_le(8192, x), U32.is_le(x, 8202)), z))))), Bool.or(U32.is_eq(x, 8232), Bool.or(U32.is_eq(x, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), Bool.or(U32.is_eq(x, 12288), U32.is_eq(x, 65279)))))), Bool.or(ErrorBody.sp_in(x, 8232, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), Bool.or(U32.is_eq(x, 12288), U32.is_eq(x, 65279))))), ebc.ws_tail(x))

def ebc.u_pick(a: Bool) -> {Eb.units1.at(a) == ErrorBody.sp_u.pick(a) : Nat}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# the code's UTF-16 units of a char are the spec's
def ebc.u(c: Char) -> {Eb.units1(c) == ErrorBody.sp_u(c) : Nat}:
  match c:
    case Chr{+x}:
      %Equal.sym(Bool, U32.is_le(65536, x), U32.is_lt(65535, x), ebw.astral(x)) : {Eb.units1.at(_) == ErrorBody.sp_u.pick(U32.is_lt(65535, x)) : Nat}
      ebc.u_pick(U32.is_lt(65535, x))

# Text
# ----

def ebt.start_pick(w: Bool, +c: Char, +t: String, -x: String, -y: String, e: {x == y : String}) -> {Eb.when(w, u => x, SCon{c, t}) == ErrorBody.sp_trim_start.pick(w, c, t, y) : String}:
  match w:
    case True{}:
      e
    case False{}:
      {==}

# the code's trim of the start is the spec's
def ebt.start(s: String) -> {Eb.trim_start(s) == ErrorBody.sp_trim_start(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Eb.is_ws(c), ErrorBody.sp_ws(c), ebc.ws(c)) : {Eb.when(_, u => Eb.trim_start(t), SCon{c, t}) == ErrorBody.sp_trim_start.pick(ErrorBody.sp_ws(c), c, t, ErrorBody.sp_trim_start(t)) : String}
      ebt.start_pick(ErrorBody.sp_ws(c), c, t, Eb.trim_start(t), ErrorBody.sp_trim_start(t), ebt.start(t))

# r is no text
def ebt.Cons(r: String) -> Type:
  match r:
    case SNil{}:
      {True{} == False{} : Bool}
    case SCon{d, u}:
      Unit

# the spec's trim of the end is empty exactly when all is white space
def ebt.Shape(b: Bool, r: String) -> Type:
  match b:
    case True{}:
      {r == SNil{} : String}
    case False{}:
      ebt.Cons(r)

def ebt.shape_pick(b: Bool, +c: Char, -t: String, -r: String) -> ebt.Shape(b, ErrorBody.sp_trim_end.pick(b, c, t, r)):
  match b:
    case True{}:
      {==}
    case False{}:
      Unit{}

def ebt.shape(s: String) -> ebt.Shape(ErrorBody.sp_all_ws(s), ErrorBody.sp_trim_end(s)):
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      ebt.shape_pick(ErrorBody.sp_all_ws(SCon{c, t}), c, t, ErrorBody.sp_trim_end(t))

def ebt.last(w: Bool, +c: Char, -t: String) -> {Eb.trim_end.last(c, w) == ErrorBody.sp_trim_end.pick(Bool.and(w, True{}), c, t, SNil{}) : String}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

def ebt.keep(w: Bool, +c: Char, -t: String, +d: Char, +u: String) -> {SCon{c, SCon{d, u}} == ErrorBody.sp_trim_end.pick(Bool.and(w, False{}), c, t, SCon{d, u}) : String}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

def ebt.end_at(b: Bool, r: String, +c: Char, -t: String, sh: ebt.Shape(b, r)) -> {Eb.trim_end.at(c, r) == ErrorBody.sp_trim_end.pick(Bool.and(ErrorBody.sp_ws(c), b), c, t, r) : String}:
  match b:
    case True{}:
      %Equal.sym(String, r, SNil{}, sh) : {Eb.trim_end.at(c, _) == ErrorBody.sp_trim_end.pick(Bool.and(ErrorBody.sp_ws(c), True{}), c, t, _) : String}
      %Equal.sym(Bool, Eb.is_ws(c), ErrorBody.sp_ws(c), ebc.ws(c)) : {Eb.trim_end.last(c, _) == ErrorBody.sp_trim_end.pick(Bool.and(ErrorBody.sp_ws(c), True{}), c, t, SNil{}) : String}
      ebt.last(ErrorBody.sp_ws(c), c, t)
    case False{}:
      match r:
        case SNil{}:
          LStg.stg.absurd({Eb.trim_end.at(c, SNil{}) == ErrorBody.sp_trim_end.pick(Bool.and(ErrorBody.sp_ws(c), False{}), c, t, SNil{}) : String}, sh)
        case SCon{+d, +u}:
          ebt.keep(ErrorBody.sp_ws(c), c, t, d, u)

# the code's trim of the end is the spec's
def ebt.end(s: String) -> {Eb.trim_end(s) == ErrorBody.sp_trim_end(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Eb.trim_end(t), ErrorBody.sp_trim_end(t), ebt.end(t)) : {Eb.trim_end.at(c, _) == ErrorBody.sp_trim_end(SCon{c, t}) : String}
      ebt.end_at(ErrorBody.sp_all_ws(t), ErrorBody.sp_trim_end(t), c, t, ebt.shape(t))

# the code's trim is the spec's
def ebt.trim(+s: String) -> {Eb.trim(s) == ErrorBody.sp_trim(s) : String}:
  %Equal.sym(String, Eb.trim_start(s), ErrorBody.sp_trim_start(s), ebt.start(s)) : {Eb.trim_end(_) == ErrorBody.sp_trim(s) : String}
  ebt.end(ErrorBody.sp_trim_start(s))

# the code's UTF-16 units of a text are the spec's
def ebt.units(s: String) -> {Eb.units(s) == ErrorBody.sp_units(s) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Nat, Eb.units1(c), ErrorBody.sp_u(c), ebc.u(c)) : {Nat.add(_, Eb.units(t)) == Nat.add(ErrorBody.sp_u(c), ErrorBody.sp_units(t)) : Nat}
      %Equal.sym(Nat, Eb.units(t), ErrorBody.sp_units(t), ebt.units(t)) : {Nat.add(ErrorBody.sp_u(c), _) == Nat.add(ErrorBody.sp_u(c), ErrorBody.sp_units(t)) : Nat}
      {==}

def ebt.prefix_pick(w: Bool, +c: Char, -x: String, -y: String, e: {x == y : String}) -> {Eb.when(w, u => SCon{c, x}, SNil{}) == ErrorBody.sp_prefix.pick(w, c, y) : String}:
  match w:
    case True{}:
      Equal.cong(String, String, z => SCon{c, z}, x, y, e)
    case False{}:
      {==}

# the code's prefix within room units is the spec's
def ebt.prefix(s: String, +room: Nat) -> {Eb.prefix(s, room) == ErrorBody.sp_prefix(s, room) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Nat, Eb.units1(c), ErrorBody.sp_u(c), ebc.u(c)) : {Eb.when(Nat.is_le(_, room), u => SCon{c, Eb.prefix(t, Nat.sub(room, _))}, SNil{}) == ErrorBody.sp_prefix(SCon{c, t}, room) : String}
      ebt.prefix_pick(Nat.is_le(ErrorBody.sp_u(c), room), c, Eb.prefix(t, Nat.sub(room, ErrorBody.sp_u(c))), ErrorBody.sp_prefix(t, Nat.sub(room, ErrorBody.sp_u(c))), ebt.prefix(t, Nat.sub(room, ErrorBody.sp_u(c))))

def ebt.cut_at(fits: Bool, +text: String, +max: Nat) -> {Eb.truncate.at(text, max, ErrorBody.sp_units(text), fits) == ErrorBody.sp_truncate.pick(fits, text, max) : String}:
  match fits:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(String, Eb.prefix(text, max), ErrorBody.sp_prefix(text, max), ebt.prefix(text, max)) : {String.concat([_, "... [truncated ", Nat.show(Nat.sub(ErrorBody.sp_units(text), max)), " chars]"]) == ErrorBody.sp_truncate.pick(False{}, text, max) : String}
      {==}

# the code's cut is the spec's
def ebt.truncate(+text: String, +max: Nat) -> {Eb.truncate(text, max) == ErrorBody.sp_truncate(text, max) : String}:
  %Equal.sym(Nat, Eb.units(text), ErrorBody.sp_units(text), ebt.units(text)) : {Eb.truncate.at(text, max, _, Nat.is_le(_, max)) == ErrorBody.sp_truncate(text, max) : String}
  ebt.cut_at(Nat.is_le(ErrorBody.sp_units(text), max), text, max)

# The body
# --------

def ebb.later(e: Eb.Probe, r: Eb.Probe) -> {Eb.pick.error(e, r) == ErrorBody.sp_pick.later(e, r) : Maybe<&2, String>}:
  match e r:
    case Eb.PNone{} Eb.PNone{}:
      {==}
    case Eb.PNone{} Eb.PText{x}:
      {==}
    case Eb.PNone{} Eb.PObj{x}:
      {==}
    case Eb.PText{y} Eb.PNone{}:
      {==}
    case Eb.PText{y} Eb.PText{x}:
      {==}
    case Eb.PText{y} Eb.PObj{x}:
      {==}
    case Eb.PObj{y} Eb.PNone{}:
      {==}
    case Eb.PObj{y} Eb.PText{x}:
      {==}
    case Eb.PObj{y} Eb.PObj{x}:
      {==}

# the code's first usable place is the spec's
def ebb.pick(b: Eb.Probe, e: Eb.Probe, r: Eb.Probe) -> {Eb.pick(b, e, r) == ErrorBody.sp_pick(b, e, r) : Maybe<&2, String>}:
  match b:
    case Eb.PText{x}:
      {==}
    case Eb.PNone{}:
      ebb.later(e, r)
    case Eb.PObj{y}:
      ebb.later(e, r)

def ebb.of(t: String) -> {Eb.body.of(t) == ErrorBody.sp_body.of(String.is_empty(t), t) : Maybe<&2, String>}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      %Equal.sym(String, Eb.truncate(SCon{c, u}, 4000n), ErrorBody.sp_truncate(SCon{c, u}, 4000n), ebt.truncate(SCon{c, u}, 4000n)) : {Some{_} == Some{ErrorBody.sp_truncate(SCon{c, u}, 4000n)} : Maybe<&2, String>}
      {==}

def ebb.trim(m: Maybe<&2, String>) -> {Eb.body.trim(m) == ErrorBody.sp_body.trim(m) : Maybe<&2, String>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(String, Eb.trim(x), ErrorBody.sp_trim(x), ebt.trim(x)) : {Eb.body.of(_) == ErrorBody.sp_body.trim(Some{x}) : Maybe<&2, String>}
      ebb.of(ErrorBody.sp_trim(x))

# the code's body is the spec's
def ebb.body(+b: Eb.Probe, +e: Eb.Probe, +r: Eb.Probe) -> {Eb.body(b, e, r) == ErrorBody.sp_body(b, e, r) : Maybe<&2, String>}:
  %Equal.sym(Maybe<&2, String>, Eb.pick(b, e, r), ErrorBody.sp_pick(b, e, r), ebb.pick(b, e, r)) : {Eb.body.trim(_) == ErrorBody.sp_body(b, e, r) : Maybe<&2, String>}
  ebb.trim(ErrorBody.sp_pick(b, e, r))

# The display string
# ------------------

# the code's display string is the spec's
def ebs.show(c: Bool, st: Maybe<&2, String>, b: Maybe<&2, String>, p: Maybe<&2, String>, +m: String) -> {Eb.show(c, st, b, p, m) == ErrorBody.sp_show(c, st, b, p, m) : String}:
  match c st b p:
    case True{} None{} None{} None{}:
      {==}
    case True{} None{} None{} Some{q}:
      {==}
    case True{} None{} Some{x} None{}:
      {==}
    case True{} None{} Some{x} Some{q}:
      {==}
    case True{} Some{s} None{} None{}:
      {==}
    case True{} Some{s} None{} Some{q}:
      {==}
    case True{} Some{s} Some{x} None{}:
      {==}
    case True{} Some{s} Some{x} Some{q}:
      {==}
    case False{} None{} None{} None{}:
      {==}
    case False{} None{} None{} Some{q}:
      {==}
    case False{} None{} Some{x} None{}:
      {==}
    case False{} None{} Some{x} Some{q}:
      {==}
    case False{} Some{s} None{} None{}:
      {==}
    case False{} Some{s} None{} Some{q}:
      {==}
    case False{} Some{s} Some{x} None{}:
      {==}
    case False{} Some{s} Some{x} Some{q}:
      {==}
