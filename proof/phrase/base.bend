# eukhe: lemmas shared by the proofs of area phrase. Each search law is
# first proven without its premise, for the search's own answer b: when b
# is True the claim holds, when False there is nothing to show (phb.CP,
# phb.SP, phb.OSP). The induction follows the search itself (the text
# first, then the items), and each step names the answers of its
# sub-searches as parameters of a helper, which splits on them. The start
# edge: the search carries a flag "a phrase may start here"; phb.may_at is
# that flag after a text, and phb.start shows it is the spec's start edge.

import Base
import ../../bend/phrase.bend as P
import ../../laws/phrase.bend as Phrase

# Logic
# -----

def phb.IfF(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# a premise False == True proves anything
def phb.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : phb.IfF(_, G)
  Unit{}

# a lazy `or` whose rest is True is True
def phb.or_rest(y: Bool, f: Unit -> Bool, e: {f(Unit{}) == True{} : Bool}) -> {P.pm.or(y, f) == True{} : Bool}:
  match y:
    case True{}:
      {==}
    case False{}:
      e

# a Bool `or` whose right side is True is True
def phb.or_r(y: Bool) -> {Bool.or(y, True{}) == True{} : Bool}:
  match y:
    case True{}:
      {==}
    case False{}:
      {==}

def phb.and_t(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      phb.absurd({False{} == True{} : Bool}, ea)

# a lazy `or` is the Bool `or`
def phb.or_lazy(a: Bool, b: Bool) -> {P.pm.or(a, u => b) == Bool.or(a, b) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Chars
# -----

def phb.none(cs: List<&2, Char>, +v: U32) -> {P.none_of(cs, Chr{v}) == Phrase.sp_none(cs, v) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case c <> +t:
      match c:
        case Chr{+w}:
          %Equal.sym(Bool, P.none_of(t, Chr{v}), Phrase.sp_none(t, v), phb.none(t, v)) : {Bool.and(Bool.not(Char.is_eq(Chr{w}, Chr{v})), _) == Phrase.sp_none(Chr{w} <> t, v) : Bool}
          {==}

# the code's class test is the spec's
def phb.cls(k: P.Cls, x: Char) -> {P.is1(k, x) == Phrase.sp_cls(k, x) : Bool}:
  match k:
    case P.CIn{lo, hi}:
      match x:
        case Chr{v}:
          {==}
    case P.COut{cs}:
      match x:
        case Chr{v}:
          phb.none(cs, v)

# a char of the class passes the code's test
def phb.cls_t(+k: P.Cls, +x: Char, e: {Phrase.sp_cls(k, x) == True{} : Bool}) -> {P.is1(k, x) == True{} : Bool}:
  Equal.trans(Bool, P.is1(k, x), Phrase.sp_cls(k, x), True{}, phb.cls(k, x), e)

# the spec's class test agrees with a True answer of the code's
def phb.cls_s(+k: P.Cls, +x: Char, e: {P.is1(k, x) == True{} : Bool}) -> {Phrase.sp_cls(k, x) == True{} : Bool}:
  Equal.trans(Bool, Phrase.sp_cls(k, x), P.is1(k, x), True{}, Equal.sym(Bool, P.is1(k, x), Phrase.sp_cls(k, x), phb.cls(k, x)), e)

# the code's word test is the spec's
def phb.word(x: Char) -> {P.is_word(x) == Phrase.sp_word(x) : Bool}:
  match x:
    case Chr{v}:
      {==}

# the code's end edge is the spec's
def phb.end(e: P.Edge, s: String) -> {P.end_ok(e, s) == Phrase.sp_end_ok(e, s) : Bool}:
  match e:
    case P.EFree{}:
      {==}
    case P.EWord{}:
      match s:
        case SNil{}:
          {==}
        case SCon{x, t}:
          Equal.cong(Bool, Bool, z => Bool.not(z), P.is_word(x), Phrase.sp_word(x), phb.word(x))
    case P.EText{}:
      {==}

def phb.end_t(+e: P.Edge, +s: String, h: {Phrase.sp_end_ok(e, s) == True{} : Bool}) -> {P.end_ok(e, s) == True{} : Bool}:
  Equal.trans(Bool, P.end_ok(e, s), Phrase.sp_end_ok(e, s), True{}, phb.end(e, s), h)

def phb.end_s(+e: P.Edge, +s: String, h: {P.end_ok(e, s) == True{} : Bool}) -> {Phrase.sp_end_ok(e, s) == True{} : Bool}:
  Equal.trans(Bool, Phrase.sp_end_ok(e, s), P.end_ok(e, s), True{}, Equal.sym(Bool, P.end_ok(e, s), Phrase.sp_end_ok(e, s), phb.end(e, s)), h)

# Prefix test, complete
# ---------------------

def phb.CP(u: String, its: List<&2, P.It>, rest: String, end: P.Edge, b: Bool) -> Type:
  match b:
    case True{}:
      {P.pm(String.append(u, rest), its, end) == True{} : Bool}
    case False{}:
      Unit

# no items: a text the end edge holds for passes
def phb.nil(s: String, +end: P.Edge, he: {Phrase.sp_end_ok(end, s) == True{} : Bool}) -> {P.pm(s, Nil{}, end) == True{} : Bool}:
  match s:
    case SNil{}:
      phb.end_t(end, SNil{}, he)
    case SCon{+x, +t}:
      phb.end_t(end, SCon{x, t}, he)

# an optional item the text skips: a text that passes the rest passes
def phb.opt_skip(s: String, c: P.Cls, k: List<&2, P.It>, +end: P.Edge, e: {P.pm(s, k, end) == True{} : Bool}) -> {P.pm(s, P.Opt{c} <> k, end) == True{} : Bool}:
  match s:
    case SNil{}:
      e
    case SCon{+x, +t}:
      %Equal.sym(Bool, P.pm(SCon{x, t}, k, end), True{}, e) : {P.pm.or(_, u => P.pm.and(P.is1(c, x), v => P.pm(t, k, end))) == True{} : Bool}
      {==}

# a star the empty text skips: a text that passes the rest passes
def phb.star_skip(s: String, c: P.Cls, k: List<&2, P.It>, +end: P.Edge, e: {P.pm(s, k, end) == True{} : Bool}) -> {P.pm(s, P.Star{c} <> k, end) == True{} : Bool}:
  match s:
    case SNil{}:
      e
    case SCon{+x, +t}:
      %Equal.sym(Bool, P.pm(SCon{x, t}, k, end), True{}, e) : {P.pm.or(_, u => P.pm.and(P.is1(c, x), v => P.pm(t, P.Star{c} <> k, end))) == True{} : Bool}
      {==}

def phb.cp_opt_nil(+rest: String, c: P.Cls, k: List<&2, P.It>, +end: P.Edge, b: Bool, ih: phb.CP(SNil{}, k, rest, end, b)) -> phb.CP(SNil{}, P.Opt{c} <> k, rest, end, b):
  match b:
    case True{}:
      phb.opt_skip(rest, c, k, end, ih)
    case False{}:
      Unit{}

def phb.cp_star_nil(+rest: String, c: P.Cls, k: List<&2, P.It>, +end: P.Edge, b: Bool, ih: phb.CP(SNil{}, k, rest, end, b)) -> phb.CP(SNil{}, P.Star{c} <> k, rest, end, b):
  match b:
    case True{}:
      phb.star_skip(rest, c, k, end, ih)
    case False{}:
      Unit{}

def phb.cp_one(+x: Char, +t: String, +rest: String, +c: P.Cls, k: List<&2, P.It>, +end: P.Edge, a: Bool, ea: {Phrase.sp_cls(c, x) == a : Bool}, b: Bool, ih: phb.CP(t, k, rest, end, b)) -> phb.CP(SCon{x, t}, P.One{c} <> k, rest, end, Bool.and(a, b)):
  match a:
    case True{}:
      match b:
        case True{}:
          %Equal.sym(Bool, P.is1(c, x), True{}, phb.cls_t(c, x, ea)) : {P.pm.and(_, u => P.pm(String.append(t, rest), k, end)) == True{} : Bool}
          ih
        case False{}:
          Unit{}
    case False{}:
      Unit{}

def phb.cp_opt(+x: Char, +t: String, +rest: String, +c: P.Cls, +k: List<&2, P.It>, +end: P.Edge, b1: Bool, ih1: phb.CP(SCon{x, t}, k, rest, end, b1), a: Bool, ea: {Phrase.sp_cls(c, x) == a : Bool}, b3: Bool, ih3: phb.CP(t, k, rest, end, b3)) -> phb.CP(SCon{x, t}, P.Opt{c} <> k, rest, end, Bool.or(b1, Bool.and(a, b3))):
  match b1:
    case True{}:
      phb.opt_skip(SCon{x, String.append(t, rest)}, c, k, end, ih1)
    case False{}:
      match a:
        case True{}:
          match b3:
            case True{}:
              %Equal.sym(Bool, P.is1(c, x), True{}, phb.cls_t(c, x, ea)) : {P.pm.or(P.pm(SCon{x, String.append(t, rest)}, k, end), u => P.pm.and(_, v => P.pm(String.append(t, rest), k, end))) == True{} : Bool}
              phb.or_rest(P.pm(SCon{x, String.append(t, rest)}, k, end), u => P.pm.and(True{}, v => P.pm(String.append(t, rest), k, end)), ih3)
            case False{}:
              Unit{}
        case False{}:
          Unit{}

def phb.cp_star(+x: Char, +t: String, +rest: String, +c: P.Cls, +k: List<&2, P.It>, +end: P.Edge, b1: Bool, ih1: phb.CP(SCon{x, t}, k, rest, end, b1), a: Bool, ea: {Phrase.sp_cls(c, x) == a : Bool}, b3: Bool, ih3: phb.CP(t, P.Star{c} <> k, rest, end, b3)) -> phb.CP(SCon{x, t}, P.Star{c} <> k, rest, end, Bool.or(b1, Bool.and(a, b3))):
  match b1:
    case True{}:
      phb.star_skip(SCon{x, String.append(t, rest)}, c, k, end, ih1)
    case False{}:
      match a:
        case True{}:
          match b3:
            case True{}:
              %Equal.sym(Bool, P.is1(c, x), True{}, phb.cls_t(c, x, ea)) : {P.pm.or(P.pm(SCon{x, String.append(t, rest)}, k, end), u => P.pm.and(_, v => P.pm(String.append(t, rest), P.Star{c} <> k, end))) == True{} : Bool}
              phb.or_rest(P.pm(SCon{x, String.append(t, rest)}, k, end), u => P.pm.and(True{}, v => P.pm(String.append(t, rest), P.Star{c} <> k, end)), ih3)
            case False{}:
              Unit{}
        case False{}:
          Unit{}

# whatever the spec answers for u, the code's prefix test agrees when True
def phb.cp(u: String, its: List<&2, P.It>, +rest: String, +end: P.Edge, +he: {Phrase.sp_end_ok(end, rest) == True{} : Bool}) -> phb.CP(u, its, rest, end, Phrase.sp_lang(u, its)):
  match u:
    case SNil{}:
      match its:
        case Nil{}:
          phb.nil(rest, end, he)
        case i <> +k:
          match i:
            case P.One{c}:
              Unit{}
            case P.Opt{+c}:
              phb.cp_opt_nil(rest, c, k, end, Phrase.sp_lang(SNil{}, k), phb.cp(SNil{}, k, rest, end, he))
            case P.Star{+c}:
              phb.cp_star_nil(rest, c, k, end, Phrase.sp_lang(SNil{}, k), phb.cp(SNil{}, k, rest, end, he))
    case SCon{+x, +t}:
      match its:
        case Nil{}:
          Unit{}
        case i <> +k:
          match i:
            case P.One{+c}:
              phb.cp_one(x, t, rest, c, k, end, Phrase.sp_cls(c, x), {==}, Phrase.sp_lang(t, k), phb.cp(t, k, rest, end, he))
            case P.Opt{+c}:
              phb.cp_opt(x, t, rest, c, k, end, Phrase.sp_lang(SCon{x, t}, k), phb.cp(SCon{x, t}, k, rest, end, he), Phrase.sp_cls(c, x), {==}, Phrase.sp_lang(t, k), phb.cp(t, k, rest, end, he))
            case P.Star{+c}:
              phb.cp_star(x, t, rest, c, k, end, Phrase.sp_lang(SCon{x, t}, k), phb.cp(SCon{x, t}, k, rest, end, he), Phrase.sp_cls(c, x), {==}, Phrase.sp_lang(t, P.Star{c} <> k), phb.cp(t, P.Star{c} <> k, rest, end, he))

# Prefix test, sound
# ------------------

def phb.SP(s: String, its: List<&2, P.It>, end: P.Edge, b: Bool) -> Type:
  match b:
    case True{}:
      Sigma<&1, &1, String, u => Sigma<&1, &1, String, r => {s == String.append(u, r) : String} & ({Phrase.sp_lang(u, its) == True{} : Bool} & {Phrase.sp_end_ok(end, r) == True{} : Bool})>>
    case False{}:
      Unit

# a part that matches the rest of the items matches with an optional item
# before
def phb.lang_opt(u: String, +c: P.Cls, +k: List<&2, P.It>, e: {Phrase.sp_lang(u, k) == True{} : Bool}) -> {Phrase.sp_lang(u, P.Opt{c} <> k) == True{} : Bool}:
  match u:
    case SNil{}:
      e
    case SCon{+y, +w}:
      %Equal.sym(Bool, Phrase.sp_lang(SCon{y, w}, k), True{}, e) : {Bool.or(_, Bool.and(Phrase.sp_cls(c, y), Phrase.sp_lang(w, k))) == True{} : Bool}
      {==}

# a part that matches the rest of the items matches with a star before
def phb.lang_star(u: String, +c: P.Cls, +k: List<&2, P.It>, e: {Phrase.sp_lang(u, k) == True{} : Bool}) -> {Phrase.sp_lang(u, P.Star{c} <> k) == True{} : Bool}:
  match u:
    case SNil{}:
      e
    case SCon{+y, +w}:
      %Equal.sym(Bool, Phrase.sp_lang(SCon{y, w}, k), True{}, e) : {Bool.or(_, Bool.and(Phrase.sp_cls(c, y), Phrase.sp_lang(w, P.Star{c} <> k))) == True{} : Bool}
      {==}

# the empty text with no items: the end edge holds for the empty rest
def phb.sp_end_nil(end: P.Edge) -> phb.SP(SNil{}, Nil{}, end, P.end_ok(end, SNil{})):
  match end:
    case P.EFree{}:
      (SNil{}, (SNil{}, ({==}, ({==}, {==}))))
    case P.EWord{}:
      (SNil{}, (SNil{}, ({==}, ({==}, {==}))))
    case P.EText{}:
      (SNil{}, (SNil{}, ({==}, ({==}, {==}))))

def phb.sp_opt_skip(-s: String, +c: P.Cls, +k: List<&2, P.It>, -end: P.Edge, b: Bool, ih: phb.SP(s, k, end, b)) -> phb.SP(s, P.Opt{c} <> k, end, b):
  match b:
    case True{}:
      (+u, (+r, (e, (l, he)))) = ih
      (u, (r, (e, (phb.lang_opt(u, c, k, l), he))))
    case False{}:
      Unit{}

def phb.sp_star_skip(-s: String, +c: P.Cls, +k: List<&2, P.It>, -end: P.Edge, b: Bool, ih: phb.SP(s, k, end, b)) -> phb.SP(s, P.Star{c} <> k, end, b):
  match b:
    case True{}:
      (+u, (+r, (e, (l, he)))) = ih
      (u, (r, (e, (phb.lang_star(u, c, k, l), he))))
    case False{}:
      Unit{}

# on the empty text, a True prefix test has its part
def phb.sp_nil(its: List<&2, P.It>, +end: P.Edge) -> phb.SP(SNil{}, its, end, P.pm(SNil{}, its, end)):
  match its:
    case Nil{}:
      phb.sp_end_nil(end)
    case i <> +k:
      match i:
        case P.One{c}:
          Unit{}
        case P.Opt{+c}:
          phb.sp_opt_skip(SNil{}, c, k, end, P.pm(SNil{}, k, end), phb.sp_nil(k, end))
        case P.Star{+c}:
          phb.sp_star_skip(SNil{}, c, k, end, P.pm(SNil{}, k, end), phb.sp_nil(k, end))

# no items: the part is empty, the rest is the text
def phb.sp_end(+s: String, +end: P.Edge, b: Bool, eb: {P.end_ok(end, s) == b : Bool}) -> phb.SP(s, Nil{}, end, b):
  match b:
    case True{}:
      (SNil{}, (s, ({==}, ({==}, phb.end_s(end, s, eb)))))
    case False{}:
      Unit{}

def phb.sp_one(+x: Char, -t: String, +c: P.Cls, -k: List<&2, P.It>, -end: P.Edge, a: Bool, ea: {P.is1(c, x) == a : Bool}, b: Bool, ih: phb.SP(t, k, end, b)) -> phb.SP(SCon{x, t}, P.One{c} <> k, end, P.pm.and(a, v => b)):
  match a:
    case True{}:
      match b:
        case True{}:
          (+u, (+r, (e, (l, he)))) = ih
          +ec = phb.cls_s(c, x, ea)
          (SCon{x, u}, (r, (Equal.cong(String, String, z => SCon{x, z}, t, String.append(u, r), e), (phb.and_t(Phrase.sp_cls(c, x), Phrase.sp_lang(u, k), ec, l), he))))
        case False{}:
          Unit{}
    case False{}:
      Unit{}

def phb.sp_opt(+x: Char, -t: String, +c: P.Cls, +k: List<&2, P.It>, -end: P.Edge, b1: Bool, ih1: phb.SP(SCon{x, t}, k, end, b1), a: Bool, ea: {P.is1(c, x) == a : Bool}, b3: Bool, ih3: phb.SP(t, k, end, b3)) -> phb.SP(SCon{x, t}, P.Opt{c} <> k, end, P.pm.or(b1, w => P.pm.and(a, v => b3))):
  match b1:
    case True{}:
      (+u, (+r, (e, (l, he)))) = ih1
      (u, (r, (e, (phb.lang_opt(u, c, k, l), he))))
    case False{}:
      match a:
        case True{}:
          match b3:
            case True{}:
              (+u, (+r, (e, (l, he)))) = ih3
              +ec = phb.cls_s(c, x, ea)
              +y = Phrase.sp_lang(SCon{x, u}, k)
              +el = Equal.trans(Bool, Bool.or(y, Bool.and(Phrase.sp_cls(c, x), Phrase.sp_lang(u, k))), Bool.or(y, True{}), True{}, Equal.cong(Bool, Bool, z => Bool.or(y, z), Bool.and(Phrase.sp_cls(c, x), Phrase.sp_lang(u, k)), True{}, phb.and_t(Phrase.sp_cls(c, x), Phrase.sp_lang(u, k), ec, l)), phb.or_r(y))
              (SCon{x, u}, (r, (Equal.cong(String, String, z => SCon{x, z}, t, String.append(u, r), e), (el, he))))
            case False{}:
              Unit{}
        case False{}:
          Unit{}

def phb.sp_star(+x: Char, -t: String, +c: P.Cls, +k: List<&2, P.It>, -end: P.Edge, b1: Bool, ih1: phb.SP(SCon{x, t}, k, end, b1), a: Bool, ea: {P.is1(c, x) == a : Bool}, b3: Bool, ih3: phb.SP(t, P.Star{c} <> k, end, b3)) -> phb.SP(SCon{x, t}, P.Star{c} <> k, end, P.pm.or(b1, w => P.pm.and(a, v => b3))):
  match b1:
    case True{}:
      (+u, (+r, (e, (l, he)))) = ih1
      (u, (r, (e, (phb.lang_star(u, c, k, l), he))))
    case False{}:
      match a:
        case True{}:
          match b3:
            case True{}:
              (+u, (+r, (e, (l, he)))) = ih3
              +ec = phb.cls_s(c, x, ea)
              +y = Phrase.sp_lang(SCon{x, u}, k)
              +el = Equal.trans(Bool, Bool.or(y, Bool.and(Phrase.sp_cls(c, x), Phrase.sp_lang(u, P.Star{c} <> k))), Bool.or(y, True{}), True{}, Equal.cong(Bool, Bool, z => Bool.or(y, z), Bool.and(Phrase.sp_cls(c, x), Phrase.sp_lang(u, P.Star{c} <> k)), True{}, phb.and_t(Phrase.sp_cls(c, x), Phrase.sp_lang(u, P.Star{c} <> k), ec, l)), phb.or_r(y))
              (SCon{x, u}, (r, (Equal.cong(String, String, z => SCon{x, z}, t, String.append(u, r), e), (el, he))))
            case False{}:
              Unit{}
        case False{}:
          Unit{}

# whatever the code's prefix test answers for s, a True answer has a part
def phb.sp(s: String, +its: List<&2, P.It>, +end: P.Edge) -> phb.SP(s, its, end, P.pm(s, its, end)):
  match s:
    case SNil{}:
      phb.sp_nil(its, end)
    case SCon{+x, +t}:
      match its:
        case Nil{}:
          phb.sp_end(SCon{x, t}, end, P.end_ok(end, SCon{x, t}), {==})
        case i <> +k:
          match i:
            case P.One{+c}:
              phb.sp_one(x, t, c, k, end, P.is1(c, x), {==}, P.pm(t, k, end), phb.sp(t, k, end))
            case P.Opt{+c}:
              phb.sp_opt(x, t, c, k, end, P.pm(SCon{x, t}, k, end), phb.sp(SCon{x, t}, k, end), P.is1(c, x), {==}, P.pm(t, k, end), phb.sp(t, k, end))
            case P.Star{+c}:
              phb.sp_star(x, t, c, k, end, P.pm(SCon{x, t}, k, end), phb.sp(SCon{x, t}, k, end), P.is1(c, x), {==}, P.pm(t, P.Star{c} <> k, end), phb.sp(t, P.Star{c} <> k, end))

# The start edge
# --------------

# the search's flag after the text a, from the flag m before it
def phb.may_at(a: String, +st: P.Edge, m: Bool) -> Bool:
  match a:
    case SNil{}:
      m
    case SCon{x, t}:
      phb.may_at(t, st, P.step(st, x))

def phb.free_all(a: String) -> {phb.may_at(a, P.EFree{}, True{}) == True{} : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{x, t}:
      phb.free_all(t)

def phb.text_false(a: String) -> {phb.may_at(a, P.EText{}, False{}) == False{} : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{x, t}:
      phb.text_false(t)

# after x then t, the flag of a whole word is whether the last char is no
# word char
def phb.word_at(t: String, +x: Char) -> {phb.may_at(t, P.EWord{}, Bool.not(P.is_word(x))) == Phrase.sp_last_free(SCon{x, t}) : Bool}:
  match t:
    case SNil{}:
      Equal.cong(Bool, Bool, z => Bool.not(z), P.is_word(x), Phrase.sp_word(x), phb.word(x))
    case SCon{+y, w}:
      phb.word_at(w, y)

# the flag after a text a, from the start, is the spec's start edge
def phb.start(st: P.Edge, a: String) -> {phb.may_at(a, st, True{}) == Phrase.sp_start_ok(st, a) : Bool}:
  match st:
    case P.EFree{}:
      phb.free_all(a)
    case P.EWord{}:
      match a:
        case SNil{}:
          {==}
        case SCon{+x, t}:
          phb.word_at(t, x)
    case P.EText{}:
      match a:
        case SNil{}:
          {==}
        case SCon{x, t}:
          phb.text_false(t)

# Search, complete
# ----------------

# a text that passes the prefix test, where the flag is True, is found
def phb.here(m: Bool, s: String, +st: P.Edge, +its: List<&2, P.It>, +end: P.Edge, hm: {m == True{} : Bool}, e: {P.pm(s, its, end) == True{} : Bool}) -> {P.occ(s, st, its, end, m) == True{} : Bool}:
  match m:
    case True{}:
      match s:
        case SNil{}:
          e
        case SCon{+x, +t}:
          %Equal.sym(Bool, P.pm(SCon{x, t}, its, end), True{}, e) : {P.pm.or(_, v => P.occ(t, st, its, end, P.step(st, x))) == True{} : Bool}
          {==}
    case False{}:
      phb.absurd({P.occ(s, st, its, end, False{}) == True{} : Bool}, hm)

# a text that passes the prefix test after any text a, where the flag after
# a is True, is found
def phb.oc(a: String, +s: String, +st: P.Edge, +its: List<&2, P.It>, +end: P.Edge, m: Bool, hm: {phb.may_at(a, st, m) == True{} : Bool}, e: {P.pm(s, its, end) == True{} : Bool}) -> {P.occ(String.append(a, s), st, its, end, m) == True{} : Bool}:
  match a:
    case SNil{}:
      phb.here(m, s, st, its, end, hm, e)
    case SCon{+y, +w}:
      phb.or_rest(P.pm.and(m, u => P.pm(SCon{y, String.append(w, s)}, its, end)), v => P.occ(String.append(w, s), st, its, end, P.step(st, y)), phb.oc(w, s, st, its, end, P.step(st, y), hm, e))

# Search, sound
# -------------

def phb.OSP(s: String, st: P.Edge, its: List<&2, P.It>, end: P.Edge, m: Bool, b: Bool) -> Type:
  match b:
    case True{}:
      Sigma<&1, &1, String, a => Sigma<&1, &1, String, u => Sigma<&1, &1, String, r => {s == String.append(a, String.append(u, r)) : String} & ({Phrase.sp_lang(u, its) == True{} : Bool} & ({phb.may_at(a, st, m) == True{} : Bool} & {Phrase.sp_end_ok(end, r) == True{} : Bool}))>>>
    case False{}:
      Unit

def phb.os_nil(m: Bool, -st: P.Edge, -its: List<&2, P.It>, -end: P.Edge, b: Bool, sp: phb.SP(SNil{}, its, end, b)) -> phb.OSP(SNil{}, st, its, end, m, P.pm.and(m, u => b)):
  match m:
    case True{}:
      match b:
        case True{}:
          (+u, (+r, (e, (l, he)))) = sp
          (SNil{}, (u, (r, (e, (l, ({==}, he))))))
        case False{}:
          Unit{}
    case False{}:
      Unit{}

def phb.os_next(+x: Char, -t: String, +st: P.Edge, -its: List<&2, P.It>, -end: P.Edge, -m: Bool, b2: Bool, ih: phb.OSP(t, st, its, end, P.step(st, x), b2)) -> phb.OSP(SCon{x, t}, st, its, end, m, b2):
  match b2:
    case True{}:
      (+a, (+u, (+r, (e, (l, (hm, he)))))) = ih
      (SCon{x, a}, (u, (r, (Equal.cong(String, String, z => SCon{x, z}, t, String.append(a, String.append(u, r)), e), (l, (hm, he))))))
    case False{}:
      Unit{}

def phb.os_con(+x: Char, -t: String, +st: P.Edge, -its: List<&2, P.It>, -end: P.Edge, m: Bool, b1: Bool, sp1: phb.SP(SCon{x, t}, its, end, b1), b2: Bool, ih: phb.OSP(t, st, its, end, P.step(st, x), b2)) -> phb.OSP(SCon{x, t}, st, its, end, m, P.pm.or(P.pm.and(m, u => b1), v => b2)):
  match m:
    case True{}:
      match b1:
        case True{}:
          (+u, (+r, (e, (l, he)))) = sp1
          (SNil{}, (u, (r, (e, (l, ({==}, he))))))
        case False{}:
          phb.os_next(x, t, st, its, end, True{}, b2, ih)
    case False{}:
      phb.os_next(x, t, st, its, end, False{}, b2, ih)

# whatever the code's search answers for s from the flag m, a True answer
# has its parts
def phb.os(s: String, +st: P.Edge, +its: List<&2, P.It>, +end: P.Edge, m: Bool) -> phb.OSP(s, st, its, end, m, P.occ(s, st, its, end, m)):
  match s:
    case SNil{}:
      phb.os_nil(m, st, its, end, P.pm(SNil{}, its, end), phb.sp(SNil{}, its, end))
    case SCon{+x, +t}:
      phb.os_con(x, t, st, its, end, m, P.pm(SCon{x, t}, its, end), phb.sp(SCon{x, t}, its, end), P.occ(t, st, its, end, P.step(st, x)), phb.os(t, st, its, end, P.step(st, x)))

# the law's form of a found phrase
def phb.SSP(s: String, st: P.Edge, its: List<&2, P.It>, en: P.Edge, b: Bool) -> Type:
  match b:
    case True{}:
      Sigma<&1, &1, String, a => Sigma<&1, &1, String, u => Sigma<&1, &1, String, r => {s == String.append(a, String.append(u, r)) : String} & ({Phrase.sp_lang(u, its) == True{} : Bool} & ({Phrase.sp_start_ok(st, a) == True{} : Bool} & {Phrase.sp_end_ok(en, r) == True{} : Bool}))>>>
    case False{}:
      Unit

def phb.os_fin(-s: String, +st: P.Edge, -its: List<&2, P.It>, -en: P.Edge, b: Bool, v: phb.OSP(s, st, its, en, True{}, b)) -> phb.SSP(s, st, its, en, b):
  match b:
    case True{}:
      (+a, (+u, (+r, (e, (l, (hm, he)))))) = v
      (a, (u, (r, (e, (l, (Equal.trans(Bool, Phrase.sp_start_ok(st, a), phb.may_at(a, st, True{}), True{}, Equal.sym(Bool, phb.may_at(a, st, True{}), Phrase.sp_start_ok(st, a), phb.start(st, a)), hm), he))))))
    case False{}:
      Unit{}

# A list of phrases
# -----------------

# the code's lazy search of a list is the spec's
def phb.any(+s: String, phs: List<&2, P.Ph>) -> {P.any(s, phs) == Phrase.sp_any(s, phs) : Bool}:
  match phs:
    case Nil{}:
      {==}
    case +p <> +more:
      +f = P.found(s, p)
      +e1 = Equal.cong(Bool, Bool, z => P.pm.or(f, u => z), P.any(s, more), Phrase.sp_any(s, more), phb.any(s, more))
      Equal.trans(Bool, P.pm.or(f, u => P.any(s, more)), P.pm.or(f, u => Phrase.sp_any(s, more)), Bool.or(f, Phrase.sp_any(s, more)), e1, phb.or_lazy(f, Phrase.sp_any(s, more)))
