# eukhe: lemmas shared by the proofs of area text_pat. Each search law
# is first proven without its premise, for the search's own answer b:
# when b is True the claim holds, when False there is nothing to show
# (tpb.CP, tpb.SP, tpb.OSP). The induction follows the search itself
# (the text first, then the items), and each step names the answers of
# its sub-searches as parameters of a helper, which splits on them.

import Base
import ../../bend/text_pat.bend as Tp
import ../../laws/base.bend as LawsBase
import ../../laws/text_pat.bend as TextPat

# Logic
# -----

def tpb.IfF(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# a premise False == True proves anything
def tpb.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : tpb.IfF(_, G)
  Unit{}

# a lazy `or` whose rest is True is True
def tpb.or_rest(y: Bool, f: Unit -> Bool, e: {f(Unit{}) == True{} : Bool}) -> {Tp.pm.or(y, f) == True{} : Bool}:
  match y:
    case True{}:
      {==}
    case False{}:
      e

# a Bool `or` whose right side is True is True
def tpb.or_r(y: Bool) -> {Bool.or(y, True{}) == True{} : Bool}:
  match y:
    case True{}:
      {==}
    case False{}:
      {==}

def tpb.and_t(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      tpb.absurd({False{} == True{} : Bool}, ea)

def tpb.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      tpb.absurd({False{} == True{} : Bool}, e)

def tpb.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      tpb.absurd({b == True{} : Bool}, e)

# Classes
# -------

# the code's class test is the spec's
def tpb.cls(k: Tp.Cls, x: Char) -> {Tp.is1(k, x) == TextPat.sp_cls(k, x) : Bool}:
  match k:
    case Tp.CLit{c}:
      match c x:
        case Chr{u} Chr{v}:
          {==}
    case Tp.CAny{}:
      match x:
        case Chr{v}:
          {==}
    case Tp.CDig{}:
      match x:
        case Chr{v}:
          {==}
    case Tp.CDigC{}:
      match x:
        case Chr{v}:
          {==}
    case Tp.CSp{}:
      match x:
        case Chr{v}:
          {==}

# a char of the class passes the code's test
def tpb.cls_t(+k: Tp.Cls, +x: Char, e: {TextPat.sp_cls(k, x) == True{} : Bool}) -> {Tp.is1(k, x) == True{} : Bool}:
  Equal.trans(Bool, Tp.is1(k, x), TextPat.sp_cls(k, x), True{}, tpb.cls(k, x), e)

# Prefix test, complete
# ---------------------

def tpb.CP(u: String, its: List<&2, Tp.It>, rest: String, b: Bool) -> Type:
  match b:
    case True{}:
      {Tp.pm(String.append(u, rest), its) == True{} : Bool}
    case False{}:
      Unit

# no items: every text passes
def tpb.nil(s: String) -> {Tp.pm(s, Nil{}) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{x, t}:
      {==}

# a star the empty text skips: a text that passes the rest passes
def tpb.star_skip(s: String, c: Tp.Cls, k: List<&2, Tp.It>, e: {Tp.pm(s, k) == True{} : Bool}) -> {Tp.pm(s, Tp.Star{c} <> k) == True{} : Bool}:
  match s:
    case SNil{}:
      e
    case SCon{+x, +t}:
      %Equal.sym(Bool, Tp.pm(SCon{x, t}, k), True{}, e) : {Tp.pm.or(_, u => Tp.pm.and(Tp.is1(c, x), v => Tp.pm(t, Tp.Star{c} <> k))) == True{} : Bool}
      {==}

def tpb.cp_star_nil(+rest: String, c: Tp.Cls, k: List<&2, Tp.It>, b: Bool, ih: tpb.CP(SNil{}, k, rest, b)) -> tpb.CP(SNil{}, Tp.Star{c} <> k, rest, b):
  match b:
    case True{}:
      tpb.star_skip(rest, c, k, ih)
    case False{}:
      Unit{}

def tpb.cp_one(+x: Char, +t: String, +rest: String, +c: Tp.Cls, k: List<&2, Tp.It>, a: Bool, ea: {TextPat.sp_cls(c, x) == a : Bool}, b: Bool, ih: tpb.CP(t, k, rest, b)) -> tpb.CP(SCon{x, t}, Tp.One{c} <> k, rest, Bool.and(a, b)):
  match a:
    case True{}:
      match b:
        case True{}:
          %Equal.sym(Bool, Tp.is1(c, x), True{}, tpb.cls_t(c, x, ea)) : {Tp.pm.and(_, u => Tp.pm(String.append(t, rest), k)) == True{} : Bool}
          ih
        case False{}:
          Unit{}
    case False{}:
      Unit{}

def tpb.cp_star(+x: Char, +t: String, +rest: String, +c: Tp.Cls, +k: List<&2, Tp.It>, b1: Bool, ih1: tpb.CP(SCon{x, t}, k, rest, b1), a: Bool, ea: {TextPat.sp_cls(c, x) == a : Bool}, b3: Bool, ih3: tpb.CP(t, Tp.Star{c} <> k, rest, b3)) -> tpb.CP(SCon{x, t}, Tp.Star{c} <> k, rest, Bool.or(b1, Bool.and(a, b3))):
  match b1:
    case True{}:
      tpb.star_skip(SCon{x, String.append(t, rest)}, c, k, ih1)
    case False{}:
      match a:
        case True{}:
          match b3:
            case True{}:
              %Equal.sym(Bool, Tp.is1(c, x), True{}, tpb.cls_t(c, x, ea)) : {Tp.pm.or(Tp.pm(SCon{x, String.append(t, rest)}, k), u => Tp.pm.and(_, v => Tp.pm(String.append(t, rest), Tp.Star{c} <> k))) == True{} : Bool}
              tpb.or_rest(Tp.pm(SCon{x, String.append(t, rest)}, k), u => Tp.pm.and(True{}, v => Tp.pm(String.append(t, rest), Tp.Star{c} <> k)), ih3)
            case False{}:
              Unit{}
        case False{}:
          Unit{}

# whatever the spec answers for u, the code's prefix test agrees when True
def tpb.cp(u: String, its: List<&2, Tp.It>, +rest: String) -> tpb.CP(u, its, rest, TextPat.sp_lang(u, its)):
  match u:
    case SNil{}:
      match its:
        case Nil{}:
          tpb.nil(rest)
        case i <> +k:
          match i:
            case Tp.One{c}:
              Unit{}
            case Tp.Star{+c}:
              tpb.cp_star_nil(rest, c, k, TextPat.sp_lang(SNil{}, k), tpb.cp(SNil{}, k, rest))
    case SCon{+x, +t}:
      match its:
        case Nil{}:
          Unit{}
        case i <> +k:
          match i:
            case Tp.One{+c}:
              tpb.cp_one(x, t, rest, c, k, TextPat.sp_cls(c, x), {==}, TextPat.sp_lang(t, k), tpb.cp(t, k, rest))
            case Tp.Star{+c}:
              tpb.cp_star(x, t, rest, c, k, TextPat.sp_lang(SCon{x, t}, k), tpb.cp(SCon{x, t}, k, rest), TextPat.sp_cls(c, x), {==}, TextPat.sp_lang(t, Tp.Star{c} <> k), tpb.cp(t, Tp.Star{c} <> k, rest))

# Prefix test, sound
# ------------------

def tpb.SP(s: String, its: List<&2, Tp.It>, b: Bool) -> Type:
  match b:
    case True{}:
      Sigma<&1, &1, String, u => Sigma<&1, &1, String, r => {s == String.append(u, r) : String} & {TextPat.sp_lang(u, its) == True{} : Bool}>>
    case False{}:
      Unit

# on the empty text the prefix test is the spec's
def tpb.empty(its: List<&2, Tp.It>) -> {Tp.pm(SNil{}, its) == TextPat.sp_lang(SNil{}, its) : Bool}:
  match its:
    case Nil{}:
      {==}
    case i <> k:
      match i:
        case Tp.One{c}:
          {==}
        case Tp.Star{c}:
          tpb.empty(k)

def tpb.sp_empty(its: List<&2, Tp.It>, b: Bool, e: {TextPat.sp_lang(SNil{}, its) == b : Bool}) -> tpb.SP(SNil{}, its, b):
  match b:
    case True{}:
      (SNil{}, (SNil{}, ({==}, e)))
    case False{}:
      Unit{}

# a part that matches the rest of the items matches with a star before
def tpb.lang_skip(u: String, +c: Tp.Cls, +k: List<&2, Tp.It>, e: {TextPat.sp_lang(u, k) == True{} : Bool}) -> {TextPat.sp_lang(u, Tp.Star{c} <> k) == True{} : Bool}:
  match u:
    case SNil{}:
      e
    case SCon{+y, +w}:
      %Equal.sym(Bool, TextPat.sp_lang(SCon{y, w}, k), True{}, e) : {Bool.or(_, Bool.and(TextPat.sp_cls(c, y), TextPat.sp_lang(w, Tp.Star{c} <> k))) == True{} : Bool}
      {==}

def tpb.sp_one(+x: Char, -t: String, +c: Tp.Cls, -k: List<&2, Tp.It>, a: Bool, ea: {Tp.is1(c, x) == a : Bool}, b: Bool, ih: tpb.SP(t, k, b)) -> tpb.SP(SCon{x, t}, Tp.One{c} <> k, Tp.pm.and(a, v => b)):
  match a:
    case True{}:
      match b:
        case True{}:
          (+u, (+r, (e, l))) = ih
          +ec = Equal.trans(Bool, TextPat.sp_cls(c, x), Tp.is1(c, x), True{}, Equal.sym(Bool, Tp.is1(c, x), TextPat.sp_cls(c, x), tpb.cls(c, x)), ea)
          (SCon{x, u}, (r, (Equal.cong(String, String, z => SCon{x, z}, t, String.append(u, r), e), tpb.and_t(TextPat.sp_cls(c, x), TextPat.sp_lang(u, k), ec, l))))
        case False{}:
          Unit{}
    case False{}:
      Unit{}

def tpb.sp_star(+x: Char, -t: String, +c: Tp.Cls, +k: List<&2, Tp.It>, b1: Bool, ih1: tpb.SP(SCon{x, t}, k, b1), a: Bool, ea: {Tp.is1(c, x) == a : Bool}, b3: Bool, ih3: tpb.SP(t, Tp.Star{c} <> k, b3)) -> tpb.SP(SCon{x, t}, Tp.Star{c} <> k, Tp.pm.or(b1, w => Tp.pm.and(a, v => b3))):
  match b1:
    case True{}:
      (+u, (+r, (e, l))) = ih1
      (u, (r, (e, tpb.lang_skip(u, c, k, l))))
    case False{}:
      match a:
        case True{}:
          match b3:
            case True{}:
              (+u, (+r, (e, l))) = ih3
              +ec = Equal.trans(Bool, TextPat.sp_cls(c, x), Tp.is1(c, x), True{}, Equal.sym(Bool, Tp.is1(c, x), TextPat.sp_cls(c, x), tpb.cls(c, x)), ea)
              +y = TextPat.sp_lang(SCon{x, u}, k)
              +el = Equal.trans(Bool, Bool.or(y, Bool.and(TextPat.sp_cls(c, x), TextPat.sp_lang(u, Tp.Star{c} <> k))), Bool.or(y, True{}), True{}, Equal.cong(Bool, Bool, z => Bool.or(y, z), Bool.and(TextPat.sp_cls(c, x), TextPat.sp_lang(u, Tp.Star{c} <> k)), True{}, tpb.and_t(TextPat.sp_cls(c, x), TextPat.sp_lang(u, Tp.Star{c} <> k), ec, l)), tpb.or_r(y))
              (SCon{x, u}, (r, (Equal.cong(String, String, z => SCon{x, z}, t, String.append(u, r), e), el)))
            case False{}:
              Unit{}
        case False{}:
          Unit{}

# whatever the code's prefix test answers for s, a True answer has a part
def tpb.sp(s: String, +its: List<&2, Tp.It>) -> tpb.SP(s, its, Tp.pm(s, its)):
  match s:
    case SNil{}:
      tpb.sp_empty(its, Tp.pm(SNil{}, its), Equal.sym(Bool, Tp.pm(SNil{}, its), TextPat.sp_lang(SNil{}, its), tpb.empty(its)))
    case SCon{+x, +t}:
      match its:
        case Nil{}:
          (SNil{}, (SCon{x, t}, ({==}, {==})))
        case i <> +k:
          match i:
            case Tp.One{+c}:
              tpb.sp_one(x, t, c, k, Tp.is1(c, x), {==}, Tp.pm(t, k), tpb.sp(t, k))
            case Tp.Star{+c}:
              tpb.sp_star(x, t, c, k, Tp.pm(SCon{x, t}, k), tpb.sp(SCon{x, t}, k), Tp.is1(c, x), {==}, Tp.pm(t, Tp.Star{c} <> k), tpb.sp(t, Tp.Star{c} <> k))

# Search, complete
# ----------------

# a text that passes the prefix test is found
def tpb.occ_pm(s: String, +its: List<&2, Tp.It>, e: {Tp.pm(s, its) == True{} : Bool}) -> {Tp.occ(s, its) == True{} : Bool}:
  match s:
    case SNil{}:
      e
    case SCon{+x, +t}:
      %Equal.sym(Bool, Tp.pm(SCon{x, t}, its), True{}, e) : {Tp.pm.or(_, w => Tp.occ(t, its)) == True{} : Bool}
      {==}

# a part that passes the prefix test after any text a is found
def tpb.oc(a: String, +u: String, +b: String, +its: List<&2, Tp.It>, e: {Tp.pm(String.append(u, b), its) == True{} : Bool}) -> {Tp.occ(String.append(a, String.append(u, b)), its) == True{} : Bool}:
  match a:
    case SNil{}:
      tpb.occ_pm(String.append(u, b), its, e)
    case SCon{+y, +w}:
      tpb.or_rest(Tp.pm(SCon{y, String.append(w, String.append(u, b))}, its), v => Tp.occ(String.append(w, String.append(u, b)), its), tpb.oc(w, u, b, its, e))

# Search, sound
# -------------

def tpb.OSP(s: String, its: List<&2, Tp.It>, b: Bool) -> Type:
  match b:
    case True{}:
      Sigma<&1, &1, String, a => Sigma<&1, &1, String, u => Sigma<&1, &1, String, r => {s == String.append(a, String.append(u, r)) : String} & {TextPat.sp_lang(u, its) == True{} : Bool}>>>
    case False{}:
      Unit

def tpb.os_of(-s: String, -its: List<&2, Tp.It>, b: Bool, sp: tpb.SP(s, its, b)) -> tpb.OSP(s, its, b):
  match b:
    case True{}:
      (+u, (+r, (e, l))) = sp
      (SNil{}, (u, (r, (e, l))))
    case False{}:
      Unit{}

def tpb.os_con(+x: Char, -t: String, -its: List<&2, Tp.It>, b1: Bool, sp1: tpb.SP(SCon{x, t}, its, b1), b2: Bool, ih: tpb.OSP(t, its, b2)) -> tpb.OSP(SCon{x, t}, its, Tp.pm.or(b1, w => b2)):
  match b1:
    case True{}:
      (+u, (+r, (e, l))) = sp1
      (SNil{}, (u, (r, (e, l))))
    case False{}:
      match b2:
        case True{}:
          (+a, (+u, (+r, (e, l)))) = ih
          (SCon{x, a}, (u, (r, (Equal.cong(String, String, z => SCon{x, z}, t, String.append(a, String.append(u, r)), e), l))))
        case False{}:
          Unit{}

# whatever the code's search answers for s, a True answer has a part
def tpb.os(s: String, +its: List<&2, Tp.It>) -> tpb.OSP(s, its, Tp.occ(s, its)):
  match s:
    case SNil{}:
      tpb.os_of(SNil{}, its, Tp.pm(SNil{}, its), tpb.sp(SNil{}, its))
    case SCon{+x, +t}:
      tpb.os_con(x, t, its, Tp.pm(SCon{x, t}, its), tpb.sp(SCon{x, t}, its), Tp.occ(t, its), tpb.os(t, its))

# Case
# ----

def tpb.fold_at(+x: U32, u: Bool, k: Bool, l: Bool) -> {Tp.fold.at(x, u, k, l) == Chr{TextPat.sp_fold_pick(x, u, k, l)} : Char}:
  match u k l:
    case True{} _ _:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# the code's fold is the spec's
def tpb.fold(s: String) -> {Tp.fold_str(s) == TextPat.sp_fold(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          %Equal.sym(String, Tp.fold_str(t), TextPat.sp_fold(t), tpb.fold(t)) : {SCon{Tp.fold(Chr{x}), _} == SCon{Chr{TextPat.sp_fold_code(x)}, TextPat.sp_fold(t)} : String}
          %Equal.sym(Char, Tp.fold(Chr{x}), Chr{TextPat.sp_fold_code(x)}, tpb.fold_at(x, Bool.and(U32.is_le(65, x), U32.is_le(x, 90)), U32.is_eq(x, 8490), U32.is_eq(x, 383))) : {SCon{_, TextPat.sp_fold(t)} == SCon{Chr{TextPat.sp_fold_code(x)}, TextPat.sp_fold(t)} : String}
          {==}

def tpb.lower_at(+x: U32, u: Bool, k: Bool, d: Bool, rest: String) -> {Tp.lower.at(x, u, k, d, rest) == String.append(TextPat.sp_lower_pick(x, u, k, d), rest) : String}:
  match u k d:
    case True{} _ _:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# the code's lowering is the spec's
def tpb.lower(s: String) -> {Tp.lower(s) == TextPat.sp_lower(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          %Equal.sym(String, Tp.lower(t), TextPat.sp_lower(t), tpb.lower(t)) : {Tp.lower.at(x, Bool.and(U32.is_le(65, x), U32.is_le(x, 90)), U32.is_eq(x, 8490), U32.is_eq(x, 304), _) == String.append(TextPat.sp_lower_pick(x, TextPat.sp_in(x, 65, 90), U32.is_eq(x, 8490), U32.is_eq(x, 304)), TextPat.sp_lower(t)) : String}
          tpb.lower_at(x, Bool.and(U32.is_le(65, x), U32.is_le(x, 90)), U32.is_eq(x, 8490), U32.is_eq(x, 304), TextPat.sp_lower(t))

# a lazy `or` is the Bool `or`
def tpb.or_lazy(a: Bool, b: Bool) -> {Tp.pm.or(a, u => b) == Bool.or(a, b) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def tpb.or_false(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Search over a table
# -------------------

def tpb.found(a: Bool, s: String, its: List<&2, Tp.It>) -> {Tp.found(a, s, its) == TextPat.sp_found(a, s, its) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def tpb.alts(+a: Bool, +s: String, alts: List<&2, List<&2, Tp.It>>) -> {Tp.hit.go(a, s, alts) == TextPat.sp_alts(a, s, alts) : Bool}:
  match alts:
    case Nil{}:
      {==}
    case +its <> +more:
      +f = Tp.found(a, s, its)
      +e1 = Equal.cong(Bool, Bool, z => Tp.pm.or(f, u => z), Tp.hit.go(a, s, more), TextPat.sp_alts(a, s, more), tpb.alts(a, s, more))
      +e2 = Equal.trans(Bool, Tp.pm.or(f, u => Tp.hit.go(a, s, more)), Tp.pm.or(f, u => TextPat.sp_alts(a, s, more)), Bool.or(f, TextPat.sp_alts(a, s, more)), e1, tpb.or_lazy(f, TextPat.sp_alts(a, s, more)))
      Equal.trans(Bool, Tp.pm.or(f, u => Tp.hit.go(a, s, more)), Bool.or(f, TextPat.sp_alts(a, s, more)), Bool.or(TextPat.sp_found(a, s, its), TextPat.sp_alts(a, s, more)), e2, Equal.cong(Bool, Bool, z => Bool.or(z, TextPat.sp_alts(a, s, more)), f, TextPat.sp_found(a, s, its), tpb.found(a, s, its)))

# the code's lazy search of a table is the spec's (text_pat_any)
def tpb.any(+s: String, ps: List<&2, Tp.Pat>) -> {Tp.any(s, ps) == TextPat.sp_any(s, ps) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case p <> +more:
      match p:
        case Tp.Pat{+a, +alts}:
          +h = Tp.hit.go(a, s, alts)
          +e1 = Equal.cong(Bool, Bool, z => Tp.pm.or(h, u => z), Tp.any(s, more), TextPat.sp_any(s, more), tpb.any(s, more))
          +e2 = Equal.trans(Bool, Tp.pm.or(h, u => Tp.any(s, more)), Tp.pm.or(h, u => TextPat.sp_any(s, more)), Bool.or(h, TextPat.sp_any(s, more)), e1, tpb.or_lazy(h, TextPat.sp_any(s, more)))
          Equal.trans(Bool, Tp.pm.or(h, u => Tp.any(s, more)), Bool.or(h, TextPat.sp_any(s, more)), Bool.or(TextPat.sp_alts(a, s, alts), TextPat.sp_any(s, more)), e2, Equal.cong(Bool, Bool, z => Bool.or(z, TextPat.sp_any(s, more)), h, TextPat.sp_alts(a, s, alts), tpb.alts(a, s, alts)))

# one pattern is the spec's table of one (text_pat_hit)
def tpb.hit(+s: String, +p: Tp.Pat) -> {Tp.hit(s, p) == TextPat.sp_any(s, [p]) : Bool}:
  match p:
    case Tp.Pat{+a, +alts}:
      Equal.trans(Bool, Tp.hit.go(a, s, alts), TextPat.sp_alts(a, s, alts), Bool.or(TextPat.sp_alts(a, s, alts), False{}), tpb.alts(a, s, alts), Equal.sym(Bool, Bool.or(TextPat.sp_alts(a, s, alts), False{}), TextPat.sp_alts(a, s, alts), tpb.or_false(TextPat.sp_alts(a, s, alts))))

