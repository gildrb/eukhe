# privacy/context: whether the line before a candidate position of the
# outbound scrubber reads as a version's context (an IPv4 there is a
# version: bend/privacy/ip.bend). The line before it, blanks dropped, ends
# with a requirement operator (`==` `>=` `<=` `~=` `!=` `^` `~`), or,
# quotes, `=`, `:`, `(`, `<`, `>`, `[`, `,` dropped too, its last word
# (ASCII letters, digits, `_`) holds `version` or is `ver`, `v`, `release`
# or `tag`, in any case. laws/privacy/ip.bend pins it.

import Base

# lo <= x <= hi
def in(+x: U32, lo: U32, hi: U32) -> Bool:
  Bool.and(U32.is_ge(x, lo), U32.is_le(x, hi))

# a char of the line before a position, by what the context asks of it
type VSym is Data:
  Bl{}
  Eq{}
  Gt{}
  Lt{}
  Ti{}
  Ba{}
  Ca{}
  Pu{}
  Wc{c: Char}
  Nl{}
  Ot{}

def VSym.when(hit: Bool, y: VSym, miss: VSym) -> VSym:
  match hit:
    case True{}:
      y
    case False{}:
      miss

# Bl: space, tab; Eq Gt Lt Ti Ba Ca: `=` `>` `<` `~` `!` `^`; Pu: `"` `'`
# `:` `(` `[` `,`; Wc: an ASCII letter (lowercase), digit or `_`; Nl: a
# newline; Ot: the rest
def VSym.of(c: Char) -> VSym:
  match c:
    case Chr{+x}:
      VSym.when(U32.is_eq(x, 32), Bl{}, VSym.when(U32.is_eq(x, 9), Bl{}, VSym.when(U32.is_eq(x, 61), Eq{}, VSym.when(U32.is_eq(x, 62), Gt{}, VSym.when(U32.is_eq(x, 60), Lt{}, VSym.when(U32.is_eq(x, 126), Ti{}, VSym.when(U32.is_eq(x, 33), Ba{}, VSym.when(U32.is_eq(x, 94), Ca{}, VSym.when(U32.is_eq(x, 34), Pu{}, VSym.when(U32.is_eq(x, 39), Pu{}, VSym.when(U32.is_eq(x, 58), Pu{}, VSym.when(U32.is_eq(x, 40), Pu{}, VSym.when(U32.is_eq(x, 91), Pu{}, VSym.when(U32.is_eq(x, 44), Pu{}, VSym.when(U32.is_eq(x, 10), Nl{}, VSym.when(in(x, 48, 57), Wc{Chr{x}}, VSym.when(in(x, 97, 122), Wc{Chr{x}}, VSym.when(in(x, 65, 90), Wc{Chr{(x + 32 : U32)}}, VSym.when(U32.is_eq(x, 95), Wc{Chr{x}}, Ot{})))))))))))))))))))

def VSym.list(s: String) -> List<&2, VSym>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      VSym.of(c) <> VSym.list(t)

# the line before the position, last char first: up to its first newline
def line(vs: List<&2, VSym>) -> List<&2, VSym>:
  match vs:
    case Nil{}:
      Nil{}
    case y <> t:
      match y:
        case Nl{}:
          Nil{}
        case Bl{}:
          Bl{} <> line(t)
        case Eq{}:
          Eq{} <> line(t)
        case Gt{}:
          Gt{} <> line(t)
        case Lt{}:
          Lt{} <> line(t)
        case Ti{}:
          Ti{} <> line(t)
        case Ba{}:
          Ba{} <> line(t)
        case Ca{}:
          Ca{} <> line(t)
        case Pu{}:
          Pu{} <> line(t)
        case Wc{c}:
          Wc{c} <> line(t)
        case Ot{}:
          Ot{} <> line(t)

# without its trailing blanks (the line is last char first)
def blanks(vs: List<&2, VSym>) -> List<&2, VSym>:
  match vs:
    case Nil{}:
      Nil{}
    case y <> t:
      match y:
        case Bl{}:
          blanks(t)
        case Eq{}:
          Eq{} <> t
        case Gt{}:
          Gt{} <> t
        case Lt{}:
          Lt{} <> t
        case Ti{}:
          Ti{} <> t
        case Ba{}:
          Ba{} <> t
        case Ca{}:
          Ca{} <> t
        case Pu{}:
          Pu{} <> t
        case Wc{c}:
          Wc{c} <> t
        case Nl{}:
          Nl{} <> t
        case Ot{}:
          Ot{} <> t

# the line ends with `==` `>=` `<=` `~=` `!=` (last char first: `=` and
# one of `=` `>` `<` `~` `!`), `^` or `~`
def op.eq(vs: List<&2, VSym>) -> Bool:
  match vs:
    case Nil{}:
      False{}
    case y <> t:
      match y:
        case Eq{}:
          True{}
        case Gt{}:
          True{}
        case Lt{}:
          True{}
        case Ti{}:
          True{}
        case Ba{}:
          True{}
        case Bl{}:
          False{}
        case Ca{}:
          False{}
        case Pu{}:
          False{}
        case Wc{c}:
          False{}
        case Nl{}:
          False{}
        case Ot{}:
          False{}

def op(vs: List<&2, VSym>) -> Bool:
  match vs:
    case Nil{}:
      False{}
    case y <> t:
      match y:
        case Eq{}:
          op.eq(t)
        case Ca{}:
          True{}
        case Ti{}:
          True{}
        case Bl{}:
          False{}
        case Gt{}:
          False{}
        case Lt{}:
          False{}
        case Ba{}:
          False{}
        case Pu{}:
          False{}
        case Wc{c}:
          False{}
        case Nl{}:
          False{}
        case Ot{}:
          False{}

# without its trailing blanks, quotes, `=`, `:`, `(`, `<`, `>`, `[`, `,`
def punct(vs: List<&2, VSym>) -> List<&2, VSym>:
  match vs:
    case Nil{}:
      Nil{}
    case y <> t:
      match y:
        case Bl{}:
          punct(t)
        case Eq{}:
          punct(t)
        case Gt{}:
          punct(t)
        case Lt{}:
          punct(t)
        case Pu{}:
          punct(t)
        case Ti{}:
          Ti{} <> t
        case Ba{}:
          Ba{} <> t
        case Ca{}:
          Ca{} <> t
        case Wc{c}:
          Wc{c} <> t
        case Nl{}:
          Nl{} <> t
        case Ot{}:
          Ot{} <> t

# its last word, lowercase, last char first
def word(vs: List<&2, VSym>) -> String:
  match vs:
    case Nil{}:
      SNil{}
    case y <> t:
      match y:
        case Wc{c}:
          SCon{c, word(t)}
        case Bl{}:
          SNil{}
        case Eq{}:
          SNil{}
        case Gt{}:
          SNil{}
        case Lt{}:
          SNil{}
        case Ti{}:
          SNil{}
        case Ba{}:
          SNil{}
        case Ca{}:
          SNil{}
        case Pu{}:
          SNil{}
        case Nl{}:
          SNil{}
        case Ot{}:
          SNil{}

# k is a prefix of w
def starts(k: String, w: String) -> Bool:
  match k:
    case SNil{}:
      True{}
    case SCon{+a, kt}:
      match w:
        case SNil{}:
          False{}
        case SCon{b, wt}:
          Bool.and(Char.is_eq(a, b), starts(kt, wt))

# k is in w
def holds(w: String, +k: String) -> Bool:
  match w:
    case SNil{}:
      String.is_empty(k)
    case SCon{+c, +t}:
      Bool.or(starts(k, SCon{c, t}), holds(t, k))

# a version word, last char first: holds `version`, or is `ver`, `v`,
# `release` or `tag`
def vword(+w: String) -> Bool:
  Bool.or(holds(w, "noisrev"), Bool.or(String.eq(w, "rev"), Bool.or(String.eq(w, "v"), Bool.or(String.eq(w, "esaeler"), String.eq(w, "gat")))))

def vctx.go(+vs: List<&2, VSym>) -> Bool:
  Bool.or(op(vs), vword(word(punct(vs))))

# the line before the position reads as a version's context
def vctx(before: String) -> Bool:
  vctx.go(blanks(line(VSym.list(String.reverse(before)))))
