# privacy (spec): the version context of a candidate position of the
# outbound scrubber (spec/README.md H7; the `ctx` of take4 in
# spec/harness/privacy.bend), restated without the code
# (bend/privacy/context.bend): an IPv4 written in a version's context is a
# version, so it is no address. A spec: the shipped code never calls it.
#
# S7: the line of a position is the text before it after its last
#     newline. It reads as a version's context exactly when:
#     - the line, its trailing blanks (space, tab) dropped, ends with a
#       requirement operator: `==`, `>=`, `<=`, `~=`, `!=`, `^` or `~`; or
#     - the line, its trailing blanks, quotes (`"`, `'`), `=`, `:`, `(`,
#       `<`, `>`, `[` and `,` dropped, ends with a word (its run of ASCII
#       letters, digits and `_`, a letter in any case) that holds `version`
#       or is `ver`, `v`, `release` or `tag`.
#     Nothing else is one: a plain assignment (`host = `, `server_ip = `,
#     `"ip" = `) is no version's context, so the IPv4 after it is scrubbed.
#
# The spec reads the line from its end: a text reversed, and so each
# spelling below is matched reversed.

import Base

# What the context asks of a char
# -------------------------------

# a blank (space, tab); a sign (`=` `>` `<` `~` `!` `^`); a mark (`"`
# `'` `:` `(` `[` `,`); a word char (an ASCII letter, lowercase, a digit,
# `_`); a newline; anything else
type VKind is Data:
  VBlank{}
  VSign{c: Char}
  VMark{}
  VWord{c: Char}
  VBreak{}
  VOther{}

def vwhen(hit: Bool, y: VKind, miss: VKind) -> VKind:
  match hit:
    case True{}:
      y
    case False{}:
      miss

# lo <= x <= hi
def vin(+x: U32, lo: U32, hi: U32) -> Bool:
  Bool.and(U32.is_ge(x, lo), U32.is_le(x, hi))

# the kind of a char, by its code
def vkind(c: Char) -> VKind:
  match c:
    case Chr{+x}:
      vwhen(U32.is_eq(x, 32), VBlank{}, vwhen(U32.is_eq(x, 9), VBlank{}, vwhen(U32.is_eq(x, 61), VSign{'='}, vwhen(U32.is_eq(x, 62), VSign{'>'}, vwhen(U32.is_eq(x, 60), VSign{'<'}, vwhen(U32.is_eq(x, 126), VSign{'~'}, vwhen(U32.is_eq(x, 33), VSign{'!'}, vwhen(U32.is_eq(x, 94), VSign{'^'}, vwhen(U32.is_eq(x, 34), VMark{}, vwhen(U32.is_eq(x, 39), VMark{}, vwhen(U32.is_eq(x, 58), VMark{}, vwhen(U32.is_eq(x, 40), VMark{}, vwhen(U32.is_eq(x, 91), VMark{}, vwhen(U32.is_eq(x, 44), VMark{}, vwhen(U32.is_eq(x, 10), VBreak{}, vwhen(vin(x, 48, 57), VWord{Chr{x}}, vwhen(vin(x, 97, 122), VWord{Chr{x}}, vwhen(vin(x, 65, 90), VWord{Chr{(x + 32 : U32)}}, vwhen(U32.is_eq(x, 95), VWord{Chr{x}}, VOther{})))))))))))))))))))

# the kinds of the chars of r, in order
def vkinds(r: String) -> List<&2, VKind>:
  match r:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      vkind(c) <> vkinds(t)

# The line, read from its end
# ---------------------------

# the kinds before the first newline (of a text read from its end: the
# line of the position)
def vcut(ks: List<&2, VKind>) -> List<&2, VKind>:
  match ks:
    case Nil{}:
      Nil{}
    case k <> t:
      match k:
        case VBreak{}:
          Nil{}
        case VBlank{}:
          VBlank{} <> vcut(t)
        case VSign{c}:
          VSign{c} <> vcut(t)
        case VMark{}:
          VMark{} <> vcut(t)
        case VWord{c}:
          VWord{c} <> vcut(t)
        case VOther{}:
          VOther{} <> vcut(t)

# without its trailing blanks
def vtrim(ks: List<&2, VKind>) -> List<&2, VKind>:
  match ks:
    case Nil{}:
      Nil{}
    case k <> t:
      match k:
        case VBlank{}:
          vtrim(t)
        case VSign{c}:
          VSign{c} <> t
        case VMark{}:
          VMark{} <> t
        case VWord{c}:
          VWord{c} <> t
        case VBreak{}:
          VBreak{} <> t
        case VOther{}:
          VOther{} <> t

def vpick(b: Bool, y: List<&2, VKind>, n: List<&2, VKind>) -> List<&2, VKind>:
  match b:
    case True{}:
      y
    case False{}:
      n

# a sign dropped before a word: `=`, `<`, `>`
def vdrop_sign(+c: Char) -> Bool:
  Bool.or(Char.is_eq(c, '='), Bool.or(Char.is_eq(c, '<'), Char.is_eq(c, '>')))

# without its trailing blanks, quotes, `=`, `:`, `(`, `<`, `>`, `[`, `,`
def vstrip(ks: List<&2, VKind>) -> List<&2, VKind>:
  match ks:
    case Nil{}:
      Nil{}
    case k <> t:
      match k:
        case VBlank{}:
          vstrip(t)
        case VMark{}:
          vstrip(t)
        case VSign{+c}:
          +t2 = t
          vpick(vdrop_sign(c), vstrip(t2), VSign{c} <> t2)
        case VWord{c}:
          VWord{c} <> t
        case VBreak{}:
          VBreak{} <> t
        case VOther{}:
          VOther{} <> t

# Operators and version words
# ---------------------------

# the signs at the start of ks spell p
def vsigns(p: String, ks: List<&2, VKind>) -> Bool:
  match p:
    case SNil{}:
      True{}
    case SCon{+a, pt}:
      match ks:
        case Nil{}:
          False{}
        case k <> kt:
          match k:
            case VSign{c}:
              Bool.and(Char.is_eq(a, c), vsigns(pt, kt))
            case VBlank{}:
              False{}
            case VMark{}:
              False{}
            case VWord{c}:
              False{}
            case VBreak{}:
              False{}
            case VOther{}:
              False{}

# the requirement operators
def vops() -> List<&2, String>:
  ["==", ">=", "<=", "~=", "!=", "^", "~"]

def vop.any(ops: List<&2, String>, +ks: List<&2, VKind>) -> Bool:
  match ops:
    case Nil{}:
      False{}
    case p <> rest:
      Bool.or(vsigns(String.reverse(p), ks), vop.any(rest, ks))

# a line read from its end ends with a requirement operator
def vop(+ks: List<&2, VKind>) -> Bool:
  vop.any(vops(), ks)

# the word chars at the start of ks: the line's last word, lowercase, read
# from its end
def vword(ks: List<&2, VKind>) -> String:
  match ks:
    case Nil{}:
      SNil{}
    case k <> t:
      match k:
        case VWord{c}:
          SCon{c, vword(t)}
        case VBlank{}:
          SNil{}
        case VSign{c}:
          SNil{}
        case VMark{}:
          SNil{}
        case VBreak{}:
          SNil{}
        case VOther{}:
          SNil{}

# k is a prefix of w
def vpre(k: String, w: String) -> Bool:
  match k:
    case SNil{}:
      True{}
    case SCon{+a, kt}:
      match w:
        case SNil{}:
          False{}
        case SCon{b, wt}:
          Bool.and(Char.is_eq(a, b), vpre(kt, wt))

# k is in w
def vhas(w: String, +k: String) -> Bool:
  match w:
    case SNil{}:
      String.is_empty(k)
    case SCon{+c, +t}:
      Bool.or(vpre(k, SCon{c, t}), vhas(t, k))

# a version word, read from its end: it holds `version`, or is `ver`,
# `v`, `release` or `tag`
def vname(+w: String) -> Bool:
  Bool.or(vhas(w, String.reverse("version")), Bool.or(String.eq(w, String.reverse("ver")), Bool.or(String.eq(w, "v"), Bool.or(String.eq(w, String.reverse("release")), String.eq(w, String.reverse("tag"))))))

# The context
# -----------

# a line read from its end reads as a version's context
def vctx.of(+ks: List<&2, VKind>) -> Bool:
  Bool.or(vop(vtrim(ks)), vname(vword(vstrip(ks))))

# S7: the text before a position reads as a version's context
def vctx(before: String) -> Bool:
  vctx.of(vcut(vkinds(String.reverse(before))))
