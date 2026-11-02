# privacy (spec): the outbound scrubber (privacy.anonymizeRemote,
# crates/eukhe-ai/src/privacy), restated without the code
# (bend/privacy/ip.bend, bend/privacy/token.bend): an IP address as the
# text a structured address writes, where the code reads a text symbol by
# symbol; a scrubbed and restored text as what each piece becomes, where
# the code keeps a map and asks it per value. The laws of area privacy
# (laws/privacy/) state that the code refines it. A spec: the shipped code
# never calls it (it uses the code's data types only).
#
# S1: an IPv6 is written from its groups (1 to 4 hex digits each) joined
#     by `:`, and its IPv4 (four octets joined by `.`) last: eight explicit
#     groups (an IPv4 counts two), or three to seven with one `::` between
#     the groups before it and the groups after it. One group holds a
#     decimal digit, or an IPv4 ends it.
# S2: an octet is 1 to 3 decimal digits, no leading zero, at most 255
#     (a 3-digit one starts below 2, or with 2 and then below 5, or with
#     25 and then at most 5).
# S3: an IPv6 is taken where no word char, `:` or `.` comes before it and
#     after it, and its value (its 128 bits, however it is written) is no
#     loopback `::1`, no unspecified `::`, and no IPv4 compatible
#     (`::/96`) or mapped (`::ffff:0:0/96`) whose first octet is 0, 127
#     or 255; an IPv4 where no word char or `.` comes before it, no
#     ASCII letter and `/` (a product version), and no version context;
#     after it no word char, nor `.` or `-` then an ASCII letter or digit;
#     and its first octet is not 0, 127 or 255. A word char is an ASCII
#     letter or digit, `_`, or the word mark U+00AA (Rust sends every
#     other non-ASCII char as U+00A0).
# S4: the classes PERSON, EMAIL, PHONE, IP, ID map back; KEY, CARD, IBAN
#     go one way.
# S5: a text scrubbed and restored is the text with every value of a
#     class that goes one way hidden by its one-way token: every other
#     piece comes back as it was. Scrubbed, no value is left in clear.
#     Restoring never brings a credential back.
# S6: every attempt of a failover sends the raw text: a remote attempt the
#     one scrub of it, a local attempt the text itself.

import Base
import ../../bend/privacy/ip.bend as Ip
import ../../bend/privacy/token.bend as Tk

# S1-S3: chars
# ------------

# what the grammar asks of a char: a decimal digit; a-f, A-F; `:`; `.`;
# another ASCII letter; `_` or the word mark U+00AA; `-`; anything else
type CKind is Data:
  KDec{}
  KHex{}
  KCol{}
  KDot{}
  KLet{}
  KUnd{}
  KDash{}
  KOth{}

def when(hit: Bool, y: CKind, miss: CKind) -> CKind:
  match hit:
    case True{}:
      y
    case False{}:
      miss

def code(c: Char) -> U32:
  match c:
    case Chr{x}:
      x

# lo <= x <= hi
def in(+x: U32, lo: U32, hi: U32) -> Bool:
  Bool.and(U32.is_ge(x, lo), U32.is_le(x, hi))

# the kind of a char, by its code
def kind(c: Char) -> CKind:
  match c:
    case Chr{+x}:
      when(in(x, 48, 57), KDec{}, when(in(x, 97, 102), KHex{}, when(in(x, 65, 70), KHex{}, when(U32.is_eq(x, 58), KCol{}, when(U32.is_eq(x, 46), KDot{}, when(in(x, 103, 122), KLet{}, when(in(x, 71, 90), KLet{}, when(U32.is_eq(x, 95), KUnd{}, when(U32.is_eq(x, 170), KUnd{}, when(U32.is_eq(x, 45), KDash{}, KOth{}))))))))))

# a decimal digit
def dec(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      in(x, 48, 57)

# a hex digit: a decimal digit, a-f, A-F
def hex(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(in(x, 48, 57), Bool.or(in(x, 97, 102), in(x, 65, 70)))

# an ASCII letter or digit
def k_alnum(k: CKind) -> Bool:
  match k:
    case KDec{}:
      True{}
    case KHex{}:
      True{}
    case KLet{}:
      True{}
    case KCol{}:
      False{}
    case KDot{}:
      False{}
    case KUnd{}:
      False{}
    case KDash{}:
      False{}
    case KOth{}:
      False{}

# a word char: an ASCII letter or digit, `_`, the word mark U+00AA
def k_word(k: CKind) -> Bool:
  match k:
    case KDec{}:
      True{}
    case KHex{}:
      True{}
    case KLet{}:
      True{}
    case KUnd{}:
      True{}
    case KCol{}:
      False{}
    case KDot{}:
      False{}
    case KDash{}:
      False{}
    case KOth{}:
      False{}

# no word char, `:` or `.`
def k_free(k: CKind) -> Bool:
  match k:
    case KDash{}:
      True{}
    case KOth{}:
      True{}
    case KDec{}:
      False{}
    case KHex{}:
      False{}
    case KLet{}:
      False{}
    case KUnd{}:
      False{}
    case KCol{}:
      False{}
    case KDot{}:
      False{}

# no word char or `.`
def k_edge4(k: CKind) -> Bool:
  match k:
    case KCol{}:
      True{}
    case KDash{}:
      True{}
    case KOth{}:
      True{}
    case KDec{}:
      False{}
    case KHex{}:
      False{}
    case KLet{}:
      False{}
    case KUnd{}:
      False{}
    case KDot{}:
      False{}

# no hex digit, `:` or `.`: what does not go on with an IPv6
def k_stop6(k: CKind) -> Bool:
  match k:
    case KLet{}:
      True{}
    case KUnd{}:
      True{}
    case KDash{}:
      True{}
    case KOth{}:
      True{}
    case KDec{}:
      False{}
    case KHex{}:
      False{}
    case KCol{}:
      False{}
    case KDot{}:
      False{}

# `.` or `-`
def k_sep(k: CKind) -> Bool:
  match k:
    case KDot{}:
      True{}
    case KDash{}:
      True{}
    case KDec{}:
      False{}
    case KHex{}:
      False{}
    case KCol{}:
      False{}
    case KLet{}:
      False{}
    case KUnd{}:
      False{}
    case KOth{}:
      False{}

def all_hex(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(hex(c), all_hex(t))

def all_dec(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(dec(c), all_dec(t))

def has_dec(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.or(dec(c), has_dec(t))

# the last char of s
def last(s: String) -> Maybe<&2, Char>:
  match s:
    case SNil{}:
      None{}
    case SCon{c, t}:
      match t:
        case SNil{}:
          Some{c}
        case SCon{d, u}:
          last(SCon{d, u})

# the char before the last of s
def before_last(s: String) -> Maybe<&2, Char>:
  match s:
    case SNil{}:
      None{}
    case SCon{c, t}:
      match t:
        case SNil{}:
          None{}
        case SCon{d, u}:
          match u:
            case SNil{}:
              Some{c}
            case SCon{e, v}:
              before_last(SCon{d, SCon{e, v}})

# S1, S2: what an address writes
# ------------------------------

# an octet (S2)
def octet(+o: String) -> Bool:
  match o:
    case SNil{}:
      False{}
    case SCon{+a, t1}:
      match t1:
        case SNil{}:
          dec(a)
        case SCon{+b, t2}:
          match t2:
            case SNil{}:
              Bool.and(Bool.and(dec(a), dec(b)), Bool.not(Char.is_eq(a, '0')))
            case SCon{+c, t3}:
              match t3:
                case SNil{}:
                  +x = code(a)
                  +y = code(b)
                  Bool.and(Bool.and(Bool.and(dec(a), dec(b)), Bool.and(dec(c), Bool.not(Char.is_eq(a, '0')))), Bool.or(U32.is_lt(x, 50), Bool.and(U32.is_eq(x, 50), Bool.or(U32.is_lt(y, 53), Bool.and(U32.is_eq(y, 53), U32.is_le(code(c), 53))))))
                case SCon{d, t4}:
                  False{}

def quad_ok(q: Ip.Quad) -> Bool:
  match q:
    case Ip.Quad{a, b, c, d}:
      Bool.and(Bool.and(octet(a), octet(b)), Bool.and(octet(c), octet(d)))

# an IPv4 written: its octets joined by `.`
def quad_text(q: Ip.Quad, rest: String) -> String:
  match q:
    case Ip.Quad{a, b, c, d}:
      String.append(a, SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, rest)})})})

# a group: 1 to 4 hex digits
def group(+g: String) -> Bool:
  Bool.and(all_hex(g), Bool.and(Nat.is_le(1n, String.length(g)), Nat.is_le(String.length(g), 4n)))

def groups(gs: List<&2, String>) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case g <> rest:
      Bool.and(group(g), groups(rest))

def mquad_ok(q: Maybe<&2, Ip.Quad>) -> Bool:
  match q:
    case None{}:
      True{}
    case Some{x}:
      quad_ok(x)

# the shape of an address: every group a group, its IPv4 four octets
def shaped(a: Ip.Addr) -> Bool:
  match a:
    case Ip.Full{gs, q}:
      Bool.and(groups(gs), mquad_ok(q))
    case Ip.Gap{l, r, q}:
      Bool.and(Bool.and(groups(l), groups(r)), mquad_ok(q))

# items joined by `:`, then rest
def join(xs: List<&2, String>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> more:
      match more:
        case Nil{}:
          String.append(x, rest)
        case y <> ys:
          String.append(x, SCon{':', join(y <> ys, rest)})

# the items an IPv4 adds: its text
def quad_items(q: Maybe<&2, Ip.Quad>) -> List<&2, String>:
  match q:
    case None{}:
      Nil{}
    case Some{x}:
      [quad_text(x, "")]

# an IPv6 written, then rest
def text6(a: Ip.Addr, rest: String) -> String:
  match a:
    case Ip.Full{gs, q}:
      join(List.append(&2, String, gs, quad_items(q)), rest)
    case Ip.Gap{l, r, q}:
      join(l, SCon{':', SCon{':', join(List.append(&2, String, r, quad_items(q)), rest)}})

# eight explicit groups, or three to seven around the `::` (an IPv4 is two)
def counted(a: Ip.Addr) -> Bool:
  match a:
    case Ip.Full{gs, +q}:
      Nat.is_eq(Nat.add(List.length(&2, String, gs), List.length(&2, String, List.append(&2, String, quad_items(q), quad_items(q)))), 8n)
    case Ip.Gap{l, r, +q}:
      +n = Nat.add(Nat.add(List.length(&2, String, l), List.length(&2, String, r)), List.length(&2, String, List.append(&2, String, quad_items(q), quad_items(q))))
      Bool.and(Nat.is_le(3n, n), Nat.is_le(n, 7n))

def groups_dec(gs: List<&2, String>) -> Bool:
  match gs:
    case Nil{}:
      False{}
    case g <> rest:
      Bool.or(has_dec(g), groups_dec(rest))

# a group holds a decimal digit, or an IPv4 ends it
def digit(a: Ip.Addr) -> Bool:
  match a:
    case Ip.Full{gs, q}:
      Bool.or(groups_dec(gs), Maybe.is_some(&2, Ip.Quad, q))
    case Ip.Gap{l, r, q}:
      Bool.or(Bool.or(groups_dec(l), groups_dec(r)), Maybe.is_some(&2, Ip.Quad, q))

# S3: where an address is taken
# -----------------------------

def ans(ok: Bool, n: Nat) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{n}
    case False{}:
      None{}


# what follows an IPv6 does not go on with it: no hex digit, `:` or `.`
def stops6(t: String) -> Bool:
  match t:
    case SNil{}:
      True{}
    case SCon{c, u}:
      k_stop6(kind(c))

# no word char, `:` or `.` touches an IPv6
def free(m: Maybe<&2, Char>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{c}:
      k_free(kind(c))

def first(t: String) -> Maybe<&2, Char>:
  match t:
    case SNil{}:
      None{}
    case SCon{c, u}:
      Some{c}

# S3: the value of an IPv6, its 128 bits as 32 lowercase hex digits
# -----------------------------------------------------------------

# a group as its four hex digits, lowercase
def pad(+g: String) -> String:
  String.append(String.repeat("0", Nat.sub(4n, String.length(g))), String.to_lower(g))

# groups as their hex digits, one after another
def hexs(gs: List<&2, String>) -> String:
  match gs:
    case Nil{}:
      SNil{}
    case g <> rest:
      String.append(pad(g), hexs(rest))

# a decimal number written after acc
def dval(s: String, acc: U32) -> U32:
  match s:
    case SNil{}:
      acc
    case SCon{Chr{x}, t}:
      dval(t, U32.add(U32.mul(acc, 10), U32.sub(x, 48)))

# the lowercase hex digit of a value 0 to 15
def nib(+v: U32) -> Char:
  Chr{U32.add(v, U32.add(48, U32.mul(Bool.to_u32(U32.is_ge(v, 10)), 39)))}

# a byte (0 to 255) as its two hex digits, then rest
def byte(+v: U32, rest: String) -> String:
  SCon{nib(U32.shrn(v, 4n)), SCon{nib(U32.and(v, 15)), rest}}

# an IPv4 as its eight hex digits
def hexq(q: Ip.Quad) -> String:
  match q:
    case Ip.Quad{a, b, c, d}:
      byte(dval(a, 0), byte(dval(b, 0), byte(dval(c, 0), byte(dval(d, 0), SNil{}))))

def mhexq(q: Maybe<&2, Ip.Quad>) -> String:
  match q:
    case None{}:
      SNil{}
    case Some{x}:
      hexq(x)

# the value of an address: its groups, the `::` filled with zero groups,
# then its IPv4, as hex digits
def value6(a: Ip.Addr) -> String:
  match a:
    case Ip.Full{gs, q}:
      String.append(hexs(gs), mhexq(q))
    case Ip.Gap{+l, +r, +q}:
      +n = Nat.add(Nat.add(List.length(&2, String, l), List.length(&2, String, r)), List.length(&2, String, List.append(&2, String, quad_items(q), quad_items(q))))
      String.append(hexs(List.append(&2, String, l, List.append(&2, String, List.replicate(String, Nat.sub(8n, n), "0"), r))), mhexq(q))

# the first 96 bits of an IPv4 compatible (`::/96`) or mapped
# (`::ffff:0:0/96`)
def prefix96(mapped: Bool) -> String:
  match mapped:
    case True{}:
      "00000000000000000000ffff"
    case False{}:
      "000000000000000000000000"

# a value that reaches no one (S3): an IPv4 compatible (the loopback `::1`
# and the unspecified `::` are its 0.0.0.1 and 0.0.0.0) or mapped whose
# first octet is 0, 127 or 255
def special6(+v: String) -> Bool:
  +o = String.drop(v, 24n)
  Bool.and(Bool.or(String.starts_with(v, prefix96(False{})), String.starts_with(v, prefix96(True{}))), Bool.or(String.starts_with(o, "00"), Bool.or(String.starts_with(o, "7f"), String.starts_with(o, "ff"))))

# the IPv6 a writes after before, then t, is taken: its length in chars
def take6(+a: Ip.Addr, +before: String, +t: String) -> Maybe<&2, Nat>:
  ans(Bool.and(Bool.and(Bool.and(Bool.and(counted(a), digit(a)), Bool.not(special6(value6(a)))), free(last(before))), free(first(t))), String.length(text6(a, "")))

# a decimal digit
def k_dec(k: CKind) -> Bool:
  match k:
    case KDec{}:
      True{}
    case KHex{}:
      False{}
    case KCol{}:
      False{}
    case KDot{}:
      False{}
    case KLet{}:
      False{}
    case KUnd{}:
      False{}
    case KDash{}:
      False{}
    case KOth{}:
      False{}

# what follows an IPv4's last octet does not go on with it: no decimal
# digit
def stops4(t: String) -> Bool:
  match t:
    case SNil{}:
      True{}
    case SCon{c, u}:
      Bool.not(k_dec(kind(c)))

# the first octet is not 0, 127 or 255
def first_ok(q: Ip.Quad) -> Bool:
  match q:
    case Ip.Quad{+a, b, c, d}:
      Bool.not(Bool.or(String.eq(a, "0"), Bool.or(String.eq(a, "127"), String.eq(a, "255"))))

def after4.sep(t: String) -> Bool:
  match t:
    case SNil{}:
      True{}
    case SCon{c, u}:
      Bool.not(k_alnum(kind(c)))

# no word char, nor `.` or `-` then an ASCII letter or digit, after an
# IPv4
def after4(t: String) -> Bool:
  match t:
    case SNil{}:
      True{}
    case SCon{+c, u}:
      Bool.and(Bool.not(k_word(kind(c))), Bool.or(Bool.not(k_sep(kind(c))), after4.sep(u)))

# an ASCII letter
def mletter(m: Maybe<&2, Char>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{c}:
      match c:
        case Chr{+x}:
          Bool.or(in(x, 65, 90), in(x, 97, 122))

# no word char or `.`, no ASCII letter and `/`, before an IPv4
def before4.of(m: Maybe<&2, Char>, p: Maybe<&2, Char>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+c}:
      Bool.and(k_edge4(kind(c)), Bool.not(Bool.and(Char.is_eq(c, '/'), mletter(p))))

def before4(+b: String) -> Bool:
  before4.of(last(b), before_last(b))

# the IPv4 q writes after before, then t, is taken (ctx: the line before
# reads as a version's context, S7: spec/harness/privacy_context.bend's
# vctx): its length in chars
def take4(+q: Ip.Quad, +before: String, +t: String, ctx: Bool) -> Maybe<&2, Nat>:
  ans(Bool.and(Bool.and(Bool.and(first_ok(q), after4(t)), before4(before)), Bool.not(ctx)), String.length(quad_text(q, "")))

# S4, S5: tokens
# --------------

# the classes that map back
def reversible(c: Tk.Class) -> Bool:
  match c:
    case Tk.Person{}:
      True{}
    case Tk.Email{}:
      True{}
    case Tk.Phone{}:
      True{}
    case Tk.Ip{}:
      True{}
    case Tk.Id{}:
      True{}
    case Tk.ApiKey{}:
      False{}
    case Tk.Card{}:
      False{}
    case Tk.Iban{}:
      False{}

# a text as it is
def raw(xs: List<&2, Tk.Piece>) -> List<&2, Tk.Seg>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      match x:
        case Tk.Plain{s}:
          Tk.Txt{s} <> raw(rest)
        case Tk.Value{c, v}:
          Tk.Clear{c, v} <> raw(rest)

def mask.of(r: Bool, +c: Tk.Class, +v: String) -> Tk.Seg:
  match r:
    case True{}:
      Tk.Clear{c, v}
    case False{}:
      Tk.Hash{c, v}

# a text with every value of a one-way class hidden by its token
def mask(xs: List<&2, Tk.Piece>) -> List<&2, Tk.Seg>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      match x:
        case Tk.Plain{s}:
          Tk.Txt{s} <> mask(rest)
        case Tk.Value{+c, v}:
          mask.of(reversible(c), c, v) <> mask(rest)

# a text holds no value of a one-way class
def no_secret(xs: List<&2, Tk.Piece>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      match x:
        case Tk.Plain{s}:
          no_secret(rest)
        case Tk.Value{c, v}:
          Bool.and(reversible(c), no_secret(rest))

def shape.of(r: Bool, +c: Tk.Class, +v: String) -> Tk.Seg:
  match r:
    case True{}:
      Tk.Tok{c, 0n}
    case False{}:
      Tk.Hash{c, v}

# what a scrubbed text is, indexes aside: its plain text, then for each
# value a token of its class (mapped, or one way)
def shape(xs: List<&2, Tk.Piece>) -> List<&2, Tk.Seg>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      match x:
        case Tk.Plain{s}:
          Tk.Txt{s} <> shape(rest)
        case Tk.Value{+c, v}:
          shape.of(reversible(c), c, v) <> shape(rest)

# a text with every index of a mapped token set to 0
def erase(ys: List<&2, Tk.Seg>) -> List<&2, Tk.Seg>:
  match ys:
    case Nil{}:
      Nil{}
    case y <> rest:
      match y:
        case Tk.Txt{s}:
          Tk.Txt{s} <> erase(rest)
        case Tk.Clear{c, v}:
          Tk.Clear{c, v} <> erase(rest)
        case Tk.Tok{c, i}:
          Tk.Tok{c, 0n} <> erase(rest)
        case Tk.Hash{c, v}:
          Tk.Hash{c, v} <> erase(rest)

def class_of(y: Tk.Seg) -> Maybe<&2, Tk.Class>:
  match y:
    case Tk.Txt{s}:
      None{}
    case Tk.Clear{c, v}:
      Some{c}
    case Tk.Tok{c, i}:
      Some{c}
    case Tk.Hash{c, v}:
      Some{c}

def secret_of(m: Maybe<&2, Tk.Class>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{c}:
      Bool.not(reversible(c))

def secret_seg(y: Tk.Seg) -> Bool:
  secret_of(class_of(y))

def creds.keep(b: Bool, +y: Tk.Seg, rest: List<&2, Tk.Seg>) -> List<&2, Tk.Seg>:
  match b:
    case True{}:
      y <> rest
    case False{}:
      rest

# the pieces of a text of a one-way class, in order
def creds(ys: List<&2, Tk.Seg>) -> List<&2, Tk.Seg>:
  match ys:
    case Nil{}:
      Nil{}
    case +y <> rest:
      creds.keep(secret_seg(y), y, creds(rest))

# S6: failover
# ------------

# the texts of the attempts: the one scrub y of a remote one, the raw
# text r of a local one
def sends(ts: List<&2, Bool>, +y: List<&2, Tk.Seg>, +r: List<&2, Tk.Seg>) -> List<&2, List<&2, Tk.Seg>>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> rest:
      match t:
        case True{}:
          y <> sends(rest, y, r)
        case False{}:
          r <> sends(rest, y, r)
