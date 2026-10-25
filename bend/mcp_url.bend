# mcp_url: whether a URL host is a literal loopback, private, link-local or
# unspecified address, or a `localhost` name (Rust: eukhe-bend
# rules/mcp_url.rs, asked by the MCP catalog validator of eukhe-core for
# every HTTPS endpoint). A structural check only: no DNS.
#
# - The host is read without its leading `[`s and trailing `]`s, its ASCII
#   letters lowercased.
# - `localhost` and every name ending `.localhost` are refused.
# - Four dot-separated parts that each read as a Rust u32 (an optional `+`,
#   then decimal digits, at most 4294967295) are an IPv4 address: refused
#   when a part is past 255, else when it is in 0/8, 10/8, 127/8,
#   169.254/16, 172.16/12 or 192.168/16. The first part that is no u32 or
#   is past 255 decides: no u32 makes the host no IPv4 address.
# - Else a host with `:` is an IPv6 address of eight 16-bit hex words
#   (split at its first `::`, which stands for the missing zero words; an
#   empty word is 0): refused when malformed, unspecified, loopback,
#   IPv4-mapped (::ffff:a.b.c.d) to a refused IPv4 range, in fe80::/10 or
#   in fc00::/7.
# Pure: no IO, no @unsafe.

import Base

# Text
# ----

def drop_open.at(b: Bool, c: Char, t: String, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, t}

# s without its leading `[`s
def drop_open(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      drop_open.at(Char.is_eq(c, '['), c, t, drop_open(t))

def drop_close.at(b: Bool, c: Char, r: String) -> String:
  match b:
    case True{}:
      match r:
        case SNil{}:
          SNil{}
        case SCon{x, u}:
          SCon{c, SCon{x, u}}
    case False{}:
      SCon{c, r}

# s without its trailing `]`s
def drop_close(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      drop_close.at(Char.is_eq(c, ']'), c, drop_close(t))

# the host as the checks read it
def bare(h: String) -> String:
  String.to_lower(drop_close(drop_open(h)))

def drop_zeros.at(b: Bool, c: Char, t: String, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, t}

# s without its leading `0`s
def drop_zeros(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      drop_zeros.at(Char.is_eq(c, '0'), c, t, drop_zeros(t))

def unsigned.at(b: Bool, c: Char, t: String) -> String:
  match b:
    case True{}:
      t
    case False{}:
      SCon{c, t}

# the digits of a Rust unsigned number: s without its one leading `+`
def unsigned(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      unsigned.at(Char.is_eq(c, '+'), c, t)

# Decimal parts
# -------------

# A dot-separated part: an octet, a u32 past 255, or no u32
type Part is Data:
  POct{v: U32}
  PBig{}
  PNone{}

def all_dec(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(Char.is_digit(c), all_dec(t))

# the value of decimal digits, folded onto v
def dec(s: String, v: U32) -> U32:
  match s:
    case SNil{}:
      v
    case SCon{c, t}:
      dec(t, U32.add(U32.mul(v, 10), U32.sub(Char.to_u32(c), 48)))

def part.small(b: Bool, v: U32) -> Part:
  match b:
    case True{}:
      POct{v}
    case False{}:
      PBig{}

def part.big(b: Bool) -> Part:
  match b:
    case True{}:
      PBig{}
    case False{}:
      PNone{}

def part.long(b: Bool, +g: String) -> Part:
  match b:
    case True{}:
      PBig{}
    case False{}:
      part.big(Bool.and(Nat.is_eq(String.length(g), 10n), String.is_le(g, "4294967295")))

def part.short(b: Bool, +g: String) -> Part:
  match b:
    case True{}:
      +v = dec(g, 0)
      part.small(U32.is_le(v, 255), v)
    case False{}:
      part.long(Nat.is_le(String.length(g), 9n), g)

# the part of significant digits g (no leading zero)
def part.sig(+g: String) -> Part:
  part.short(Nat.is_le(String.length(g), 3n), g)

def part.digits(b: Bool, d: String) -> Part:
  match b:
    case True{}:
      part.sig(drop_zeros(d))
    case False{}:
      PNone{}

def part(s: String) -> Part:
  +d = unsigned(s)
  part.digits(Bool.and(Bool.not(String.is_empty(d)), all_dec(d)), d)

# IPv4
# ----

# A host read as IPv4: not four u32 parts, refused, or its four octets
type V4 is Data:
  V4No{}
  V4Bad{}
  V4Quad{a: U32, b: U32, c: U32, d: U32}

def quad.d(a: U32, b: U32, c: U32, s: Part) -> V4:
  match s:
    case POct{d}:
      V4Quad{a, b, c, d}
    case PBig{}:
      V4Bad{}
    case PNone{}:
      V4No{}

def quad.c(a: U32, b: U32, r: Part, s: Part) -> V4:
  match r:
    case POct{c}:
      quad.d(a, b, c, s)
    case PBig{}:
      V4Bad{}
    case PNone{}:
      V4No{}

def quad.b(a: U32, q: Part, r: Part, s: Part) -> V4:
  match q:
    case POct{b}:
      quad.c(a, b, r, s)
    case PBig{}:
      V4Bad{}
    case PNone{}:
      V4No{}

# four parts, read in order: the first that is no octet decides
def quad(p: Part, q: Part, r: Part, s: Part) -> V4:
  match p:
    case POct{a}:
      quad.b(a, q, r, s)
    case PBig{}:
      V4Bad{}
    case PNone{}:
      V4No{}

def v4.parts(ps: List<&2, String>) -> V4:
  match ps:
    case Nil{}:
      V4No{}
    case p <> t1:
      match t1:
        case Nil{}:
          V4No{}
        case q <> t2:
          match t2:
            case Nil{}:
              V4No{}
            case r <> t3:
              match t3:
                case Nil{}:
                  V4No{}
                case s <> t4:
                  match t4:
                    case Nil{}:
                      quad(part(p), part(q), part(r), part(s))
                    case x <> t5:
                      V4No{}

def v4(b: String) -> V4:
  v4.parts(String.split(b, '.'))

# the first two octets of a refused IPv4 range
def private_ab(+a: U32, +b: U32) -> Bool:
  Bool.or(Bool.or(U32.is_eq(a, 127), Bool.or(U32.is_eq(a, 10), U32.is_eq(a, 0))), Bool.or(Bool.and(U32.is_eq(a, 172), Bool.and(U32.is_ge(b, 16), U32.is_le(b, 31))), Bool.or(Bool.and(U32.is_eq(a, 192), U32.is_eq(b, 168)), Bool.and(U32.is_eq(a, 169), U32.is_eq(b, 254)))))

# IPv6
# ----

def is_hex(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)), Bool.and(U32.is_ge(x, 97), U32.is_le(x, 102)))

def all_hex(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(is_hex(c), all_hex(t))

def hex_digit.at(b: Bool, x: U32) -> U32:
  match b:
    case True{}:
      U32.sub(x, 48)
    case False{}:
      U32.sub(x, 87)

def hex_digit(c: Char) -> U32:
  match c:
    case Chr{+x}:
      hex_digit.at(U32.is_le(x, 57), x)

# the value of hex digits, folded onto v
def hex(s: String, v: U32) -> U32:
  match s:
    case SNil{}:
      v
    case SCon{c, t}:
      hex(t, U32.add(U32.mul(v, 16), hex_digit(c)))

def word.sig(b: Bool, g: String) -> Maybe<&2, U32>:
  match b:
    case True{}:
      Some{hex(g, 0)}
    case False{}:
      None{}

def word.digits(b: Bool, d: String) -> Maybe<&2, U32>:
  match b:
    case True{}:
      +g = drop_zeros(d)
      word.sig(Nat.is_le(String.length(g), 4n), g)
    case False{}:
      None{}

# a 16-bit word: an empty part is 0, else a Rust u16 in radix 16
def word(s: String) -> Maybe<&2, U32>:
  match s:
    case SNil{}:
      Some{0}
    case SCon{c, t}:
      +d = unsigned(SCon{c, t})
      word.digits(Bool.and(Bool.not(String.is_empty(d)), all_hex(d)), d)

def words.cons(m: Maybe<&2, U32>, r: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{w}:
      match r:
        case None{}:
          None{}
        case Some{ws}:
          Some{w <> ws}

# the words of the parts, or None when one is malformed
def words(ps: List<&2, String>) -> Maybe<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      Some{Nil{}}
    case p <> t:
      words.cons(word(p), words(t))

def zeros(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      0 <> zeros(p)

def any_empty(ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> t:
      Bool.or(String.is_empty(p), any_empty(t))

# The address split at its first `::`: no `::`, or the text before it and
# after it
type Halves is Data:
  One{all: String}
  Two{head: String, tail: String}

def halves.push(c: Char, h: Halves) -> Halves:
  match h:
    case One{a}:
      One{SCon{c, a}}
    case Two{a, b}:
      Two{SCon{c, a}, b}

def halves.at(b: Bool, c: Char, t: String, r: Halves) -> Halves:
  match b:
    case True{}:
      Two{SNil{}, String.drop(t, 1n)}
    case False{}:
      halves.push(c, r)

def halves(s: String) -> Halves:
  match s:
    case SNil{}:
      One{SNil{}}
    case SCon{+c, +t}:
      halves.at(Bool.and(Char.is_eq(c, ':'), String.starts_with(t, ":")), c, t, halves(t))

# the parts of a side of `::`: none when it is empty
def side(s: String) -> List<&2, String>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      String.split(SCon{c, t}, ':')

def join3(a: Maybe<&2, List<&2, U32>>, z: List<&2, U32>, b: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match a:
    case None{}:
      None{}
    case Some{x}:
      match b:
        case None{}:
          None{}
        case Some{y}:
          Some{List.append(&2, U32, x, List.append(&2, U32, z, y))}

def expand.two.at(b: Bool, hp: List<&2, String>, tp: List<&2, String>, n: Nat) -> Maybe<&2, List<&2, U32>>:
  match b:
    case True{}:
      join3(words(hp), zeros(Nat.sub(8n, n)), words(tp))
    case False{}:
      None{}

def expand.two(+hp: List<&2, String>, +tp: List<&2, String>) -> Maybe<&2, List<&2, U32>>:
  +n = Nat.add(List.length(&2, String, hp), List.length(&2, String, tp))
  expand.two.at(Nat.is_le(n, 7n), hp, tp, n)

def expand.one.at(b: Bool, ps: List<&2, String>) -> Maybe<&2, List<&2, U32>>:
  match b:
    case True{}:
      words(ps)
    case False{}:
      None{}

def expand.one(+ps: List<&2, String>) -> Maybe<&2, List<&2, U32>>:
  expand.one.at(Bool.and(Nat.is_eq(List.length(&2, String, ps), 8n), Bool.not(any_empty(ps))), ps)

def expand.of(h: Halves) -> Maybe<&2, List<&2, U32>>:
  match h:
    case One{a}:
      expand.one(side(a))
    case Two{a, b}:
      expand.two(side(a), side(b))

# the eight words of an IPv6 address, or None when malformed
def expand(s: String) -> Maybe<&2, List<&2, U32>>:
  expand.of(halves(s))

# the refused IPv6 ranges, over eight words
def v6.check(+w0: U32, +w1: U32, +w2: U32, +w3: U32, +w4: U32, +w5: U32, +w6: U32, +w7: U32) -> Bool:
  +z5 = Bool.and(U32.is_eq(w0, 0), Bool.and(U32.is_eq(w1, 0), Bool.and(U32.is_eq(w2, 0), Bool.and(U32.is_eq(w3, 0), U32.is_eq(w4, 0)))))
  +z7 = Bool.and(z5, Bool.and(U32.is_eq(w5, 0), U32.is_eq(w6, 0)))
  Bool.or(Bool.and(z7, Bool.or(U32.is_eq(w7, 0), U32.is_eq(w7, 1))), Bool.or(Bool.and(z5, Bool.and(U32.is_eq(w5, 65535), private_ab(U32.shrn(w6, 8n), U32.and(w6, 255)))), Bool.or(Bool.and(U32.is_ge(w0, 65152), U32.is_le(w0, 65215)), Bool.and(U32.is_ge(w0, 64512), U32.is_le(w0, 65023)))))

# eight words checked; any other count (never expanded) is refused
def v6.words(ws: List<&2, U32>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case w0 <> t0:
      match t0:
        case Nil{}:
          True{}
        case w1 <> t1:
          match t1:
            case Nil{}:
              True{}
            case w2 <> t2:
              match t2:
                case Nil{}:
                  True{}
                case w3 <> t3:
                  match t3:
                    case Nil{}:
                      True{}
                    case w4 <> t4:
                      match t4:
                        case Nil{}:
                          True{}
                        case w5 <> t5:
                          match t5:
                            case Nil{}:
                              True{}
                            case w6 <> t6:
                              match t6:
                                case Nil{}:
                                  True{}
                                case w7 <> t7:
                                  match t7:
                                    case Nil{}:
                                      v6.check(w0, w1, w2, w3, w4, w5, w6, w7)
                                    case x <> t8:
                                      True{}

def v6.of(m: Maybe<&2, List<&2, U32>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{ws}:
      v6.words(ws)

def v6(b: Bool, s: String) -> Bool:
  match b:
    case True{}:
      v6.of(expand(s))
    case False{}:
      False{}

# The check
# ---------

def after_v4(v: V4, +s: String) -> Bool:
  match v:
    case V4No{}:
      v6(String.contains(s, ":"), s)
    case V4Bad{}:
      True{}
    case V4Quad{a, b, c, d}:
      private_ab(a, b)

def refused.at(named: Bool, +s: String) -> Bool:
  match named:
    case True{}:
      True{}
    case False{}:
      after_v4(v4(s), s)

# whether the host h is refused
def refused(h: String) -> Bool:
  +s = bare(h)
  refused.at(Bool.or(String.eq(s, "localhost"), String.ends_with(s, ".localhost")), s)
