# privacy/ip: which text at a candidate position of the outbound scrubber
# (crates/eukhe-ai/src/privacy) is an IP address, as the compiled core
# runs it (bend/ffi_privacy.bend; Rust: eukhe-bend rules/privacy.rs, asked
# by eukhe-ai privacy/detect.rs). laws/privacy/ip.bend pins it against
# spec/harness/privacy.bend.
#
# A candidate is the text before the position (`before`, the end of its
# line: at most the 48 bytes before it) and the text from it (`rest`, at
# most 48 chars: an address is at most 45 chars, and the grammar reads at
# most two chars past one). Rust sends every char that is no ASCII as its
# class: U+00AA (a word char) or U+00A0 (any other).
#
# 1. IPv6 (RFC 4291 text form): eight groups of 1 to 4 hex digits split
#    by `:`, or fewer around one `::` (three to seven explicit groups); the
#    last two groups may be written as an IPv4. One group holds a decimal
#    digit (an IPv4 does). No word char, `:` or `.` touches it on either
#    side. So `a::before`, `std::sync::Arc`, `dead::beef`, `xs[1::2]`, the
#    loopback `::1` and the link-local `fe80::1` are no address.
# 2. IPv4: four dotted decimal octets, 0 to 255, no leading zero. No word
#    char or `.` before it, and no product name and `/` (`Chrome/120.0.0.0`);
#    no word char after it, nor a `.` or `-` and a letter or digit (a fifth
#    part, a pre-release). The first octet is not 0 (unspecified), 127
#    (loopback) or 255 (mask, broadcast). Not in a version's context: the
#    line before it, blanks dropped, ends with a requirement operator (`==`
#    `>=` `<=` `~=` `!=` `^` `~`), or, quotes, `=`, `:`, `(`, `<`, `>`,
#    `[`, `,` dropped too, its last word (ASCII letters, digits, `_`) holds
#    `version` or is `ver`, `v`, `release` or `tag`, in any case.
# 3. A candidate is an IPv6, else an IPv4, else none: the answer is the
#    address's length in chars.

import Base
import ./context.bend as Cx

# Symbols
# -------

# a char of rest, by what the grammar asks of it
type Sym is Data:
  Dig{c: Char}
  Hx{c: Char}
  Col{}
  Dot{}
  Let{}
  Und{}
  Dash{}
  Oth{}

def Sym.when(hit: Bool, y: Sym, miss: Sym) -> Sym:
  match hit:
    case True{}:
      y
    case False{}:
      miss

# Dig: 0-9; Hx: a-f, A-F; Col: `:`; Dot: `.`; Let: the other ASCII
# letters; Und: `_` and the word mark U+00AA; Dash: `-`; Oth: the rest
def Sym.of(c: Char) -> Sym:
  match c:
    case Chr{+x}:
      Sym.when(Cx.in(x, 48, 57), Dig{Chr{x}}, Sym.when(Cx.in(x, 97, 102), Hx{Chr{x}}, Sym.when(Cx.in(x, 65, 70), Hx{Chr{x}}, Sym.when(U32.is_eq(x, 58), Col{}, Sym.when(U32.is_eq(x, 46), Dot{}, Sym.when(Cx.in(x, 103, 122), Let{}, Sym.when(Cx.in(x, 71, 90), Let{}, Sym.when(U32.is_eq(x, 95), Und{}, Sym.when(U32.is_eq(x, 170), Und{}, Sym.when(U32.is_eq(x, 45), Dash{}, Oth{}))))))))))

def Sym.list(s: String) -> List<&2, Sym>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      Sym.of(c) <> Sym.list(t)

# no word char, `:` or `.`
def Sym.free(y: Sym) -> Bool:
  match y:
    case Dig{c}:
      False{}
    case Hx{c}:
      False{}
    case Col{}:
      False{}
    case Dot{}:
      False{}
    case Let{}:
      False{}
    case Und{}:
      False{}
    case Dash{}:
      True{}
    case Oth{}:
      True{}

# an ASCII letter or digit
def Sym.alnum(y: Sym) -> Bool:
  match y:
    case Dig{c}:
      True{}
    case Hx{c}:
      True{}
    case Col{}:
      False{}
    case Dot{}:
      False{}
    case Let{}:
      True{}
    case Und{}:
      False{}
    case Dash{}:
      False{}
    case Oth{}:
      False{}

# a word char: an ASCII letter or digit, `_`, the word mark
def Sym.word(y: Sym) -> Bool:
  match y:
    case Dig{c}:
      True{}
    case Hx{c}:
      True{}
    case Col{}:
      False{}
    case Dot{}:
      False{}
    case Let{}:
      True{}
    case Und{}:
      True{}
    case Dash{}:
      False{}
    case Oth{}:
      False{}

# Runs
# ----

# a run of chars, and what follows it
type Cut is Data:
  Cut{s: String, rest: List<&2, Sym>}

def run.cons(c: Char, r: Cut) -> Cut:
  match r:
    case Cut{h, rest}:
      Cut{SCon{c, h}, rest}

# the hex digits at the start of ss, and what follows them
def run(ss: List<&2, Sym>) -> Cut:
  match ss:
    case Nil{}:
      Cut{SNil{}, Nil{}}
    case y <> t:
      match y:
        case Dig{c}:
          run.cons(c, run(t))
        case Hx{c}:
          run.cons(c, run(t))
        case Col{}:
          Cut{SNil{}, Col{} <> t}
        case Dot{}:
          Cut{SNil{}, Dot{} <> t}
        case Let{}:
          Cut{SNil{}, Let{} <> t}
        case Und{}:
          Cut{SNil{}, Und{} <> t}
        case Dash{}:
          Cut{SNil{}, Dash{} <> t}
        case Oth{}:
          Cut{SNil{}, Oth{} <> t}

# the decimal digits at the start of ss, and what follows them
def drun(ss: List<&2, Sym>) -> Cut:
  match ss:
    case Nil{}:
      Cut{SNil{}, Nil{}}
    case y <> t:
      match y:
        case Dig{c}:
          run.cons(c, drun(t))
        case Hx{c}:
          Cut{SNil{}, Hx{c} <> t}
        case Col{}:
          Cut{SNil{}, Col{} <> t}
        case Dot{}:
          Cut{SNil{}, Dot{} <> t}
        case Let{}:
          Cut{SNil{}, Let{} <> t}
        case Und{}:
          Cut{SNil{}, Und{} <> t}
        case Dash{}:
          Cut{SNil{}, Dash{} <> t}
        case Oth{}:
          Cut{SNil{}, Oth{} <> t}

# Octets and quads
# ----------------

# a 3-digit octet a b c (a is no 0) is at most 255
def le255(a: Char, b: Char, c: Char) -> Bool:
  match a b c:
    case Chr{+x} Chr{+y} Chr{z}:
      Bool.or(U32.is_lt(x, 50), Bool.and(U32.is_eq(x, 50), Bool.or(U32.is_lt(y, 53), Bool.and(U32.is_eq(y, 53), U32.is_le(z, 53)))))

# 1 to 3 decimal digits, no leading zero, at most 255
def oct_ok(ds: String) -> Bool:
  match ds:
    case SNil{}:
      False{}
    case SCon{+a, t1}:
      match t1:
        case SNil{}:
          True{}
        case SCon{b, t2}:
          match t2:
            case SNil{}:
              Bool.not(Char.is_eq(a, '0'))
            case SCon{c, t3}:
              match t3:
                case SNil{}:
                  Bool.and(Bool.not(Char.is_eq(a, '0')), le255(a, b, c))
                case SCon{d, t4}:
                  False{}

# four dotted decimal octets
type Quad is Data:
  Quad{a: String, b: String, c: String, d: String}

# a quad, and what follows it
type QCut is Data:
  QCut{q: Quad, rest: List<&2, Sym>}

def oct.ok(ok: Bool, +ds: String, +rest: List<&2, Sym>) -> Maybe<&2, Cut>:
  match ok:
    case True{}:
      Some{Cut{ds, rest}}
    case False{}:
      None{}

def oct.of(r: Cut) -> Maybe<&2, Cut>:
  match r:
    case Cut{+ds, rest}:
      oct.ok(oct_ok(ds), ds, rest)

# an octet at the start of ss (its whole digit run), and what follows it
def oct(ss: List<&2, Sym>) -> Maybe<&2, Cut>:
  oct.of(drun(ss))

# a dot, then an octet
def dot_oct(ss: List<&2, Sym>) -> Maybe<&2, Cut>:
  match ss:
    case Nil{}:
      None{}
    case y <> t:
      match y:
        case Dot{}:
          oct(t)
        case Dig{c}:
          None{}
        case Hx{c}:
          None{}
        case Col{}:
          None{}
        case Let{}:
          None{}
        case Und{}:
          None{}
        case Dash{}:
          None{}
        case Oth{}:
          None{}

def quad.d(+a: String, +b: String, +c: String, m: Maybe<&2, Cut>) -> Maybe<&2, QCut>:
  match m:
    case None{}:
      None{}
    case Some{Cut{d, rest}}:
      Some{QCut{Quad{a, b, c, d}, rest}}

def quad.c(+a: String, +b: String, m: Maybe<&2, Cut>) -> Maybe<&2, QCut>:
  match m:
    case None{}:
      None{}
    case Some{Cut{c, rest}}:
      quad.d(a, b, c, dot_oct(rest))

def quad.b(+a: String, m: Maybe<&2, Cut>) -> Maybe<&2, QCut>:
  match m:
    case None{}:
      None{}
    case Some{Cut{b, rest}}:
      quad.c(a, b, dot_oct(rest))

def quad.a(m: Maybe<&2, Cut>) -> Maybe<&2, QCut>:
  match m:
    case None{}:
      None{}
    case Some{Cut{a, rest}}:
      quad.b(a, dot_oct(rest))

# a quad at the start of ss, and what follows it
def quad(ss: List<&2, Sym>) -> Maybe<&2, QCut>:
  quad.a(oct(ss))

# IPv6
# ----

# an address read: its groups (before the `::`, after it), and the IPv4
# that ends it
type Addr is Data:
  Full{gs: List<&2, String>, q: Maybe<&2, Quad>}
  Gap{l: List<&2, String>, r: List<&2, String>, q: Maybe<&2, Quad>}

# the groups read so far: whether a `::` came, the groups before it,
# the groups after it
type Acc is Data:
  Acc{gap: Bool, l: List<&2, String>, r: List<&2, String>}

# where the reader is: the start of the text; inside a group that started
# at start, with room for that many more hex digits; inside a run of more
# than four hex digits; where a group may start (after `::` or `:`)
type Mode is Data:
  Begin{}
  Grp{start: List<&2, Sym>, room: Nat}
  Long{start: List<&2, Sym>}
  Open{}

type Read is Data:
  Got{a: Addr, rest: List<&2, Sym>}
  Bad{}

def Acc.push(acc: Acc, g: String) -> Acc:
  match acc:
    case Acc{gap, l, r}:
      match gap:
        case False{}:
          Acc{False{}, List.append(&2, String, l, [g]), r}
        case True{}:
          Acc{True{}, l, List.append(&2, String, r, [g])}

def Acc.addr(acc: Acc, q: Maybe<&2, Quad>) -> Addr:
  match acc:
    case Acc{gap, l, r}:
      match gap:
        case False{}:
          Full{l, q}
        case True{}:
          Gap{l, r, q}

def finish(acc: Acc, q: Maybe<&2, Quad>, rest: List<&2, Sym>) -> Read:
  Got{Acc.addr(acc, q), rest}

# the IPv4 that ends the address, read from its first group's start
def quad_end(acc: Acc, m: Maybe<&2, QCut>) -> Read:
  match m:
    case None{}:
      Bad{}
    case Some{QCut{q, rest}}:
      finish(acc, Some{q}, rest)

# the group that started at start
def group.of(r: Cut) -> String:
  match r:
    case Cut{g, rest}:
      g

def group(start: List<&2, Sym>) -> String:
  group.of(run(start))

# the reading ends at rest, before a char that is no hex digit, `:` or `.`
def read.stop(m: Mode, acc: Acc, rest: List<&2, Sym>) -> Read:
  match m:
    case Begin{}:
      Bad{}
    case Grp{start, room}:
      finish(Acc.push(acc, group(start)), None{}, rest)
    case Long{start}:
      Bad{}
    case Open{}:
      finish(acc, None{}, rest)

# a `:` that no hex digit or `:` follows: only where a group may start
# does the reading end before it
def read.colon(m: Mode, acc: Acc, rest: List<&2, Sym>) -> Read:
  match m:
    case Begin{}:
      Bad{}
    case Grp{start, room}:
      Bad{}
    case Long{start}:
      Bad{}
    case Open{}:
      finish(acc, None{}, rest)

# read the address, one symbol at a time (the reader of
# crates/eukhe-ai/src/privacy/detect.rs before the core ran it, symbol by
# symbol)
def read(ss: List<&2, Sym>, m: Mode, acc: Acc) -> Read:
  match ss:
    case Nil{}:
      match m:
        case Begin{}:
          Bad{}
        case Grp{start, room}:
          finish(Acc.push(acc, group(start)), None{}, Nil{})
        case Long{start}:
          Bad{}
        case Open{}:
          finish(acc, None{}, Nil{})
    case y <> +t:
      match y:
        case Dig{c}:
          match m:
            case Begin{}:
              read(t, Grp{Dig{c} <> t, 3n}, acc)
            case Grp{start, room}:
              match room:
                case 0n:
                  read(t, Long{start}, acc)
                case 1n+p:
                  read(t, Grp{start, p}, acc)
            case Long{start}:
              read(t, Long{start}, acc)
            case Open{}:
              read(t, Grp{Dig{c} <> t, 3n}, acc)
        case Hx{c}:
          match m:
            case Begin{}:
              read(t, Grp{Hx{c} <> t, 3n}, acc)
            case Grp{start, room}:
              match room:
                case 0n:
                  read(t, Long{start}, acc)
                case 1n+p:
                  read(t, Grp{start, p}, acc)
            case Long{start}:
              read(t, Long{start}, acc)
            case Open{}:
              read(t, Grp{Hx{c} <> t, 3n}, acc)
        case Col{}:
          match t:
            case Nil{}:
              match m:
                case Begin{}:
                  Bad{}
                case Grp{start, room}:
                  Bad{}
                case Long{start}:
                  Bad{}
                case Open{}:
                  finish(acc, None{}, [Col{}])
            case z <> u:
              match z:
                case Col{}:
                  match m:
                    case Begin{}:
                      read(u, Open{}, Acc{True{}, Nil{}, Nil{}})
                    case Grp{start, room}:
                      match acc:
                        case Acc{gap, l, r}:
                          match gap:
                            case False{}:
                              read(u, Open{}, Acc{True{}, List.append(&2, String, l, [group(start)]), r})
                            case True{}:
                              Bad{}
                    case Long{start}:
                      Bad{}
                    case Open{}:
                      finish(acc, None{}, Col{} <> t)
                case Dig{c}:
                  match m:
                    case Begin{}:
                      Bad{}
                    case Grp{start, room}:
                      read(t, Open{}, Acc.push(acc, group(start)))
                    case Long{start}:
                      Bad{}
                    case Open{}:
                      finish(acc, None{}, Col{} <> t)
                case Hx{c}:
                  match m:
                    case Begin{}:
                      Bad{}
                    case Grp{start, room}:
                      read(t, Open{}, Acc.push(acc, group(start)))
                    case Long{start}:
                      Bad{}
                    case Open{}:
                      finish(acc, None{}, Col{} <> t)
                case Dot{}:
                  read.colon(m, acc, Col{} <> t)
                case Let{}:
                  read.colon(m, acc, Col{} <> t)
                case Und{}:
                  read.colon(m, acc, Col{} <> t)
                case Dash{}:
                  read.colon(m, acc, Col{} <> t)
                case Oth{}:
                  read.colon(m, acc, Col{} <> t)
        case Dot{}:
          match m:
            case Begin{}:
              Bad{}
            case Grp{start, room}:
              quad_end(acc, quad(start))
            case Long{start}:
              quad_end(acc, quad(start))
            case Open{}:
              finish(acc, None{}, Dot{} <> t)
        case Let{}:
          read.stop(m, acc, Let{} <> t)
        case Und{}:
          read.stop(m, acc, Und{} <> t)
        case Dash{}:
          read.stop(m, acc, Dash{} <> t)
        case Oth{}:
          read.stop(m, acc, Oth{} <> t)

# the length of what an address holds besides its groups: an IPv4 is two
def Quad.n(q: Maybe<&2, Quad>) -> Nat:
  match q:
    case None{}:
      0n
    case Some{x}:
      2n

# eight explicit groups, or three to seven around a `::`
def counted(a: Addr) -> Bool:
  match a:
    case Full{+gs, q}:
      Nat.is_eq(Nat.add(List.length(&2, String, gs), Quad.n(q)), 8n)
    case Gap{+l, +r, q}:
      +n = Nat.add(Nat.add(List.length(&2, String, l), List.length(&2, String, r)), Quad.n(q))
      Bool.and(Nat.is_le(3n, n), Nat.is_le(n, 7n))

# g holds a decimal digit
def dig_in(g: String) -> Bool:
  match g:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.or(Char.is_digit(c), dig_in(t))

def digs(gs: List<&2, String>) -> Bool:
  match gs:
    case Nil{}:
      False{}
    case g <> rest:
      Bool.or(dig_in(g), digs(rest))

# a group holds a decimal digit, or an IPv4 ends the address
def digit(a: Addr) -> Bool:
  match a:
    case Full{gs, q}:
      Bool.or(digs(gs), Maybe.is_some(&2, Quad, q))
    case Gap{l, r, q}:
      Bool.or(digs(l), Bool.or(digs(r), Maybe.is_some(&2, Quad, q)))

def ans(ok: Bool, n: Nat) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{n}
    case False{}:
      None{}

# the chars before a position: the one before the last, the last
def last2(s: String, p: Maybe<&2, Char>, q: Maybe<&2, Char>) -> Maybe<&2, Char> & Maybe<&2, Char>:
  match s:
    case SNil{}:
      (p, q)
    case SCon{c, t}:
      last2(t, q, Some{c})

def last.of(r: Maybe<&2, Char> & Maybe<&2, Char>) -> Maybe<&2, Char>:
  match r:
    case (p, q):
      q

def last(s: String) -> Maybe<&2, Char>:
  last.of(last2(s, None{}, None{}))

# no word char, `:` or `.` before an IPv6
def edge6(m: Maybe<&2, Char>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{c}:
      Sym.free(Sym.of(c))

# no word char or `.` follows an IPv6 (the reader stops at no hex digit)
def after6(rest: List<&2, Sym>) -> Bool:
  match rest:
    case Nil{}:
      True{}
    case y <> t:
      Sym.free(y)

def v6.got(n: Nat, r: Read) -> Maybe<&2, Nat>:
  match r:
    case Bad{}:
      None{}
    case Got{+a, +rest}:
      ans(Bool.and(Bool.and(counted(a), digit(a)), after6(rest)), Nat.sub(n, List.length(&2, Sym, rest)))

def v6.go(ok: Bool, s: String) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      +ss = Sym.list(s)
      v6.got(List.length(&2, Sym, ss), read(ss, Begin{}, Acc{False{}, Nil{}, Nil{}}))
    case False{}:
      None{}

# the IPv6 at the start of s after before: its length in chars
def v6(before: String, s: String) -> Maybe<&2, Nat>:
  v6.go(edge6(last(before)), s)

# IPv4
# ----

# not 0.x (unspecified), 127.x (loopback), 255.x (mask, broadcast)
def first_ok(q: Quad) -> Bool:
  match q:
    case Quad{+a, b, c, d}:
      Bool.not(Bool.or(String.eq(a, "0"), Bool.or(String.eq(a, "127"), String.eq(a, "255"))))

# no word char, `.` or `-` and an ASCII letter or digit after an IPv4
def after4.sep(rest: List<&2, Sym>) -> Bool:
  match rest:
    case Nil{}:
      True{}
    case y <> t:
      Bool.not(Sym.alnum(y))

def after4(rest: List<&2, Sym>) -> Bool:
  match rest:
    case Nil{}:
      True{}
    case y <> t:
      match y:
        case Dig{c}:
          False{}
        case Hx{c}:
          False{}
        case Col{}:
          True{}
        case Dot{}:
          after4.sep(t)
        case Let{}:
          False{}
        case Und{}:
          False{}
        case Dash{}:
          after4.sep(t)
        case Oth{}:
          True{}

# an ASCII letter
def alpha(m: Maybe<&2, Char>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{c}:
      match c:
        case Chr{+x}:
          Bool.or(Cx.in(x, 65, 90), Cx.in(x, 97, 122))

# no word char or `.` before an IPv4
def Sym.edge4(y: Sym) -> Bool:
  match y:
    case Dig{c}:
      False{}
    case Hx{c}:
      False{}
    case Col{}:
      True{}
    case Dot{}:
      False{}
    case Let{}:
      False{}
    case Und{}:
      False{}
    case Dash{}:
      True{}
    case Oth{}:
      True{}

# the chars before an IPv4: no word char or `.`, no letter and `/`
def edge4(r: Maybe<&2, Char> & Maybe<&2, Char>) -> Bool:
  match r:
    case (p, q):
      match q:
        case None{}:
          True{}
        case Some{+c}:
          Bool.and(Sym.edge4(Sym.of(c)), Bool.not(Bool.and(Char.is_eq(c, '/'), alpha(p))))

def v4.got(n: Nat, m: Maybe<&2, QCut>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{QCut{q, +rest}}:
      ans(Bool.and(first_ok(q), after4(rest)), Nat.sub(n, List.length(&2, Sym, rest)))

def v4.go(ok: Bool, s: String) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      +ss = Sym.list(s)
      v4.got(List.length(&2, Sym, ss), quad(ss))
    case False{}:
      None{}

# the IPv4 at the start of s after before: its length in chars
def v4(+before: String, s: String) -> Maybe<&2, Nat>:
  v4.go(Bool.and(edge4(last2(before, None{}, None{})), Bool.not(Cx.vctx(before))), s)

# The answer
# ----------

# the address at the start of rest after before (an IPv6, else an IPv4):
# its length in chars
def ip(+before: String, +rest: String) -> Maybe<&2, Nat>:
  Maybe.or(&2, Nat, v6(before, rest), v4(before, rest))
