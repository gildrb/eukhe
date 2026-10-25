# eukhe: the laws of area mcp_url

import Base
import ../bend/mcp_url.bend as Mu
import ../bend/ffi_mcp_url.bend as FMu
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (D1) A URL host the MCP catalog refuses
# ---------------------------------------
# bend/mcp_url.bend, run as the compiled core by bend/ffi_mcp_url.bend
# (eukhe-bend rules/mcp_url.rs; asked by eukhe-core's MCP catalog validator
# for the host of every HTTPS endpoint, as the url crate gives it). Every
# input is free: any host text.
#
# R1: the host is read without all its leading `[` and then all its
#     trailing `]`, its ASCII letters lowercased (Rust
#     `trim_start_matches`, `trim_end_matches`, `to_ascii_lowercase`).
# R2: `localhost`, and a name that ends with `.localhost`, is refused.
# R3: a part is read as a Rust u32 (`str::parse::<u32>`): an optional
#     leading `+` with something after it, then decimal digits only (at
#     least one), worth at most 4294967295 (leading zeros allowed).
#     Without its leading zeros: at most 3 digits is the value (an octet
#     when at most 255); 4 to 9 digits, or 10 digits at most 4294967295,
#     is past 255; else no u32.
# R4: a host that splits at `.` into exactly four parts is IPv4 when the
#     parts, read in order up to the first that is no octet (0-255), are
#     octets: the first part past 255 refuses the host; the first part
#     that is no u32 makes it no IPv4 address. An IPv4 address is refused
#     when its first octet is 0, 10 or 127, or its first two are
#     169.254, 172.16-31 or 192.168.
# R5: another host that holds `:` is IPv6. It splits at its first `::`
#     into the text before and after (no `::`: one text). A side's parts
#     are its `:`-separated pieces (none for an empty side). Without `::`
#     there must be exactly 8 parts, none empty; with `::` at most 7 in
#     all, the missing ones zero words between the sides. A part is a word:
#     empty is 0, else a Rust u16 in radix 16 (`u16::from_str_radix`: an
#     optional leading `+` with something after it, then hex digits, at
#     most 4 without leading zeros). A malformed address is refused.
# R6: an IPv6 address is refused when it is :: or ::1, when it is
#     IPv4-mapped (five zero words, then ffff) and its last two words as
#     four octets are in R4's ranges, when its first word is in fe80-febf
#     (fe80::/10) or fc00-fdff (fc00::/7).
# R7: any other host passes.
# R8: the entry answers each request Rust writes (the host, its length
#     within the wire) with whether R1-R7 refuse it, reads exactly the
#     request and nothing after it, and answers any other input with the
#     exact error form `E mcp_url: malformed request`.
#
# Changed from the Rust it replaced (eukhe-core mcp/url_checks.rs): its
# IPv4-mapped test asked for six zero words and a sixth word ffff at once,
# so it never held, and `[::ffff:7f00:1]` (the url crate's spelling of
# `[::ffff:127.0.0.1]`) passed. R6 checks the mapped address as its
# comment meant.

# Spec helpers
# ------------

# R1, R3, R5: s without all its leading chars ch
def mu_lead.at(b: Bool, c: Char, t: String, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, t}

def mu_lead(s: String, +ch: Char) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      mu_lead.at(Char.is_eq(c, ch), c, t, mu_lead(t, ch))

def mu_trail.at(b: Bool, c: Char, r: String) -> String:
  match b:
    case True{}:
      match r:
        case SNil{}:
          SNil{}
        case SCon{x, u}:
          SCon{c, SCon{x, u}}
    case False{}:
      SCon{c, r}

# R1: s without all its trailing chars ch
def mu_trail(s: String, +ch: Char) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      mu_trail.at(Char.is_eq(c, ch), c, mu_trail(t, ch))

# R1
def mu_bare(h: String) -> String:
  String.to_lower(mu_trail(mu_lead(h, '['), ']'))

def mu_plus.at(b: Bool, c: Char, t: String) -> String:
  match b:
    case True{}:
      t
    case False{}:
      SCon{c, t}

# R3, R5: s without its one leading `+`
def mu_plus(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      mu_plus.at(Char.is_eq(c, '+'), c, t)

# R3: every char is a decimal digit (codes 48-57)
def mu_decs(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(Char.is_digit(c), mu_decs(t))

# R5: every char is a hex digit (codes 48-57, 97-102: after R1, no
#     uppercase letter is left)
def mu_hex_char(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)), Bool.and(U32.is_ge(x, 97), U32.is_le(x, 102)))

def mu_hexs(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(mu_hex_char(c), mu_hexs(t))

# R3: the value of decimal digits after v
def mu_dval(s: String, v: U32) -> U32:
  match s:
    case SNil{}:
      v
    case SCon{c, t}:
      mu_dval(t, U32.add(U32.mul(v, 10), U32.sub(Char.to_u32(c), 48)))

# R5: the value of a hex digit: a decimal digit's code less 48, a letter's
#     code less 87 (a is 10)
def mu_hdigit.at(b: Bool, x: U32) -> U32:
  match b:
    case True{}:
      U32.sub(x, 48)
    case False{}:
      U32.sub(x, 87)

def mu_hdigit(c: Char) -> U32:
  match c:
    case Chr{+x}:
      mu_hdigit.at(U32.is_le(x, 57), x)

# R5: the value of hex digits after v
def mu_hval(s: String, v: U32) -> U32:
  match s:
    case SNil{}:
      v
    case SCon{c, t}:
      mu_hval(t, U32.add(U32.mul(v, 16), mu_hdigit(c)))

# R3: a part of significant digits g, by its digit count
def mu_sig.ten(b: Bool) -> Mu.Part:
  match b:
    case True{}:
      Mu.PBig{}
    case False{}:
      Mu.PNone{}

def mu_sig.mid(b: Bool, +g: String) -> Mu.Part:
  match b:
    case True{}:
      Mu.PBig{}
    case False{}:
      mu_sig.ten(Bool.and(Nat.is_eq(String.length(g), 10n), String.is_le(g, "4294967295")))

def mu_sig.val(b: Bool, v: U32) -> Mu.Part:
  match b:
    case True{}:
      Mu.POct{v}
    case False{}:
      Mu.PBig{}

def mu_sig.short(b: Bool, +g: String) -> Mu.Part:
  match b:
    case True{}:
      +v = mu_dval(g, 0)
      mu_sig.val(U32.is_le(v, 255), v)
    case False{}:
      mu_sig.mid(Nat.is_le(String.length(g), 9n), g)

def mu_sig(+g: String) -> Mu.Part:
  mu_sig.short(Nat.is_le(String.length(g), 3n), g)

def mu_part.at(b: Bool, d: String) -> Mu.Part:
  match b:
    case True{}:
      mu_sig(mu_lead(d, '0'))
    case False{}:
      Mu.PNone{}

# R3
def mu_part(s: String) -> Mu.Part:
  +d = mu_plus(s)
  mu_part.at(Bool.and(Bool.not(String.is_empty(d)), mu_decs(d)), d)

# R4: read the parts in order; the first that is no octet decides
def mu_quad.d(a: U32, b: U32, c: U32, s: Mu.Part) -> Mu.V4:
  match s:
    case Mu.POct{d}:
      Mu.V4Quad{a, b, c, d}
    case Mu.PBig{}:
      Mu.V4Bad{}
    case Mu.PNone{}:
      Mu.V4No{}

def mu_quad.c(a: U32, b: U32, r: Mu.Part, s: Mu.Part) -> Mu.V4:
  match r:
    case Mu.POct{c}:
      mu_quad.d(a, b, c, s)
    case Mu.PBig{}:
      Mu.V4Bad{}
    case Mu.PNone{}:
      Mu.V4No{}

def mu_quad.b(a: U32, q: Mu.Part, r: Mu.Part, s: Mu.Part) -> Mu.V4:
  match q:
    case Mu.POct{b}:
      mu_quad.c(a, b, r, s)
    case Mu.PBig{}:
      Mu.V4Bad{}
    case Mu.PNone{}:
      Mu.V4No{}

def mu_quad(p: Mu.Part, q: Mu.Part, r: Mu.Part, s: Mu.Part) -> Mu.V4:
  match p:
    case Mu.POct{a}:
      mu_quad.b(a, q, r, s)
    case Mu.PBig{}:
      Mu.V4Bad{}
    case Mu.PNone{}:
      Mu.V4No{}

# R4: exactly four parts
def mu_v4.parts(ps: List<&2, String>) -> Mu.V4:
  match ps:
    case Nil{}:
      Mu.V4No{}
    case p <> t1:
      match t1:
        case Nil{}:
          Mu.V4No{}
        case q <> t2:
          match t2:
            case Nil{}:
              Mu.V4No{}
            case r <> t3:
              match t3:
                case Nil{}:
                  Mu.V4No{}
                case s <> t4:
                  match t4:
                    case Nil{}:
                      mu_quad(mu_part(p), mu_part(q), mu_part(r), mu_part(s))
                    case x <> t5:
                      Mu.V4No{}

# R4: x is in lo..hi
def mu_in(+x: U32, lo: U32, hi: U32) -> Bool:
  Bool.and(U32.is_ge(x, lo), U32.is_le(x, hi))

# R4: the refused ranges, by the first two octets
def mu_private(+a: U32, +b: U32) -> Bool:
  Bool.or(Bool.or(U32.is_eq(a, 127), Bool.or(U32.is_eq(a, 10), U32.is_eq(a, 0))), Bool.or(Bool.and(U32.is_eq(a, 172), mu_in(b, 16, 31)), Bool.or(Bool.and(U32.is_eq(a, 192), U32.is_eq(b, 168)), Bool.and(U32.is_eq(a, 169), U32.is_eq(b, 254)))))

# R5: a word
def mu_word.sig(b: Bool, g: String) -> Maybe<&2, U32>:
  match b:
    case True{}:
      Some{mu_hval(g, 0)}
    case False{}:
      None{}

def mu_word.at(b: Bool, d: String) -> Maybe<&2, U32>:
  match b:
    case True{}:
      +g = mu_lead(d, '0')
      mu_word.sig(Nat.is_le(String.length(g), 4n), g)
    case False{}:
      None{}

def mu_word(s: String) -> Maybe<&2, U32>:
  match s:
    case SNil{}:
      Some{0}
    case SCon{c, t}:
      +d = mu_plus(SCon{c, t})
      mu_word.at(Bool.and(Bool.not(String.is_empty(d)), mu_hexs(d)), d)

def mu_words.cons(m: Maybe<&2, U32>, r: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{w}:
      match r:
        case None{}:
          None{}
        case Some{ws}:
          Some{w <> ws}

# R5: the words of the parts; None when one is malformed
def mu_words(ps: List<&2, String>) -> Maybe<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      Some{Nil{}}
    case p <> t:
      mu_words.cons(mu_word(p), mu_words(t))

# R5: n zero words
def mu_zeros(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      0 <> mu_zeros(p)

def mu_any_empty(ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> t:
      Bool.or(String.is_empty(p), mu_any_empty(t))

def mu_halves.push(c: Char, h: Mu.Halves) -> Mu.Halves:
  match h:
    case Mu.One{a}:
      Mu.One{SCon{c, a}}
    case Mu.Two{a, b}:
      Mu.Two{SCon{c, a}, b}

def mu_halves.at(b: Bool, c: Char, t: String, r: Mu.Halves) -> Mu.Halves:
  match b:
    case True{}:
      Mu.Two{SNil{}, String.drop(t, 1n)}
    case False{}:
      mu_halves.push(c, r)

# R5: the text before and after the first `::`
def mu_halves(s: String) -> Mu.Halves:
  match s:
    case SNil{}:
      Mu.One{SNil{}}
    case SCon{+c, +t}:
      mu_halves.at(Bool.and(Char.is_eq(c, ':'), String.starts_with(t, ":")), c, t, mu_halves(t))

# R5: a side's parts
def mu_side(s: String) -> List<&2, String>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      String.split(SCon{c, t}, ':')

def mu_join(a: Maybe<&2, List<&2, U32>>, z: List<&2, U32>, b: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match a:
    case None{}:
      None{}
    case Some{x}:
      match b:
        case None{}:
          None{}
        case Some{y}:
          Some{List.append(&2, U32, x, List.append(&2, U32, z, y))}

def mu_two.at(b: Bool, hp: List<&2, String>, tp: List<&2, String>, n: Nat) -> Maybe<&2, List<&2, U32>>:
  match b:
    case True{}:
      mu_join(mu_words(hp), mu_zeros(Nat.sub(8n, n)), mu_words(tp))
    case False{}:
      None{}

def mu_two(+hp: List<&2, String>, +tp: List<&2, String>) -> Maybe<&2, List<&2, U32>>:
  +n = Nat.add(List.length(&2, String, hp), List.length(&2, String, tp))
  mu_two.at(Nat.is_le(n, 7n), hp, tp, n)

def mu_one.at(b: Bool, ps: List<&2, String>) -> Maybe<&2, List<&2, U32>>:
  match b:
    case True{}:
      mu_words(ps)
    case False{}:
      None{}

def mu_one(+ps: List<&2, String>) -> Maybe<&2, List<&2, U32>>:
  mu_one.at(Bool.and(Nat.is_eq(List.length(&2, String, ps), 8n), Bool.not(mu_any_empty(ps))), ps)

def mu_expand.of(h: Mu.Halves) -> Maybe<&2, List<&2, U32>>:
  match h:
    case Mu.One{a}:
      mu_one(mu_side(a))
    case Mu.Two{a, b}:
      mu_two(mu_side(a), mu_side(b))

# R5: the eight words; None when malformed
def mu_expand(s: String) -> Maybe<&2, List<&2, U32>>:
  mu_expand.of(mu_halves(s))

# R6: the refused ranges over the eight words
def mu_ranges(+w0: U32, +w1: U32, +w2: U32, +w3: U32, +w4: U32, +w5: U32, +w6: U32, +w7: U32) -> Bool:
  +z5 = Bool.and(U32.is_eq(w0, 0), Bool.and(U32.is_eq(w1, 0), Bool.and(U32.is_eq(w2, 0), Bool.and(U32.is_eq(w3, 0), U32.is_eq(w4, 0)))))
  +z7 = Bool.and(z5, Bool.and(U32.is_eq(w5, 0), U32.is_eq(w6, 0)))
  Bool.or(Bool.and(z7, Bool.or(U32.is_eq(w7, 0), U32.is_eq(w7, 1))), Bool.or(Bool.and(z5, Bool.and(U32.is_eq(w5, 65535), mu_private(U32.shrn(w6, 8n), U32.and(w6, 255)))), Bool.or(mu_in(w0, 65152, 65215), mu_in(w0, 64512, 65023))))

# R6: eight words (expand never answers another count)
def mu_eight(ws: List<&2, U32>) -> Bool:
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
                                      mu_ranges(w0, w1, w2, w3, w4, w5, w6, w7)
                                    case x <> t8:
                                      True{}

def mu_v6(m: Maybe<&2, List<&2, U32>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{ws}:
      mu_eight(ws)

def mu_v6.at(b: Bool, s: String) -> Bool:
  match b:
    case True{}:
      mu_v6(mu_expand(s))
    case False{}:
      False{}

def mu_after(v: Mu.V4, +s: String) -> Bool:
  match v:
    case Mu.V4No{}:
      mu_v6.at(String.contains(s, ":"), s)
    case Mu.V4Bad{}:
      True{}
    case Mu.V4Quad{a, b, c, d}:
      mu_private(a, b)

def mu_refused.at(named: Bool, +s: String) -> Bool:
  match named:
    case True{}:
      True{}
    case False{}:
      mu_after(mu_v4.parts(String.split(s, '.')), s)

# R1-R7: whether the host h is refused
def mu_refused(h: String) -> Bool:
  +s = mu_bare(h)
  mu_refused.at(Bool.or(String.eq(s, "localhost"), String.ends_with(s, ".localhost")), s)

# R8: the spelling of a request and its reply
def mu_w_req(h: String, rest: String) -> String:
  Wr.put_str(h, rest)

def mu_w_reply(h: String) -> String:
  Wr.put_bool(mu_refused(h), "")

# Laws: the check
# ---------------

# LAW mcp_url_spec (R1-R7): whether every host is refused is the spec's
# EXCLUDES: brackets kept, a case-sensitive host, `localhost` passed, a
#   quad of other parts or with a part past 255 passed, a part past u32
#   refusing, a `+` refused or a lone `+` read as 0, a wrong range bound,
#   an IPv6 split at its last `::`, an empty word refused, a word past
#   ffff read, a malformed address passed, :: or ::1 passed, a mapped
#   private address passed, fe80::/10 or fc00::/7 passed
law mcp_url_spec:
  for +h: String
  {Mu.refused(h) == mu_refused(h) : Bool}

# LAW mcp_url_refuses_example (R1-R6): anchor: hosts Rust refused, and the
# mapped loopback the fix refuses
# EXCLUDES: a spec that drifts from the Rust it replaced
law mcp_url_refuses_example:
  {[Mu.refused("localhost"), Mu.refused("LocalHost"), Mu.refused("a.localhost"), Mu.refused("127.0.0.1"), Mu.refused("10.0.0.5"), Mu.refused("0.0.0.0"), Mu.refused("172.16.1.2"), Mu.refused("192.168.0.1"), Mu.refused("169.254.1.1"), Mu.refused("999.1.1.1"), Mu.refused("[::1]"), Mu.refused("[::]"), Mu.refused("[fe80::1]"), Mu.refused("[fc00::1]"), Mu.refused("[fd12::1]"), Mu.refused("[zz::1]"), Mu.refused("[::ffff:7f00:1]")] == [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}] : List<&2, Bool>}

# LAW mcp_url_passes_example (R3-R7): anchor: hosts Rust passed
# EXCLUDES: a spec that drifts from the Rust it replaced
law mcp_url_passes_example:
  {[Mu.refused("mcp.linear.app"), Mu.refused("8.8.8.8"), Mu.refused("172.32.0.1"), Mu.refused("[2606:4700::6810:85e5]"), Mu.refused("[2001:db8::1]"), Mu.refused("x.999.1.1"), Mu.refused("+8.8.8.8"), Mu.refused("[::ffff:808:808]")] == [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] : List<&2, Bool>}

# Laws: the entry (R8)
# --------------------

# LAW mcp_url_entry_answers (R8): the entry answers every host Rust
# spells, its length within the wire, with the spec's verdict
# EXCLUDES: another verdict, a verdict spelled otherwise, a default
law mcp_url_entry_answers:
  for +h: String
  for fit: {LawsBase.wire_fits(String.length(h)) == True{} : Bool}
  {FMu.ffi(mu_w_req(h, "")) == mu_w_reply(h) : String}

# LAW mcp_url_entry_exact (R8): every input the entry does not answer with
# the error form is a spelled host that fits the wire
# EXCLUDES: a verdict on input that is no request (a short host, input
#   left over)
law mcp_url_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FMu.ffi(s)) == False{} : Bool}
  exs h: String
  {s == mu_w_req(h, "") : String} & {LawsBase.wire_fits(String.length(h)) == True{} : Bool}

# LAW mcp_url_entry_refuses (R8): every error the entry answers is exactly
# `E mcp_url: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law mcp_url_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FMu.ffi(s)) == True{} : Bool}
  {FMu.ffi(s) == Wr.err("mcp_url: malformed request") : String}

# LAW mcp_url_entry_left_over (R8): a spelled host followed by more input
# answers the error form
# EXCLUDES: the input after the request ignored or read into the host
law mcp_url_entry_left_over:
  for +h: String
  for +c: Char
  for +t: String
  for fit: {LawsBase.wire_fits(String.length(h)) == True{} : Bool}
  {FMu.ffi(mu_w_req(h, SCon{c, t})) == Wr.err("mcp_url: malformed request") : String}

# LAW mcp_url_entry_example (R8): anchor: the wire strings Rust sends and
# the replies it reads; input left over and a malformed request
# EXCLUDES: another spelling of a request or of a reply
law mcp_url_entry_example:
  {[FMu.ffi("9,127.0.0.1"), FMu.ffi("7,8.8.8.8"), FMu.ffi("7,8.8.8.8x"), FMu.ffi("x")] == ["T", "F", Wr.err("mcp_url: malformed request"), Wr.err("mcp_url: malformed request")] : List<&2, String>}
