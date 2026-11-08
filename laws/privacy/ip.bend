# eukhe: the laws of area privacy, section ip: which text at a candidate
# position of the outbound scrubber is an IP address (bend/privacy/ip.bend,
# bend/privacy/context.bend)

import Base
import ../../bend/privacy/ip.bend as Ip
import ../../bend/privacy/context.bend as Cx
import ../../spec/harness/privacy.bend as S
import ../../spec/harness/privacy_context.bend as Sv

# (H7) The outbound scrubber rewrites no code
# -------------------------------------------
# spec/README.md H7. The scrubber (privacy.anonymizeRemote, eukhe-ai
# privacy) once took any `::` as an IPv6 (CSS `a::before` left as
# `aIP_4d040core`, every Rust `std::sync` path rewritten) and versions and
# loopback as IPv4 (`127.0.0.1` left as `IP_12ca17`, and the model typed
# that into a URL). Its IP grammar now runs as the compiled core
# (bend/ffi_privacy.bend's call, asked by eukhe-ai privacy/detect.rs for
# every position that could start an address): Ip.ip(before, rest).
# spec/harness/privacy.bend restates it (S1-S3) as the text a structured
# address writes. Every input is free: any text before, any text from the
# position.
#
# R1: an IPv6 is taken exactly when it is a shaped address (S1) with a
#     digit-bearing group and eight groups, or three to seven around a
#     `::`, that no word char, `:` or `.` touches on either side, and
#     whose value is no loopback, unspecified or reserved IPv4 (S3, R3);
#     its answer is its length. Nothing else is taken as an IPv6.
# R2: an IPv4 is taken exactly when it is four octets (S2), its first not
#     0, 127 or 255, with no word char or `.` before it, no product name
#     and `/`, no version context (S7, spec/harness/privacy_context.bend),
#     and no word char after it, nor `.` or `-` and a letter or digit
#     (S3). Nothing else is taken as an IPv4.
# R3: code is no address: a `::` path or pseudo-element (no digit, fewer
#     than three groups, a word char before it), a version (three parts, a
#     fifth part, a version word or operator before it), a loopback,
#     unspecified or mask address: an IPv6 in any written form whose value
#     is the loopback `::1`, the unspecified `::`, or an IPv4 compatible
#     (`::/96`) or mapped (`::ffff:0:0/96`) whose first octet is 0, 127 or
#     255 (S3).
# R11: an address is taken exactly when it is the IPv6 or the IPv4 at the
#     position (R1, R2); a version's context is exactly the spec's (S7):
#     a plain assignment (`host = `) is none.

# Laws: IPv6 (R1)
# ---------------

# LAW privacy_ipv6_decides (R1): every shaped IPv6 written after any text,
# then followed by a char that does not go on with it (or nothing), is
# taken exactly as the spec takes it, with its length
# EXCLUDES: any `::` taken as an address (the old regex: `a::before`,
#   `std::sync::Arc`, `dead::beef`), an address with no decimal digit or
#   with fewer than three groups around `::` taken, nine groups taken, a
#   word char, `:` or `.` before or after ignored, a valid address
#   refused, a wrong length
law privacy_ipv6_decides:
  for +a: Ip.Addr
  for +before: String
  for +t: String
  for +sh: {S.shaped(a) == True{} : Bool}
  for +st: {S.stops6(t) == True{} : Bool}
  {Ip.v6(before, S.text6(a, t)) == S.take6(a, before, t) : Maybe<&2, Nat>}

# LAW privacy_ipv6_exact (R1): every IPv6 the grammar takes is a shaped
# address written there, followed by a char that does not go on with it,
# that the spec takes, with that length
# EXCLUDES: anything taken that is no address (a group of five digits, a
#   second `::`, a `:` at the end, a hex word glued to it), a length that
#   cuts an address or runs past it
law privacy_ipv6_exact:
  for +before: String
  for +s: String
  for +n: Nat
  for +h: {Ip.v6(before, s) == Some{n} : Maybe<&2, Nat>}
  exs a: Ip.Addr
  exs t: String
  {s == S.text6(a, t) : String} & ({S.shaped(a) == True{} : Bool} & ({S.stops6(t) == True{} : Bool} & {S.take6(a, before, t) == Some{n} : Maybe<&2, Nat>}))

# LAW privacy_ipv6_needs_digit (R3): a `::` path whose groups hold no
# decimal digit is no address of any kind, whatever comes before it
# EXCLUDES: `dead::beef`, `cafe::babe::face()`, `a::b::c`, a CSS
#   `::selection` taken as an IPv6 or an IPv4
law privacy_ipv6_needs_digit:
  for +a: Ip.Addr
  for +before: String
  for +t: String
  for +sh: {S.shaped(a) == True{} : Bool}
  for +st: {S.stops6(t) == True{} : Bool}
  for +nd: {S.digit(a) == False{} : Bool}
  {Ip.ip(before, S.text6(a, t)) == None{} : Maybe<&2, Nat>}

# LAW privacy_ipv6_needs_three (R3): a `::` with fewer than three explicit
# groups around it (an IPv4 counts two) is no address of any kind
# EXCLUDES: `a::b`, `xs[1::2]`, the loopback `::1`, the link-local
#   `fe80::1`, `fd::dup2` taken as an IPv6 or an IPv4
law privacy_ipv6_needs_three:
  for +l: List<&2, String>
  for +r: List<&2, String>
  for +q: Maybe<&2, Ip.Quad>
  for +before: String
  for +t: String
  for +sh: {S.shaped(Ip.Gap{l, r, q}) == True{} : Bool}
  for +st: {S.stops6(t) == True{} : Bool}
  for +few: {S.counted(Ip.Gap{l, r, q}) == False{} : Bool}
  {Ip.ip(before, S.text6(Ip.Gap{l, r, q}, t)) == None{} : Maybe<&2, Nat>}

# LAW privacy_ipv6_loopback_any_form (R3): every written form of the
# loopback `::1` and the unspecified `::` (eight groups, a `::` anywhere,
# leading zeros, an IPv4 `0.0.0.1` last) is no address of any kind,
# whatever comes before it: every address whose value is 31 zero hex
# digits then any last one (so `::2` to `::f`, the IPv4-compatible
# 0.0.0.2 to 0.0.0.15, too)
# EXCLUDES: `0:0:0:0:0:0:0:1`, `0:0:0:0:0:0:0:0`, `0:0:0::1`,
#   `0000:0000:0000:0000:0000:0000:0000:0001`, `0:0::0:0:1`,
#   `0:0:0:0:0:0:0.0.0.1` taken (H7: no loopback or unspecified address
#   is an IP address); a grammar that checks only the shape of an IPv6
law privacy_ipv6_loopback_any_form:
  for +a: Ip.Addr
  for +d: Char
  for +before: String
  for +t: String
  for +sh: {S.shaped(a) == True{} : Bool}
  for +st: {S.stops6(t) == True{} : Bool}
  for +lo: {S.value6(a) == String.append("0000000000000000000000000000000", SCon{d, SNil{}}) : String}
  {Ip.ip(before, S.text6(a, t)) == None{} : Maybe<&2, Nat>}

# LAW privacy_ipv6_mapped_reserved (R3): every IPv6 whose value is an
# IPv4 compatible (`::/96`, mapped false) or mapped (`::ffff:0:0/96`,
# mapped true) whose first octet is 0, 127 or 255 (hex 00, 7f, ff: the
# reserved IPv4s of privacy_ipv4_reserved), its IPv4 written in dots or in
# hex, is no address of any kind, whatever comes before it
# EXCLUDES: `::ffff:127.0.0.1`, `0:0:0:0:0:ffff:7f00:1`, `::ffff:0.1.2.3`,
#   `0:0::255.1.2.3` taken, a loopback IPv4 left in clear only when it is
#   written alone
law privacy_ipv6_mapped_reserved:
  for +a: Ip.Addr
  for +mapped: Bool
  for +rest: String
  for +before: String
  for +t: String
  for +sh: {S.shaped(a) == True{} : Bool}
  for +st: {S.stops6(t) == True{} : Bool}
  ({S.value6(a) == String.append(S.prefix96(mapped), String.append("00", rest)) : String} -> {Ip.ip(before, S.text6(a, t)) == None{} : Maybe<&2, Nat>}) & (({S.value6(a) == String.append(S.prefix96(mapped), String.append("7f", rest)) : String} -> {Ip.ip(before, S.text6(a, t)) == None{} : Maybe<&2, Nat>}) & ({S.value6(a) == String.append(S.prefix96(mapped), String.append("ff", rest)) : String} -> {Ip.ip(before, S.text6(a, t)) == None{} : Maybe<&2, Nat>}))

# LAW privacy_ip_boundary (R1, R2, R3): after a word char nothing is an
# address, whatever follows
# EXCLUDES: `a::before` read from its first `:`, `v10.0.0.1` read from
#   its `1`, an address glued to the identifier before it
law privacy_ip_boundary:
  for +p: String
  for +c: Char
  for +rest: String
  for +w: {S.k_word(S.kind(c)) == True{} : Bool}
  {Ip.ip(String.append(p, SCon{c, SNil{}}), rest) == None{} : Maybe<&2, Nat>}

# Laws: IPv4 (R2)
# ---------------

# LAW privacy_ipv4_decides (R2): every four octets written after any text,
# then followed by no decimal digit, are taken exactly as the spec takes
# them (with the grammar's version context), with their length
# EXCLUDES: a loopback, unspecified or mask address taken, a fifth part or
#   a pre-release taken, a product version (`Chrome/120.0.0.0`) taken, a
#   word char or `.` before or after ignored, a public address refused, a
#   wrong length
law privacy_ipv4_decides:
  for +q: Ip.Quad
  for +before: String
  for +t: String
  for +ok: {S.quad_ok(q) == True{} : Bool}
  for +st: {S.stops4(t) == True{} : Bool}
  {Ip.v4(before, S.quad_text(q, t)) == S.take4(q, before, t, Cx.vctx(before)) : Maybe<&2, Nat>}

# LAW privacy_ipv4_exact (R2): every IPv4 the grammar takes is four octets
# written there, followed by no decimal digit, that the spec takes, with
# that length
# EXCLUDES: three or five parts, an octet past 255 or with a leading zero,
#   a length that cuts an address or runs past it
law privacy_ipv4_exact:
  for +before: String
  for +s: String
  for +n: Nat
  for +h: {Ip.v4(before, s) == Some{n} : Maybe<&2, Nat>}
  exs q: Ip.Quad
  exs t: String
  {s == S.quad_text(q, t) : String} & ({S.quad_ok(q) == True{} : Bool} & ({S.stops4(t) == True{} : Bool} & {S.take4(q, before, t, Cx.vctx(before)) == Some{n} : Maybe<&2, Nat>}))

# LAW privacy_ipv4_reserved (R3): an address starting 0., 127. or 255. is
# no address of any kind, whatever follows its first octet
# EXCLUDES: `127.0.0.1` scrubbed (the model typed `http://IP_12ca17:5180`),
#   `0.0.0.0:8080`, `255.255.255.0` taken
law privacy_ipv4_reserved:
  for +b: String
  for +c: String
  for +d: String
  for +before: String
  for +t: String
  {Ip.ip(before, S.quad_text(Ip.Quad{"0", b, c, d}, t)) == None{} : Maybe<&2, Nat>} & ({Ip.ip(before, S.quad_text(Ip.Quad{"127", b, c, d}, t)) == None{} : Maybe<&2, Nat>} & {Ip.ip(before, S.quad_text(Ip.Quad{"255", b, c, d}, t)) == None{} : Maybe<&2, Nat>})

# LAW privacy_ipv4_version_context (R3): after a version word or a
# requirement operator (and blanks), at the end of any text, nothing is an
# IPv4
# EXCLUDES: `version = "1.2.3.4"`, `Version: 10.0.0.1`,
#   `numpy==1.26.4.1`, `django>=4.2.1.0`, `click~=8.1.7.2` taken
law privacy_ipv4_version_context:
  for +p: String
  for +s: String
  {Ip.v4(String.append(p, "version "), s) == None{} : Maybe<&2, Nat>} & ({Ip.v4(String.append(p, "Version: \""), s) == None{} : Maybe<&2, Nat>} & ({Ip.v4(String.append(p, "=="), s) == None{} : Maybe<&2, Nat>} & ({Ip.v4(String.append(p, ">="), s) == None{} : Maybe<&2, Nat>} & ({Ip.v4(String.append(p, "<="), s) == None{} : Maybe<&2, Nat>} & ({Ip.v4(String.append(p, "~="), s) == None{} : Maybe<&2, Nat>} & ({Ip.v4(String.append(p, "!="), s) == None{} : Maybe<&2, Nat>} & ({Ip.v4(String.append(p, "^"), s) == None{} : Maybe<&2, Nat>} & {Ip.v4(String.append(p, "~"), s) == None{} : Maybe<&2, Nat>})))))))

# LAW privacy_ipv4_version_context_spec (R2, R11): for every text before a
# position, the grammar's version context is the spec's (S7): the line,
# blanks dropped, ends with a requirement operator, or, punctuation
# dropped, its last word is a version word; nothing else is one
# EXCLUDES: `host = `, `server_ip = `, `"ip" = ` (a plain assignment)
#   read as version context, so the IPv4 after it leaves in clear; an
#   operator or a version word missed; a context read past the line's
#   newline
law privacy_ipv4_version_context_spec:
  for +before: String
  {Cx.vctx(before) == Sv.vctx(before) : Bool}

# LAW privacy_ipv4_three_parts (R3): three dotted octets followed by no
# word char, `:` or `.` (or nothing) are no address of any kind
# EXCLUDES: `1.2.3`, `go 1.21.0`, `v0.10.62` taken
law privacy_ipv4_three_parts:
  for +x: String
  for +y: String
  for +z: String
  for +before: String
  for +t: String
  for +ok: {Bool.and(S.octet(x), Bool.and(S.octet(y), S.octet(z))) == True{} : Bool}
  for +nd: {S.free(S.first(t)) == True{} : Bool}
  {Ip.ip(before, String.append(x, SCon{'.', String.append(y, SCon{'.', String.append(z, t)})})) == None{} : Maybe<&2, Nat>}

# LAW privacy_ip_v6_or_v4 (R11): the answer at a position is its IPv6
# (R1), else its IPv4 (R2)
# EXCLUDES: an IPv6 or an IPv4 the grammar takes dropped from the answer,
#   an answer that is neither
law privacy_ip_v6_or_v4:
  for +before: String
  for +rest: String
  {Ip.ip(before, rest) == Maybe.or(&2, Nat, Ip.v6(before, rest), Ip.v4(before, rest)) : Maybe<&2, Nat>}

# Anchors (R1-R3)
# ---------------

# LAW privacy_ip_code_example (R3): anchor: the candidates of the failures
# and of the corpus: `a::before` (from its start and from its `:`),
# `std::sync::Arc`, `dead::beef`, `xs[1::2]`, `::1`, `127.0.0.1` in a URL,
# versions (`1.2.3`, `v10.0.0.1`, `version = "1.2.3.4"`, `Version:
# 10.0.0.1`, `Chrome/120.0.0.0`, `1.2.3.4.5`) are no address
# EXCLUDES: a law that holds only for shapes no code has
law privacy_ip_code_example:
  {[Ip.ip("", "a::before {"), Ip.ip("a", "::before {"), Ip.ip("", "std::sync::Arc"), Ip.ip("std", "::sync::Arc"), Ip.ip("", "dead::beef"), Ip.ip("xs[1", "::2]"), Ip.ip("bind [", "::1]:9000"), Ip.ip("http://", "127.0.0.1:5180"), Ip.ip("", "1.2.3 x"), Ip.ip("v", "10.0.0.1"), Ip.ip("version = \"", "1.2.3.4\""), Ip.ip("Version: ", "10.0.0.1"), Ip.ip("Mozilla/5.0 Chrome/", "120.0.0.0 x"), Ip.ip("", "1.2.3.4.5")] == [None{}, None{}, None{}, None{}, None{}, None{}, None{}, None{}, None{}, None{}, None{}, None{}, None{}, None{}] : List<&2, Maybe<&2, Nat>>}

# LAW privacy_ip_personal_example (R1, R2): anchor: the addresses of the
# corpus are taken whole: an IPv4 after `@` and after a space, an IPv6 in
# brackets, an IPv4-mapped IPv6, an IPv4 that ends a sentence
# EXCLUDES: a grammar so strict it takes no address
law privacy_ip_personal_example:
  {[Ip.ip("ssh deploy@", "203.0.113.7"), Ip.ip("server ", "10.0.0.7 refused"), Ip.ip("upstream [", "2001:db8::8a2e:370:7334]:443"), Ip.ip("mapped ", "::ffff:192.0.2.128 here"), Ip.ip("ping ", "192.168.1.20. ")] == [Some{11n}, Some{8n}, Some{23n}, Some{18n}, Some{12n}] : List<&2, Maybe<&2, Nat>>}

# LAW privacy_ip_assignment_example (R2, R11): anchor: an IPv4 after a
# plain assignment (`host = `, `server_ip = `, `"ip" = `, `x = ` on a
# second line after a version) is taken whole, and the spec reads no
# version context there; after `version = "`, `numpy==` and `ver ` it
# reads one
# EXCLUDES: an `=` with blanks before it read as a requirement operator
#   (the scrubber leaked `host = 203.0.113.9`)
law privacy_ip_assignment_example:
  {[Ip.ip("host = ", "203.0.113.9"), Ip.ip("server_ip = ", "10.1.2.3"), Ip.ip("\"ip\" = ", "198.51.100.4"), Ip.ip("version = \"1.2.3\"\nx = ", "192.0.2.1")] == [Some{11n}, Some{8n}, Some{12n}, Some{9n}] : List<&2, Maybe<&2, Nat>>} & {[Sv.vctx("host = "), Sv.vctx("server_ip = "), Sv.vctx("\"ip\" = "), Sv.vctx("version = \""), Sv.vctx("numpy=="), Sv.vctx("ver ")] == [False{}, False{}, False{}, True{}, True{}, True{}] : List<&2, Bool>}

# LAW privacy_ipv6_reserved_example (R1, R3): anchor: the addresses the
# shape alone took (the full-form loopback and unspecified, `0:0:0::1`,
# the IPv4-mapped loopback), and other forms of them (leading zeros, a
# `::` inside, an IPv4 `0.0.0.1`, the mapped loopback in hex, mapped 0.x,
# compatible 255.x) are no address; a public IPv4 mapped (in hex), a
# mapped 126.x and a `::fffe:` prefix are taken whole
# EXCLUDES: a law that holds only for shapes no text has; a refusal so
#   wide it drops a public mapped address
law privacy_ipv6_reserved_example:
  {[Ip.ip("connect ", "0:0:0:0:0:0:0:1 now"), Ip.ip("bind ", "0:0:0:0:0:0:0:0 now"), Ip.ip("connect ", "0:0:0::1 now"), Ip.ip("connect ", "::ffff:127.0.0.1 now"), Ip.ip("x ", "0000:0000:0000:0000:0000:0000:0000:0001"), Ip.ip("x ", "0:0::0:0:1"), Ip.ip("x ", "0:0:0:0:0:0:0.0.0.1"), Ip.ip("x ", "0:0:0:0:0:FFFF:7F00:1"), Ip.ip("x ", "::ffff:0.1.2.3"), Ip.ip("x ", "0:0::255.1.2.3"), Ip.ip("x ", "::ffff:c000:280"), Ip.ip("x ", "::ffff:126.0.0.1"), Ip.ip("x ", "::fffe:127.0.0.1")] == [None{}, None{}, None{}, None{}, None{}, None{}, None{}, None{}, None{}, None{}, Some{15n}, Some{16n}, Some{16n}] : List<&2, Maybe<&2, Nat>>}
