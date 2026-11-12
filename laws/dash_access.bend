# eukhe: the laws of area dash_access

import Base
import ../bend/dash_access.bend as Ac
import ../bend/ffi_dash_access.bend as FAc
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (D1) Who may reach the dashboard
# --------------------------------
# bend/dash_access.bend, run as the compiled core by
# bend/ffi_dash_access.bend (crates/eukhe-dashboard access.rs, called by
# http.rs and bridge.rs for every request and WebSocket upgrade). Every
# input is free: any `Host`, any `Origin`, any list of allowed hosts.
#
# R1: an authority `host[:port]` (Rust `split_authority`) is none when it
#     is empty or holds '@', '/', '?', '#' or a space. A text that starts
#     with '[' is an IPv6 literal: the host runs to its first ']'
#     (brackets kept); after it comes nothing, or ':' and a port. Any
#     other text splits at its last ':' (Rust `rsplit_once`): the host
#     before it, the port after it; with no ':' it is all host. A host
#     that is empty, or holds a ':' without starting with '[', makes no
#     authority. A port is Rust's `u16::from_str`: an optional '+', then
#     one or more decimal digits worth at most 65535 (leading zeros
#     allowed); any other port text makes no authority.
# R2: a `Host` is allowed when it is an authority whose host is, but for
#     ASCII case, 127.0.0.1, localhost, [::1], or one of the allowed hosts
#     (any port).
# R3: an `Origin` matches a `Host` when it is `<scheme>://<authority>`
#     (cut at its first "://"), the scheme is http or https in any ASCII
#     case, both authorities are authorities (R1), their hosts are the same
#     but for ASCII case, and their ports are the same once the scheme's
#     default port (http 80, https 443) fills in a missing one.
# R4: the entry answers each request Rust writes (R2 or R3, every length
#     within the wire) with the verdict, reads exactly the request and
#     nothing after it, and answers any other input with the exact error
#     form `E dash_access: malformed request`.

# Spec helpers
# ------------
# An authority is stated by how it is written (sp_spell) and what makes
# its writing well formed (sp_well), from the words of R1; the laws say
# the code reads exactly the well-formed writings, and no other text.

# R1: a char no authority holds
def sp_forbidden(+c: Char) -> Bool:
  Bool.or(Char.is_eq(c, '@'), Bool.or(Char.is_eq(c, '/'), Bool.or(Char.is_eq(c, '?'), Bool.or(Char.is_eq(c, '#'), Char.is_eq(c, ' ')))))

# R1: s holds a char no authority holds
def sp_holds(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.or(sp_forbidden(c), sp_holds(t))

# s holds the char k
def sp_has(s: String, +k: Char) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.or(Char.is_eq(c, k), sp_has(t, k))

# R1: every char of s is a decimal digit
def sp_all_digits(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(Char.is_digit(c), sp_all_digits(t))

def sp_value.go(s: String, +acc: Nat) -> Nat:
  match s:
    case SNil{}:
      acc
    case SCon{c, t}:
      sp_value.go(t, Nat.add(Nat.mul(10n, acc), U32.to_nat(U32.sub(Char.to_u32(c), 48))))

# R1: the decimal value of the digits s after acc (no bound: the law
# bounds it)
def sp_value(+acc: Nat, s: String) -> Nat:
  sp_value.go(s, acc)

# R1: a port as written after its ':': an optional '+', then the digits
type SpPort is Data:
  SpPort{plus: Bool, digits: String}

# R1: an authority as written: a host that is not bracketed, or the inside
# of an IPv6 literal's brackets; then a port, if one is written
type SpAuth is Data:
  SpPlain{host: String, port: Maybe<&2, SpPort>}
  SpBracket{inside: String, port: Maybe<&2, SpPort>}

def sp_sign(plus: Bool, ds: String) -> String:
  match plus:
    case True{}:
      SCon{'+', ds}
    case False{}:
      ds

# R1: the text of a port, with its ':'
def sp_port_text(p: Maybe<&2, SpPort>) -> String:
  match p:
    case None{}:
      SNil{}
    case Some{q}:
      match q:
        case SpPort{plus, ds}:
          SCon{':', sp_sign(plus, ds)}

# R1: the text of an authority
def sp_spell(a: SpAuth) -> String:
  match a:
    case SpPlain{h, p}:
      String.append(h, sp_port_text(p))
    case SpBracket{i, p}:
      SCon{'[', String.append(i, SCon{']', sp_port_text(p)})}

# R1: its host (an IPv6 literal keeps its brackets)
def sp_name(a: SpAuth) -> String:
  match a:
    case SpPlain{h, p}:
      h
    case SpBracket{i, p}:
      SCon{'[', String.append(i, "]")}

def sp_port_of(p: Maybe<&2, SpPort>) -> Maybe<&2, Nat>:
  match p:
    case None{}:
      None{}
    case Some{q}:
      match q:
        case SpPort{plus, ds}:
          Some{sp_value(0n, ds)}

# R1: its port's value, if a port is written
def sp_port(a: SpAuth) -> Maybe<&2, Nat>:
  match a:
    case SpPlain{h, p}:
      sp_port_of(p)
    case SpBracket{i, p}:
      sp_port_of(p)

# R1: a port is one or more digits worth at most 65535
def sp_port_ok(p: Maybe<&2, SpPort>) -> Bool:
  match p:
    case None{}:
      True{}
    case Some{q}:
      match q:
        case SpPort{plus, +ds}:
          Bool.and(Bool.not(String.is_empty(ds)), Bool.and(sp_all_digits(ds), Nat.is_le(sp_value(0n, ds), 65535n)))

# R1: a host that is not bracketed: not empty, not starting with '[', no
# ':'
def sp_plain_ok(h: String) -> Bool:
  match h:
    case SNil{}:
      False{}
    case SCon{+c, t}:
      Bool.and(Bool.not(Char.is_eq(c, '[')), Bool.not(sp_has(SCon{c, t}, ':')))

def sp_well.parts(a: SpAuth) -> Bool:
  match a:
    case SpPlain{h, p}:
      Bool.and(sp_plain_ok(h), sp_port_ok(p))
    case SpBracket{i, p}:
      Bool.and(Bool.not(sp_has(i, ']')), sp_port_ok(p))

# R1: a well-formed authority: its host as above, the inside of brackets
# without ']', a well-formed port, and no char an authority never holds
def sp_well(+a: SpAuth) -> Bool:
  Bool.and(Bool.not(sp_holds(sp_spell(a))), sp_well.parts(a))

# R2: s with every ASCII capital made small
def sp_lower(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      SCon{Char.to_lower(c), sp_lower(t)}

# R2: a and b are equal but for ASCII case (Rust `eq_ignore_ascii_case`)
def sp_ci(a: String, b: String) -> Bool:
  LawsBase.text_same(sp_lower(a), sp_lower(b))

def sp_any_ci(+n: String, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(sp_ci(x, n), sp_any_ci(n, t))

# R2: the host n is a loopback name or one of the allowed hosts al
def sp_named(+n: String, al: List<&2, String>) -> Bool:
  sp_any_ci(n, "127.0.0.1" <> "localhost" <> "[::1]" <> al)

# R3: a scheme and its default port
type SpScheme is Data:
  SpScheme{name: String, port: Nat}

# R3: the schemes and their default ports (RFC 9110 4.2.1, 4.2.2: http 80,
# https 443)
def sp_schemes() -> List<&2, SpScheme>:
  [SpScheme{"http", 80n}, SpScheme{"https", 443n}]

def sp_scheme.at(b: Bool, d: Nat, r: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{d}
    case False{}:
      r

def sp_scheme.in(+sc: String, ts: List<&2, SpScheme>) -> Maybe<&2, Nat>:
  match ts:
    case Nil{}:
      None{}
    case t <> rest:
      match t:
        case SpScheme{w, d}:
          sp_scheme.at(sp_ci(sc, w), d, sp_scheme.in(sc, rest))

# R3: the default port of the scheme sc (any ASCII case), if it is one
def sp_scheme(+sc: String) -> Maybe<&2, Nat>:
  sp_scheme.in(sc, sp_schemes())

# R3: an `Origin` as written: scheme "://" authority
def sp_origin_text(sc: String, a: SpAuth) -> String:
  String.append(sc, SCon{':', SCon{'/', SCon{'/', sp_spell(a)}}})

def sp_port_or(m: Maybe<&2, Nat>, d: Nat) -> Nat:
  match m:
    case None{}:
      d
    case Some{n}:
      n

# R3: the page of a and the host b are the same site under the default
# port d: same host but for ASCII case, same port once d fills a missing
# one
def sp_same_site(+d: Nat, +a: SpAuth, +b: SpAuth) -> Bool:
  Bool.and(sp_ci(sp_name(a), sp_name(b)), Nat.is_eq(sp_port_or(sp_port(a), d), sp_port_or(sp_port(b), d)))

# R3: an origin as written, against a host
type SpOrigin is Data:
  SpOrigin{scheme: String, page: SpAuth, host: SpAuth}

def sp_o_origin(w: SpOrigin) -> String:
  match w:
    case SpOrigin{sc, a, b}:
      sp_origin_text(sc, a)

def sp_o_host(w: SpOrigin) -> String:
  match w:
    case SpOrigin{sc, a, b}:
      sp_spell(b)

# R3: both authorities well formed, the scheme http or https
def sp_o_ok(w: SpOrigin) -> Bool:
  match w:
    case SpOrigin{+sc, +a, +b}:
      Bool.and(Maybe.is_some(&2, Nat, sp_scheme(sc)), Bool.and(sp_well(a), sp_well(b)))

# R4: the spelling of a request and of its reply

def sp_w_req(q: FAc.Req, rest: String) -> String:
  match q:
    case FAc.QHost{h, al}:
      Wr.put_nat(0n, Wr.put_str(h, Wr.put_list(~String, ~Wr.put_str, al, rest)))
    case FAc.QOrigin{o, h}:
      Wr.put_nat(1n, Wr.put_str(o, Wr.put_str(h, rest)))

# the reply Rust reads: the model's verdict (pinned by the laws above it)
def sp_w_reply(q: FAc.Req) -> String:
  match q:
    case FAc.QHost{h, al}:
      Wr.put_bool(Ac.host_allowed(h, al), "")
    case FAc.QOrigin{o, h}:
      Wr.put_bool(Ac.same_origin(o, h), "")

# every length of xs fits the wire
def sp_fit_strs(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(LawsBase.wire_fits(String.length(x)), sp_fit_strs(t))

# every number and length of the request fits the wire
def sp_fit_req(q: FAc.Req) -> Bool:
  match q:
    case FAc.QHost{h, +al}:
      Bool.and(LawsBase.wire_fits(String.length(h)), Bool.and(LawsBase.wire_fits(List.length(&2, String, al)), sp_fit_strs(al)))
    case FAc.QOrigin{o, h}:
      Bool.and(LawsBase.wire_fits(String.length(o)), LawsBase.wire_fits(String.length(h)))

# R1: a decimal digit, and one that may lead a number past 65535
type PortDigit is Data:
  P0{}
  P1{}
  P2{}
  P3{}
  P4{}
  P5{}
  P6{}
  P7{}
  P8{}
  P9{}

type PortLead is Data:
  L1{}
  L2{}
  L3{}
  L4{}
  L5{}
  L6{}
  L7{}
  L8{}
  L9{}

def sp_digit(d: PortDigit) -> Char:
  match d:
    case P0{}:
      '0'
    case P1{}:
      '1'
    case P2{}:
      '2'
    case P3{}:
      '3'
    case P4{}:
      '4'
    case P5{}:
      '5'
    case P6{}:
      '6'
    case P7{}:
      '7'
    case P8{}:
      '8'
    case P9{}:
      '9'

def sp_lead(d: PortLead) -> Char:
  match d:
    case L1{}:
      '1'
    case L2{}:
      '2'
    case L3{}:
      '3'
    case L4{}:
      '4'
    case L5{}:
      '5'
    case L6{}:
      '6'
    case L7{}:
      '7'
    case L8{}:
      '8'
    case L9{}:
      '9'

# the digits ds as text
def sp_digits(ds: List<&2, PortDigit>) -> String:
  match ds:
    case Nil{}:
      SNil{}
    case d <> t:
      SCon{sp_digit(d), sp_digits(t)}

# Laws: the verdicts
# ------------------

# LAW dash_access_host_spelled (R1, R2): every well-formed authority (R1:
# a host that is not bracketed, or an IPv6 literal, then an optional
# ':' and a port of one or more digits worth at most 65535, leading zeros
# and a '+' allowed; no '@', '/', '?', '#' or space) is allowed exactly
# when its host is, but for ASCII case, a loopback name or an allowed
# host, whatever its port
# EXCLUDES: an allowed host refused (with a port, a '+', leading zeros, in
#   capitals, bracketed), a foreign name allowed (DNS rebinding), a prefix
#   or case-sensitive name test, a port taken for part of the host
law dash_access_host_spelled:
  for +a: SpAuth
  for +al: List<&2, String>
  for ok: {sp_well(a) == True{} : Bool}
  {Ac.host_allowed(sp_spell(a), al) == sp_named(sp_name(a), al) : Bool}

# LAW dash_access_host_only_spelled (R1, R2): every `Host` that is allowed
# is the writing of a well-formed authority (so dash_access_host_spelled
# gives its verdict); any other text is refused
# EXCLUDES: a userinfo, path, query or fragment read as part of a host; the
#   first ':' taken for the last; an IPv6 literal cut at a later ']' or
#   followed by junk; an empty host; a ':' in a host that is not
#   bracketed; a bad, signed-negative, empty or too large port accepted
law dash_access_host_only_spelled:
  for +h: String
  for +al: List<&2, String>
  for yes: {Ac.host_allowed(h, al) == True{} : Bool}
  exs a: SpAuth
  {h == sp_spell(a) : String} & {sp_well(a) == True{} : Bool}

# LAW dash_access_origin_spelled (R1, R3): an `Origin` written as a scheme
# that is http or https (any ASCII case), "://" and a well-formed
# authority matches a well-formed `Host` exactly when both hosts are the
# same but for ASCII case and both ports are the same once the scheme's
# default port fills a missing one
# EXCLUDES: another site's origin matched (cross-site WebSocket
#   hijacking), another port matched, a default port swapped or missing,
#   the page's own origin refused
law dash_access_origin_spelled:
  for +sc: String
  for +d: Nat
  for +a: SpAuth
  for +b: SpAuth
  for scheme: {sp_scheme(sc) == Some{d} : Maybe<&2, Nat>}
  for wa: {sp_well(a) == True{} : Bool}
  for wb: {sp_well(b) == True{} : Bool}
  {Ac.same_origin(sp_origin_text(sc, a), sp_spell(b)) == sp_same_site(d, a, b) : Bool}

# LAW dash_access_origin_only_spelled (R1, R3): every `Origin` that
# matches a `Host` is written as an http or https scheme, "://" and a
# well-formed authority, and the `Host` is a well-formed authority (so
# dash_access_origin_spelled gives the verdict); any other pair is refused
# EXCLUDES: a scheme other than http/https (`file://`, `null`, an empty
#   one), a page path or query accepted, a malformed `Host` matched
law dash_access_origin_only_spelled:
  for +o: String
  for +h: String
  for yes: {Ac.same_origin(o, h) == True{} : Bool}
  exs w: SpOrigin
  {o == sp_o_origin(w) : String} & {h == sp_o_host(w) : String} & {sp_o_ok(w) == True{} : Bool}

# LAW dash_access_host_long_port (R1, R2): every `Host` whose port is more
# than 5 decimal digits, the first not 0 (so worth more than 65535), is
# refused, whatever comes before its last ':' and whatever hosts are
# allowed (proven by induction over the digit run, for every length)
# EXCLUDES: a port read modulo 65536 or capped and kept, a long port
#   accepted because its value ran past the runtime's numbers, a long port
#   accepted after a bracketed or allowed host
law dash_access_host_long_port:
  for +n: String
  for +a: PortLead
  for +d1: PortDigit
  for +d2: PortDigit
  for +d3: PortDigit
  for +d4: PortDigit
  for +d5: PortDigit
  for +ds: List<&2, PortDigit>
  for +al: List<&2, String>
  {Ac.host_allowed(String.append(n, SCon{':', SCon{sp_lead(a), sp_digits(d1 <> d2 <> d3 <> d4 <> d5 <> ds)}}), al) == False{} : Bool}

# LAW dash_access_host_01_example (R1, R2): anchor: Rust's vector: the Host "127.0.0.1:8377" is allowed
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_01_example:
  {Ac.host_allowed("127.0.0.1:8377", ["box.tail1234.ts.net"]) == True{} : Bool}

# LAW dash_access_host_02_example (R1, R2): anchor: Rust's vector: the Host "127.0.0.1" is allowed
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_02_example:
  {Ac.host_allowed("127.0.0.1", []) == True{} : Bool}

# LAW dash_access_host_03_example (R1, R2): anchor: Rust's vector: the Host "LOCALHOST:1" is allowed
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_03_example:
  {Ac.host_allowed("LOCALHOST:1", []) == True{} : Bool}

# LAW dash_access_host_04_example (R1, R2): anchor: Rust's vector: the Host "[::1]:8377" is allowed
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_04_example:
  {Ac.host_allowed("[::1]:8377", []) == True{} : Bool}

# LAW dash_access_host_05_example (R1, R2): anchor: Rust's vector: the Host "[::1]" is allowed
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_05_example:
  {Ac.host_allowed("[::1]", []) == True{} : Bool}

# LAW dash_access_host_06_example (R1, R2): anchor: Rust's vector: the Host "box.tail1234.ts.net" is allowed
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_06_example:
  {Ac.host_allowed("box.tail1234.ts.net", ["box.tail1234.ts.net"]) == True{} : Bool}

# LAW dash_access_host_07_example (R1, R2): anchor: Rust's vector: the Host "Box.Tail1234.ts.net:443" is allowed
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_07_example:
  {Ac.host_allowed("Box.Tail1234.ts.net:443", ["box.tail1234.ts.net"]) == True{} : Bool}

# LAW dash_access_host_08_example (R1, R2): anchor: Rust's vector: the Host "evil.example:8377" is refused
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_08_example:
  {Ac.host_allowed("evil.example:8377", ["box.tail1234.ts.net"]) == False{} : Bool}

# LAW dash_access_host_09_example (R1, R2): anchor: Rust's vector: the Host "127.0.0.1.evil.example" is refused
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_09_example:
  {Ac.host_allowed("127.0.0.1.evil.example", []) == False{} : Bool}

# LAW dash_access_host_10_example (R1, R2): anchor: Rust's vector: the Host "localhost." is refused
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_10_example:
  {Ac.host_allowed("localhost.", []) == False{} : Bool}

# LAW dash_access_host_11_example (R1, R2): anchor: Rust's vector: the Host "" is refused
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_11_example:
  {Ac.host_allowed("", []) == False{} : Bool}

# LAW dash_access_host_12_example (R1, R2): anchor: Rust's vector: the Host "127.0.0.1:http" is refused
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_12_example:
  {Ac.host_allowed("127.0.0.1:http", []) == False{} : Bool}

# LAW dash_access_host_13_example (R1, R2): anchor: Rust's vector: the Host "user@127.0.0.1" is refused
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_13_example:
  {Ac.host_allowed("user@127.0.0.1", []) == False{} : Bool}

# LAW dash_access_host_14_example (R1, R2): anchor: Rust's vector: the Host "::1" is refused
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_14_example:
  {Ac.host_allowed("::1", []) == False{} : Bool}

# LAW dash_access_host_15_example (R1, R2): anchor: a port or bracket edge case per R1 (Rust `split_authority`, `u16::from_str`): the Host "localhost:65535" is allowed
# EXCLUDES: a reading of this host other than Rust `split_authority` and
#   `u16::from_str` give
law dash_access_host_15_example:
  {Ac.host_allowed("localhost:65535", []) == True{} : Bool}

# LAW dash_access_host_16_example (R1, R2): anchor: a port or bracket edge case per R1 (Rust `split_authority`, `u16::from_str`): the Host "localhost:65536" is refused
# EXCLUDES: a reading of this host other than Rust `split_authority` and
#   `u16::from_str` give
law dash_access_host_16_example:
  {Ac.host_allowed("localhost:65536", []) == False{} : Bool}

# LAW dash_access_host_17_example (R1, R2): anchor: a port or bracket edge case per R1 (Rust `split_authority`, `u16::from_str`): the Host "localhost:000080" is allowed
# EXCLUDES: a reading of this host other than Rust `split_authority` and
#   `u16::from_str` give
law dash_access_host_17_example:
  {Ac.host_allowed("localhost:000080", []) == True{} : Bool}

# LAW dash_access_host_18_example (R1, R2): anchor: a port or bracket edge case per R1 (Rust `split_authority`, `u16::from_str`): the Host "localhost:+80" is allowed
# EXCLUDES: a reading of this host other than Rust `split_authority` and
#   `u16::from_str` give
law dash_access_host_18_example:
  {Ac.host_allowed("localhost:+80", []) == True{} : Bool}

# LAW dash_access_host_19_example (R1, R2): anchor: a port or bracket edge case per R1 (Rust `split_authority`, `u16::from_str`): the Host "localhost:+" is refused
# EXCLUDES: a reading of this host other than Rust `split_authority` and
#   `u16::from_str` give
law dash_access_host_19_example:
  {Ac.host_allowed("localhost:+", []) == False{} : Bool}

# LAW dash_access_host_20_example (R1, R2): anchor: a port or bracket edge case per R1 (Rust `split_authority`, `u16::from_str`): the Host "localhost:" is refused
# EXCLUDES: a reading of this host other than Rust `split_authority` and
#   `u16::from_str` give
law dash_access_host_20_example:
  {Ac.host_allowed("localhost:", []) == False{} : Bool}

# LAW dash_access_host_21_example (R1, R2): anchor: a port or bracket edge case per R1 (Rust `split_authority`, `u16::from_str`): the Host "localhost:-1" is refused
# EXCLUDES: a reading of this host other than Rust `split_authority` and
#   `u16::from_str` give
law dash_access_host_21_example:
  {Ac.host_allowed("localhost:-1", []) == False{} : Bool}

# LAW dash_access_host_22_example (R1, R2): anchor: a port or bracket edge case per R1 (Rust `split_authority`, `u16::from_str`): the Host "localhost:100000" (a port of six digits) is refused; longer ports: dash_access_host_long_port
# EXCLUDES: a reading of this host other than Rust `split_authority` and
#   `u16::from_str` give
law dash_access_host_22_example:
  {Ac.host_allowed("localhost:100000", []) == False{} : Bool}

# LAW dash_access_host_23_example (R1, R2): anchor: a port or bracket edge case per R1 (Rust `split_authority`, `u16::from_str`): the Host "[::1]]:80" is refused
# EXCLUDES: a reading of this host other than Rust `split_authority` and
#   `u16::from_str` give
law dash_access_host_23_example:
  {Ac.host_allowed("[::1]]:80", []) == False{} : Bool}

# LAW dash_access_host_24_example (R1, R2): anchor: a port or bracket edge case per R1 (Rust `split_authority`, `u16::from_str`): the Host "[::1]x" is refused
# EXCLUDES: a reading of this host other than Rust `split_authority` and
#   `u16::from_str` give
law dash_access_host_24_example:
  {Ac.host_allowed("[::1]x", []) == False{} : Bool}

# LAW dash_access_host_25_example (R1, R2): anchor: a port or bracket edge case per R1 (Rust `split_authority`, `u16::from_str`): the Host "a:b:80" is refused
# EXCLUDES: a reading of this host other than Rust `split_authority` and
#   `u16::from_str` give
law dash_access_host_25_example:
  {Ac.host_allowed("a:b:80", ["a:b"]) == False{} : Bool}

# LAW dash_access_origin_example (R1, R3): anchor: Rust's vectors: an
# origin of its own host with and without default ports, another host,
# another port, another site, http against port 443, `null`, `file://`, a
# path; a scheme in capitals
# EXCLUDES: a spec that drifts from the Rust it replaced
law dash_access_origin_example:
  {[Ac.same_origin("http://127.0.0.1:8377", "127.0.0.1:8377"), Ac.same_origin("https://box.ts.net", "box.ts.net"), Ac.same_origin("https://box.ts.net", "box.ts.net:443"), Ac.same_origin("http://localhost", "localhost:80"), Ac.same_origin("http://[::1]:9", "[::1]:9"), Ac.same_origin("http://127.0.0.1:8377", "localhost:8377"), Ac.same_origin("http://127.0.0.1:9999", "127.0.0.1:8377"), Ac.same_origin("https://evil.example", "127.0.0.1:8377"), Ac.same_origin("http://box.ts.net", "box.ts.net:443"), Ac.same_origin("null", "127.0.0.1:8377"), Ac.same_origin("file://", "127.0.0.1:8377"), Ac.same_origin("http://127.0.0.1:8377/path", "127.0.0.1:8377"), Ac.same_origin("HTTP://Box.ts.net", "box.TS.net:80")] == [True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}] : List<&2, Bool>}

# Laws: the entry (R4)
# --------------------

# LAW dash_access_entry_answers (R4): the entry answers every request Rust
# spells, every length within the wire, with the model's verdict
# (Ac.host_allowed, Ac.same_origin: pinned by the laws above), spelled
# EXCLUDES: a field misread, swapped or dropped; one check answered for
#   the other; a default
law dash_access_entry_answers:
  for +q: FAc.Req
  for h: {sp_fit_req(q) == True{} : Bool}
  {FAc.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW dash_access_entry_reads (R4): the entry's decoder reads a spelled
# request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law dash_access_entry_reads:
  for +q: FAc.Req
  for +rest: String
  for h: {sp_fit_req(q) == True{} : Bool}
  {FAc.get_req(sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FAc.Req>}

# LAW dash_access_entry_exact (R4): every input the entry does not answer
# with the error form is a spelled request that fits the wire
# EXCLUDES: a verdict made on input that is no request (an unknown tag, a
#   malformed field, input left over)
law dash_access_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FAc.ffi(s)) == False{} : Bool}
  exs r: FAc.Req
  {s == sp_w_req(r, "") : String} & {sp_fit_req(r) == True{} : Bool}

# LAW dash_access_entry_refuses (R4): every error the entry answers is
# exactly `E dash_access: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law dash_access_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FAc.ffi(s)) == True{} : Bool}
  {FAc.ffi(s) == Wr.err("dash_access: malformed request") : String}

# LAW dash_access_entry_example (R4): anchor: the wire strings Rust sends
# and the replies it reads; an unknown tag and input left over
# EXCLUDES: tags in another order, a field order other than Rust's
law dash_access_entry_example:
  {[FAc.ffi("0,14,localhost:83770,"), FAc.ffi("0,6,box:801,3,box"), FAc.ffi("0,6,evil:10,"), FAc.ffi("1,16,http://localhost9,localhost"), FAc.ffi("1,4,null9,localhost"), FAc.ffi("2,"), FAc.ffi("0,6,evil:10,x")] == ["T", "T", "F", "T", "F", Wr.err("dash_access: malformed request"), Wr.err("dash_access: malformed request")] : List<&2, String>}
