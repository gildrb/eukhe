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

def sp_cut(x: Ac.Authority, y: Ac.Authority, b: Bool) -> Ac.Authority:
  match b:
    case True{}:
      x
    case False{}:
      y

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

def sp_has_colon(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.or(Char.is_eq(c, ':'), sp_has_colon(t))

# R2: a and b are equal but for ASCII case (Rust `eq_ignore_ascii_case`)
def sp_ci(a: String, b: String) -> Bool:
  match a b:
    case SNil{} SNil{}:
      True{}
    case SNil{} SCon{y, v}:
      False{}
    case SCon{x, u} SNil{}:
      False{}
    case SCon{x, u} SCon{y, v}:
      Bool.and(Char.is_eq(Char.to_lower(x), Char.to_lower(y)), sp_ci(u, v))

def sp_any_ci(+n: String, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(sp_ci(x, n), sp_any_ci(n, t))

def sp_front(c: Char, m: Maybe<&2, Ac.Cut>) -> Maybe<&2, Ac.Cut>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      match p:
        case Ac.Cut{a, b}:
          Some{Ac.Cut{SCon{c, a}, b}}

def sp_closing.at(b: Bool, c: Char, t: String, r: Maybe<&2, Ac.Cut>) -> Maybe<&2, Ac.Cut>:
  match b:
    case True{}:
      Some{Ac.Cut{SCon{c, SNil{}}, t}}
    case False{}:
      sp_front(c, r)

# R1: s through its first ']', and what follows
def sp_closing(s: String) -> Maybe<&2, Ac.Cut>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      sp_closing.at(Char.is_eq(c, ']'), c, t, sp_closing(t))

def sp_rsplit.here(b: Bool, t: String) -> Maybe<&2, Ac.Cut>:
  match b:
    case True{}:
      Some{Ac.Cut{SNil{}, t}}
    case False{}:
      None{}

def sp_rsplit.at(c: Char, t: String, r: Maybe<&2, Ac.Cut>) -> Maybe<&2, Ac.Cut>:
  match r:
    case Some{p}:
      sp_front(c, Some{p})
    case None{}:
      sp_rsplit.here(Char.is_eq(c, ':'), t)

# R1: s before and after its last ':' (Rust `rsplit_once(':')`)
def sp_rsplit(s: String) -> Maybe<&2, Ac.Cut>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      sp_rsplit.at(c, t, sp_rsplit(t))

def sp_clamp.at(b: Bool, x: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      65536n

# R1: a value past 65535 stays past it (65536) while digits follow
def sp_clamp(+x: Nat) -> Nat:
  sp_clamp.at(Nat.is_le(x, 65535n), x)

def sp_dec.if(b: Bool, r: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      r
    case False{}:
      None{}

# R1: the decimal value of the digits s after v, or None
def sp_dec(s: String, +v: Nat) -> Maybe<&2, Nat>:
  match s:
    case SNil{}:
      Some{v}
    case SCon{+c, t}:
      sp_dec.if(Char.is_digit(c), sp_dec(t, sp_clamp(Nat.add(Nat.mul(10n, v), U32.to_nat(U32.sub(Char.to_u32(c), 48))))))

def sp_u16.fit(b: Bool, v: Nat) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{v}
    case False{}:
      None{}

def sp_u16.val(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{+v}:
      sp_u16.fit(Nat.is_le(v, 65535n), v)

# R1: one or more digits worth at most 65535
def sp_u16.digits(s: String) -> Maybe<&2, Nat>:
  match s:
    case SNil{}:
      None{}
    case SCon{c, t}:
      sp_u16.val(sp_dec(SCon{c, t}, 0n))

def sp_u16.plus(b: Bool, c: Char, t: String) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      sp_u16.digits(t)
    case False{}:
      sp_u16.digits(SCon{c, t})

# R1: a port (Rust `u16::from_str`)
def sp_u16(s: String) -> Maybe<&2, Nat>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, t}:
      sp_u16.plus(Char.is_eq(c, '+'), c, t)

def sp_ported(h: String, m: Maybe<&2, Nat>) -> Ac.Authority:
  match m:
    case None{}:
      Ac.NoAuthority{}
    case Some{n}:
      Ac.HostPort{h, Some{n}}

def sp_bracketed.rest(h: String, r: String) -> Ac.Authority:
  match r:
    case SNil{}:
      Ac.HostPort{h, None{}}
    case SCon{+d, p}:
      sp_cut(sp_ported(h, sp_u16(p)), Ac.NoAuthority{}, Char.is_eq(d, ':'))

# R1: an IPv6 literal and what follows it
def sp_bracketed(m: Maybe<&2, Ac.Cut>) -> Ac.Authority:
  match m:
    case None{}:
      Ac.NoAuthority{}
    case Some{p}:
      match p:
        case Ac.Cut{h, r}:
          sp_bracketed.rest(h, r)

def sp_unbracketed.port(h: String, p: Maybe<&2, String>) -> Ac.Authority:
  match p:
    case None{}:
      Ac.HostPort{h, None{}}
    case Some{t}:
      sp_ported(h, sp_u16(t))

# R1: a host that is not bracketed must be neither empty nor hold a ':'
def sp_unbracketed.host(+h: String, p: Maybe<&2, String>) -> Ac.Authority:
  sp_cut(Ac.NoAuthority{}, sp_unbracketed.port(h, p), Bool.or(String.is_empty(h), sp_has_colon(h)))

def sp_unbracketed(+s: String, m: Maybe<&2, Ac.Cut>) -> Ac.Authority:
  match m:
    case None{}:
      sp_unbracketed.host(s, None{})
    case Some{p}:
      match p:
        case Ac.Cut{h, t}:
          sp_unbracketed.host(h, Some{t})

def sp_authority.form(b: Bool, +s: String) -> Ac.Authority:
  match b:
    case True{}:
      sp_bracketed(sp_closing(s))
    case False{}:
      sp_unbracketed(s, sp_rsplit(s))

# R1: the authority s is, if any
def sp_authority(s: String) -> Ac.Authority:
  match s:
    case SNil{}:
      Ac.NoAuthority{}
    case SCon{+c, +t}:
      sp_cut(Ac.NoAuthority{}, sp_authority.form(Char.is_eq(c, '['), SCon{c, t}), sp_holds(SCon{c, t}))

def sp_host.of(a: Ac.Authority, allowed: List<&2, String>) -> Bool:
  match a:
    case Ac.HostPort{+n, p}:
      Bool.or(sp_any_ci(n, ["127.0.0.1", "localhost", "[::1]"]), sp_any_ci(n, allowed))
    case Ac.NoAuthority{}:
      False{}

# R2: the verdict on a `Host`
def sp_host(host: String, allowed: List<&2, String>) -> Bool:
  sp_host.of(sp_authority(host), allowed)

def sp_split3.found(m: Maybe<&2, String>, c: Char, r: Maybe<&2, Ac.Cut>) -> Maybe<&2, Ac.Cut>:
  match m:
    case Some{x}:
      Some{Ac.Cut{SNil{}, x}}
    case None{}:
      sp_front(c, r)

def sp_slashes.if(b: Bool, r: String) -> Maybe<&2, String>:
  match b:
    case True{}:
      Some{r}
    case False{}:
      None{}

# t after its leading "//", if it has one
def sp_slashes(t: String) -> Maybe<&2, String>:
  match t:
    case SNil{}:
      None{}
    case SCon{a, u}:
      match u:
        case SNil{}:
          None{}
        case SCon{b, r}:
          sp_slashes.if(Bool.and(Char.is_eq(a, '/'), Char.is_eq(b, '/')), r)

def sp_split3.at(colon: Bool, c: Char, t: String, r: Maybe<&2, Ac.Cut>) -> Maybe<&2, Ac.Cut>:
  match colon:
    case True{}:
      sp_split3.found(sp_slashes(t), c, r)
    case False{}:
      sp_front(c, r)

# R3: s before and after its first "://" (Rust `split_once("://")`)
def sp_split3(s: String) -> Maybe<&2, Ac.Cut>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      sp_split3.at(Char.is_eq(c, ':'), c, t, sp_split3(t))

def sp_default.of(http: Bool, https: Bool) -> Maybe<&2, Nat>:
  match http https:
    case True{} True{}:
      Some{80n}
    case True{} False{}:
      Some{80n}
    case False{} True{}:
      Some{443n}
    case False{} False{}:
      None{}

# R3: a scheme's default port
def sp_default(+s: String) -> Maybe<&2, Nat>:
  sp_default.of(sp_ci(s, "http"), sp_ci(s, "https"))

def sp_or(m: Maybe<&2, Nat>, d: Nat) -> Nat:
  match m:
    case None{}:
      d
    case Some{n}:
      n

def sp_match(+d: Nat, a: Ac.Authority, b: Ac.Authority) -> Bool:
  match a b:
    case Ac.HostPort{n, p} Ac.HostPort{m, q}:
      Bool.and(sp_ci(n, m), Nat.is_eq(sp_or(p, d), sp_or(q, d)))
    case Ac.HostPort{n, p} Ac.NoAuthority{}:
      False{}
    case Ac.NoAuthority{} Ac.HostPort{m, q}:
      False{}
    case Ac.NoAuthority{} Ac.NoAuthority{}:
      False{}

def sp_origin.port(d: Maybe<&2, Nat>, au: String, host: String) -> Bool:
  match d:
    case None{}:
      False{}
    case Some{n}:
      sp_match(n, sp_authority(au), sp_authority(host))

def sp_origin.cut(m: Maybe<&2, Ac.Cut>, host: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{p}:
      match p:
        case Ac.Cut{sc, au}:
          sp_origin.port(sp_default(sc), au, host)

# R3: the verdict on an `Origin` against a `Host`
def sp_origin(origin: String, host: String) -> Bool:
  sp_origin.cut(sp_split3(origin), host)

# R4: the spelling of a request and of its reply

def sp_w_req(q: FAc.Req, rest: String) -> String:
  match q:
    case FAc.QHost{h, al}:
      Wr.put_nat(0n, Wr.put_str(h, Wr.put_list(~String, ~Wr.put_str, al, rest)))
    case FAc.QOrigin{o, h}:
      Wr.put_nat(1n, Wr.put_str(o, Wr.put_str(h, rest)))

def sp_w_reply(q: FAc.Req) -> String:
  match q:
    case FAc.QHost{h, al}:
      Wr.put_bool(sp_host(h, al), "")
    case FAc.QOrigin{o, h}:
      Wr.put_bool(sp_origin(o, h), "")

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

# LAW dash_access_host_spec (R1, R2): the verdict on every `Host` and every
# list of allowed hosts is the spec's
# EXCLUDES: a foreign name allowed (DNS rebinding), a userinfo or path
#   read as a host, the first ':' taken for the last, an IPv6 literal cut
#   at a later ']', a bad or too large port accepted, a case-sensitive or
#   prefix name test, an allowed host refused
law dash_access_host_spec:
  for +h: String
  for +al: List<&2, String>
  {Ac.host_allowed(h, al) == sp_host(h, al) : Bool}

# LAW dash_access_origin_spec (R1, R3): the verdict on every `Origin`
# against every `Host` is the spec's
# EXCLUDES: another site's origin matched (cross-site WebSocket
#   hijacking), a scheme other than http/https, a default port swapped or
#   missing, another port matched, a page path accepted
law dash_access_origin_spec:
  for +o: String
  for +h: String
  {Ac.same_origin(o, h) == sp_origin(o, h) : Bool}

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

# LAW dash_access_host_15_example (R1, R2): anchor: Rust's vector: the Host "localhost:65535" is allowed
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_15_example:
  {Ac.host_allowed("localhost:65535", []) == True{} : Bool}

# LAW dash_access_host_16_example (R1, R2): anchor: Rust's vector: the Host "localhost:65536" is refused
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_16_example:
  {Ac.host_allowed("localhost:65536", []) == False{} : Bool}

# LAW dash_access_host_17_example (R1, R2): anchor: Rust's vector: the Host "localhost:000080" is allowed
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_17_example:
  {Ac.host_allowed("localhost:000080", []) == True{} : Bool}

# LAW dash_access_host_18_example (R1, R2): anchor: Rust's vector: the Host "localhost:+80" is allowed
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_18_example:
  {Ac.host_allowed("localhost:+80", []) == True{} : Bool}

# LAW dash_access_host_19_example (R1, R2): anchor: Rust's vector: the Host "localhost:+" is refused
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_19_example:
  {Ac.host_allowed("localhost:+", []) == False{} : Bool}

# LAW dash_access_host_20_example (R1, R2): anchor: Rust's vector: the Host "localhost:" is refused
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_20_example:
  {Ac.host_allowed("localhost:", []) == False{} : Bool}

# LAW dash_access_host_21_example (R1, R2): anchor: Rust's vector: the Host "localhost:-1" is refused
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_21_example:
  {Ac.host_allowed("localhost:-1", []) == False{} : Bool}

# LAW dash_access_host_22_example (R1, R2): anchor: Rust's vector, shortened: the Host "localhost:100000" (a port of six digits) is refused; longer ports: dash_access_host_long_port
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_22_example:
  {Ac.host_allowed("localhost:100000", []) == False{} : Bool}

# LAW dash_access_host_23_example (R1, R2): anchor: Rust's vector: the Host "[::1]]:80" is refused
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_23_example:
  {Ac.host_allowed("[::1]]:80", []) == False{} : Bool}

# LAW dash_access_host_24_example (R1, R2): anchor: Rust's vector: the Host "[::1]x" is refused
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
law dash_access_host_24_example:
  {Ac.host_allowed("[::1]x", []) == False{} : Bool}

# LAW dash_access_host_25_example (R1, R2): anchor: Rust's vector: the Host "a:b:80" is refused
# EXCLUDES: a spec that drifts from the Rust it replaced on this host
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
# spells, every length within the wire, with the spelled verdict of the
# spec
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
