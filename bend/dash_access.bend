# dash_access: who may reach the dashboard (Rust: crates/eukhe-dashboard
# access.rs, called by http.rs and bridge.rs for every request).
#
# Every request must name a loopback host (127.0.0.1, localhost, [::1],
# any port) or a host the user allowed (`eukhe dashboard --allow-host`) in
# its `Host`: that defeats DNS rebinding. A WebSocket upgrade must also
# carry the page's own `Origin`: same host, and the same port once the
# scheme's default port (http 80, https 443) fills in a missing one: that
# defeats cross-site WebSocket hijacking. Host names compare without ASCII
# case. Pure: no IO, no @unsafe.

import Base

# A text cut in two: before and after a separator
type Cut is Data:
  Cut{before: String, after: String}

# One `host[:port]` read (Rust `split_authority`)
type Authority is Data:
  # the host (an IPv6 literal keeps its brackets) and the port, if written
  HostPort{name: String, port: Maybe<&2, Nat>}
  # not an authority: empty, userinfo, a path, a bad port, a stray ':'
  NoAuthority{}

# Chars
# -----

# a char no authority holds: '@', '/', '?', '#' or a space
def stop(+c: Char) -> Bool:
  Bool.or(Char.is_eq(c, '@'), Bool.or(Char.is_eq(c, '/'), Bool.or(Char.is_eq(c, '?'), Bool.or(Char.is_eq(c, '#'), Char.is_eq(c, ' ')))))

# s holds a char no authority holds
def stops(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.or(stop(c), stops(t))

# s holds a ':'
def colons(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.or(Char.is_eq(c, ':'), colons(t))

# a and b are the same text but for ASCII case
def same(a: String, b: String) -> Bool:
  match a b:
    case SNil{} SNil{}:
      True{}
    case SNil{} SCon{y, v}:
      False{}
    case SCon{x, u} SNil{}:
      False{}
    case SCon{x, u} SCon{y, v}:
      Bool.and(Char.is_eq(Char.to_lower(x), Char.to_lower(y)), same(u, v))

# n is one of xs but for ASCII case
def among(+n: String, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(same(x, n), among(n, t))

# Splits
# ------

def cons(c: Char, m: Maybe<&2, Cut>) -> Maybe<&2, Cut>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      match p:
        case Cut{a, b}:
          Some{Cut{SCon{c, a}, b}}

def close.at(b: Bool, c: Char, t: String, r: Maybe<&2, Cut>) -> Maybe<&2, Cut>:
  match b:
    case True{}:
      Some{Cut{SCon{c, SNil{}}, t}}
    case False{}:
      cons(c, r)

# s up to and including its first ']', and what follows
def close(s: String) -> Maybe<&2, Cut>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      close.at(Char.is_eq(c, ']'), c, t, close(t))

def last.here(b: Bool, t: String) -> Maybe<&2, Cut>:
  match b:
    case True{}:
      Some{Cut{SNil{}, t}}
    case False{}:
      None{}

def last.at(c: Char, t: String, r: Maybe<&2, Cut>) -> Maybe<&2, Cut>:
  match r:
    case Some{p}:
      cons(c, Some{p})
    case None{}:
      last.here(Char.is_eq(c, ':'), t)

# s before and after its last ':' (Rust `rsplit_once(':')`)
def last(s: String) -> Maybe<&2, Cut>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      last.at(c, t, last(t))

# Ports
# -----

# 65536 for anything larger: the value never grows past the runtime's Nat
def cap.at(b: Bool, x: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      65536n

def cap(+x: Nat) -> Nat:
  cap.at(Nat.is_le(x, 65535n), x)

def digits.keep(d: Bool, r: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match d:
    case True{}:
      r
    case False{}:
      None{}

# the value of a digit (any char: the digit test is separate)
def digit(c: Char) -> Nat:
  U32.to_nat(U32.sub(Char.to_u32(c), 48))

# the value of the decimal digits s after v (capped at 65536), or None
# when s holds another char
def digits(s: String, +v: Nat) -> Maybe<&2, Nat>:
  match s:
    case SNil{}:
      Some{v}
    case SCon{+c, t}:
      digits.keep(Char.is_digit(c), digits(t, cap(Nat.add(Nat.mul(10n, v), digit(c)))))

def num.fit.at(b: Bool, v: Nat) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{v}
    case False{}:
      None{}

def num.fit(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{+v}:
      num.fit.at(Nat.is_le(v, 65535n), v)

# one or more digits worth at most 65535
def num(s: String) -> Maybe<&2, Nat>:
  match s:
    case SNil{}:
      None{}
    case SCon{c, t}:
      num.fit(digits(SCon{c, t}, 0n))

def port.sign(b: Bool, c: Char, t: String) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      num(t)
    case False{}:
      num(SCon{c, t})

# a port's text (Rust `u16::from_str`): an optional '+', then digits
def port(s: String) -> Maybe<&2, Nat>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, t}:
      port.sign(Char.is_eq(c, '+'), c, t)

# Authorities
# -----------

def with_port(h: String, m: Maybe<&2, Nat>) -> Authority:
  match m:
    case None{}:
      NoAuthority{}
    case Some{n}:
      HostPort{h, Some{n}}

def after.colon(b: Bool, h: String, p: String) -> Authority:
  match b:
    case True{}:
      with_port(h, port(p))
    case False{}:
      NoAuthority{}

# a bracketed host h and what follows its ']'
def after(h: String, r: String) -> Authority:
  match r:
    case SNil{}:
      HostPort{h, None{}}
    case SCon{+d, p}:
      after.colon(Char.is_eq(d, ':'), h, p)

def bracket(m: Maybe<&2, Cut>) -> Authority:
  match m:
    case None{}:
      NoAuthority{}
    case Some{p}:
      match p:
        case Cut{h, r}:
          after(h, r)

def plain.host(bad: Bool, h: String, p: Maybe<&2, String>) -> Authority:
  match bad:
    case True{}:
      NoAuthority{}
    case False{}:
      match p:
        case None{}:
          HostPort{h, None{}}
        case Some{t}:
          with_port(h, port(t))

# a host that is not bracketed: not empty, no ':'
def plain.check(+h: String, p: Maybe<&2, String>) -> Authority:
  plain.host(Bool.or(String.is_empty(h), colons(h)), h, p)

def plain(+s: String, m: Maybe<&2, Cut>) -> Authority:
  match m:
    case None{}:
      plain.check(s, None{})
    case Some{p}:
      match p:
        case Cut{h, t}:
          plain.check(h, Some{t})

def split.form(b: Bool, +s: String) -> Authority:
  match b:
    case True{}:
      bracket(close(s))
    case False{}:
      plain(s, last(s))

def split.ok(bad: Bool, +c: Char, t: String) -> Authority:
  match bad:
    case True{}:
      NoAuthority{}
    case False{}:
      split.form(Char.is_eq(c, '['), SCon{c, t})

# the authority s reads as (Rust `split_authority`)
def split(s: String) -> Authority:
  match s:
    case SNil{}:
      NoAuthority{}
    case SCon{+c, +t}:
      split.ok(stops(SCon{c, t}), c, t)

# Hosts
# -----

# the host names always allowed
def loopback() -> List<&2, String>:
  ["127.0.0.1", "localhost", "[::1]"]

def host_allowed.of(a: Authority, allowed: List<&2, String>) -> Bool:
  match a:
    case HostPort{+n, p}:
      Bool.or(among(n, loopback()), among(n, allowed))
    case NoAuthority{}:
      False{}

# whether a request's `Host` names a host the dashboard serves
def host_allowed(host: String, allowed: List<&2, String>) -> Bool:
  host_allowed.of(split(host), allowed)

# Origins
# -------

def sep.slashes(b: Bool, r: String) -> Maybe<&2, String>:
  match b:
    case True{}:
      Some{r}
    case False{}:
      None{}

# t without its leading "//", when it has one
def sep.rest(t: String) -> Maybe<&2, String>:
  match t:
    case SNil{}:
      None{}
    case SCon{a, u}:
      match u:
        case SNil{}:
          None{}
        case SCon{b, r}:
          sep.slashes(Bool.and(Char.is_eq(a, '/'), Char.is_eq(b, '/')), r)

def sep.found(m: Maybe<&2, String>, c: Char, r: Maybe<&2, Cut>) -> Maybe<&2, Cut>:
  match m:
    case Some{x}:
      Some{Cut{SNil{}, x}}
    case None{}:
      cons(c, r)

def sep.at(colon: Bool, c: Char, t: String, r: Maybe<&2, Cut>) -> Maybe<&2, Cut>:
  match colon:
    case True{}:
      sep.found(sep.rest(t), c, r)
    case False{}:
      cons(c, r)

# s before and after its first "://" (Rust `split_once("://")`)
def sep(s: String) -> Maybe<&2, Cut>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      sep.at(Char.is_eq(c, ':'), c, t, sep(t))

def scheme.of(http: Bool, https: Bool) -> Maybe<&2, Nat>:
  match http:
    case True{}:
      Some{80n}
    case False{}:
      match https:
        case True{}:
          Some{443n}
        case False{}:
          None{}

# the default port of a scheme (any ASCII case): http 80, https 443
def scheme(+s: String) -> Maybe<&2, Nat>:
  scheme.of(same(s, "http"), same(s, "https"))

def port_or(m: Maybe<&2, Nat>, d: Nat) -> Nat:
  match m:
    case None{}:
      d
    case Some{n}:
      n

def origin.pair(+d: Nat, a: Authority, b: Authority) -> Bool:
  match a b:
    case HostPort{n, p} HostPort{m, q}:
      Bool.and(same(n, m), Nat.is_eq(port_or(p, d), port_or(q, d)))
    case HostPort{n, p} NoAuthority{}:
      False{}
    case NoAuthority{} HostPort{m, q}:
      False{}
    case NoAuthority{} NoAuthority{}:
      False{}

def origin.port(d: Maybe<&2, Nat>, au: String, host: String) -> Bool:
  match d:
    case None{}:
      False{}
    case Some{n}:
      origin.pair(n, split(au), split(host))

def origin.sep(m: Maybe<&2, Cut>, host: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{p}:
      match p:
        case Cut{sc, au}:
          origin.port(scheme(sc), au, host)

# whether `origin` (the `Origin` header) is the origin of a page served
# under `host` (the request's `Host`)
def same_origin(origin: String, host: String) -> Bool:
  origin.sep(sep(origin), host)
