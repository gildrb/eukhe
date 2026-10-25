# eukhe: lemmas shared by the proofs of area dash_access: each helper of
# bend/dash_access.bend answers what its spec helper of
# laws/dash_access.bend answers, on every input (by induction on the
# text for the scans, case by case for the choices)

import Base
import ../../bend/dash_access.bend as Ac
import ../../laws/dash_access.bend as DashAccess
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit

# Scans
# -----

def dab.stops(s: String) -> {Ac.stops(s) == DashAccess.sp_holds(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %dab.stops(t) : {Bool.or(Ac.stop(c), Ac.stops(t)) == Bool.or(DashAccess.sp_forbidden(c), _) : Bool}
      {==}

def dab.colons(s: String) -> {Ac.colons(s) == DashAccess.sp_has_colon(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %dab.colons(t) : {Bool.or(Char.is_eq(c, ':'), Ac.colons(t)) == Bool.or(Char.is_eq(c, ':'), _) : Bool}
      {==}

def dab.same(a: String, b: String) -> {Ac.same(a, b) == DashAccess.sp_ci(a, b) : Bool}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, v}:
      {==}
    case SCon{x, u} SNil{}:
      {==}
    case SCon{x, u} SCon{y, v}:
      %dab.same(u, v) : {Bool.and(Char.is_eq(Char.to_lower(x), Char.to_lower(y)), Ac.same(u, v)) == Bool.and(Char.is_eq(Char.to_lower(x), Char.to_lower(y)), _) : Bool}
      {==}

def dab.among(+n: String, xs: List<&2, String>) -> {Ac.among(n, xs) == DashAccess.sp_any_ci(n, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      %dab.same(x, n) : {Bool.or(Ac.same(x, n), Ac.among(n, t)) == Bool.or(_, DashAccess.sp_any_ci(n, t)) : Bool}
      %dab.among(n, t) : {Bool.or(Ac.same(x, n), Ac.among(n, t)) == Bool.or(Ac.same(x, n), _) : Bool}
      {==}

# every length fits, as the doc_commit spec says it (its list lemmas are
# reused)
def dab.fits(xs: List<&2, String>) -> {DashAccess.sp_fit_strs(xs) == DocCommit.sp_fit_strs(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %dab.fits(t) : {Bool.and(LawsBase.wire_fits(String.length(x)), DashAccess.sp_fit_strs(t)) == Bool.and(LawsBase.wire_fits(String.length(x)), _) : Bool}
      {==}

# Cuts
# ----

def dab.cons(c: Char, m: Maybe<&2, Ac.Cut>) -> {Ac.cons(c, m) == DashAccess.sp_front(c, m) : Maybe<&2, Ac.Cut>}:
  match m:
    case None{}:
      {==}
    case Some{p}:
      match p:
        case Ac.Cut{a, b}:
          {==}

def dab.close_at(b: Bool, c: Char, t: String, r: Maybe<&2, Ac.Cut>) -> {Ac.close.at(b, c, t, r) == DashAccess.sp_closing.at(b, c, t, r) : Maybe<&2, Ac.Cut>}:
  match b:
    case True{}:
      {==}
    case False{}:
      dab.cons(c, r)

def dab.close(s: String) -> {Ac.close(s) == DashAccess.sp_closing(s) : Maybe<&2, Ac.Cut>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %dab.close(t) : {Ac.close.at(Char.is_eq(c, ']'), c, t, Ac.close(t)) == DashAccess.sp_closing.at(Char.is_eq(c, ']'), c, t, _) : Maybe<&2, Ac.Cut>}
      dab.close_at(Char.is_eq(c, ']'), c, t, Ac.close(t))

def dab.last_here(b: Bool, t: String) -> {Ac.last.here(b, t) == DashAccess.sp_rsplit.here(b, t) : Maybe<&2, Ac.Cut>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def dab.last_at(r: Maybe<&2, Ac.Cut>, c: Char, t: String) -> {Ac.last.at(c, t, r) == DashAccess.sp_rsplit.at(c, t, r) : Maybe<&2, Ac.Cut>}:
  match r:
    case Some{p}:
      dab.cons(c, Some{p})
    case None{}:
      dab.last_here(Char.is_eq(c, ':'), t)

def dab.last(s: String) -> {Ac.last(s) == DashAccess.sp_rsplit(s) : Maybe<&2, Ac.Cut>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %dab.last(t) : {Ac.last.at(c, t, Ac.last(t)) == DashAccess.sp_rsplit.at(c, t, _) : Maybe<&2, Ac.Cut>}
      dab.last_at(Ac.last(t), c, t)

# Ports
# -----

def dab.cap_at(b: Bool, x: Nat) -> {Ac.cap.at(b, x) == DashAccess.sp_clamp.at(b, x) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def dab.cap(+x: Nat) -> {Ac.cap(x) == DashAccess.sp_clamp(x) : Nat}:
  dab.cap_at(Nat.is_le(x, 65535n), x)

def dab.keep(b: Bool, r: Maybe<&2, Nat>) -> {Ac.digits.keep(b, r) == DashAccess.sp_dec.if(b, r) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def dab.digits(s: String, +v: Nat) -> {Ac.digits(s, v) == DashAccess.sp_dec(s, v) : Maybe<&2, Nat>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +x = Nat.add(Nat.mul(10n, v), Ac.digit(c))
      %dab.cap(x) : {Ac.digits.keep(Char.is_digit(c), Ac.digits(t, Ac.cap(x))) == DashAccess.sp_dec.if(Char.is_digit(c), DashAccess.sp_dec(t, _)) : Maybe<&2, Nat>}
      %dab.digits(t, Ac.cap(x)) : {Ac.digits.keep(Char.is_digit(c), Ac.digits(t, Ac.cap(x))) == DashAccess.sp_dec.if(Char.is_digit(c), _) : Maybe<&2, Nat>}
      dab.keep(Char.is_digit(c), Ac.digits(t, Ac.cap(x)))

def dab.fit_at(b: Bool, v: Nat) -> {Ac.num.fit.at(b, v) == DashAccess.sp_u16.fit(b, v) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def dab.fit(m: Maybe<&2, Nat>) -> {Ac.num.fit(m) == DashAccess.sp_u16.val(m) : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{+v}:
      dab.fit_at(Nat.is_le(v, 65535n), v)

def dab.num(s: String) -> {Ac.num(s) == DashAccess.sp_u16.digits(s) : Maybe<&2, Nat>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %dab.digits(SCon{c, t}, 0n) : {Ac.num.fit(Ac.digits(SCon{c, t}, 0n)) == DashAccess.sp_u16.val(_) : Maybe<&2, Nat>}
      dab.fit(Ac.digits(SCon{c, t}, 0n))

def dab.sign(b: Bool, +c: Char, +t: String) -> {Ac.port.sign(b, c, t) == DashAccess.sp_u16.plus(b, c, t) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      dab.num(t)
    case False{}:
      dab.num(SCon{c, t})

def dab.port(s: String) -> {Ac.port(s) == DashAccess.sp_u16(s) : Maybe<&2, Nat>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      dab.sign(Char.is_eq(c, '+'), c, t)

def dab.with_port(h: String, m: Maybe<&2, Nat>) -> {Ac.with_port(h, m) == DashAccess.sp_ported(h, m) : Ac.Authority}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      {==}

def dab.ported(+h: String, +p: String) -> {Ac.with_port(h, Ac.port(p)) == DashAccess.sp_ported(h, DashAccess.sp_u16(p)) : Ac.Authority}:
  %dab.port(p) : {Ac.with_port(h, Ac.port(p)) == DashAccess.sp_ported(h, _) : Ac.Authority}
  dab.with_port(h, Ac.port(p))

# Authorities
# -----------

def dab.after_colon(b: Bool, +h: String, +p: String) -> {Ac.after.colon(b, h, p) == DashAccess.sp_cut(DashAccess.sp_ported(h, DashAccess.sp_u16(p)), Ac.NoAuthority{}, b) : Ac.Authority}:
  match b:
    case True{}:
      dab.ported(h, p)
    case False{}:
      {==}

def dab.after(+h: String, r: String) -> {Ac.after(h, r) == DashAccess.sp_bracketed.rest(h, r) : Ac.Authority}:
  match r:
    case SNil{}:
      {==}
    case SCon{+d, +p}:
      dab.after_colon(Char.is_eq(d, ':'), h, p)

def dab.bracket(m: Maybe<&2, Ac.Cut>) -> {Ac.bracket(m) == DashAccess.sp_bracketed(m) : Ac.Authority}:
  match m:
    case None{}:
      {==}
    case Some{p}:
      match p:
        case Ac.Cut{+h, r}:
          dab.after(h, r)

def dab.plain_host(b: Bool, +h: String, p: Maybe<&2, String>) -> {Ac.plain.host(b, h, p) == DashAccess.sp_cut(Ac.NoAuthority{}, DashAccess.sp_unbracketed.port(h, p), b) : Ac.Authority}:
  match b:
    case True{}:
      {==}
    case False{}:
      match p:
        case None{}:
          {==}
        case Some{+t}:
          dab.ported(h, t)

def dab.plain_check(+h: String, p: Maybe<&2, String>) -> {Ac.plain.check(h, p) == DashAccess.sp_unbracketed.host(h, p) : Ac.Authority}:
  %dab.colons(h) : {Ac.plain.host(Bool.or(String.is_empty(h), Ac.colons(h)), h, p) == DashAccess.sp_cut(Ac.NoAuthority{}, DashAccess.sp_unbracketed.port(h, p), Bool.or(String.is_empty(h), _)) : Ac.Authority}
  dab.plain_host(Bool.or(String.is_empty(h), Ac.colons(h)), h, p)

def dab.plain(+s: String, m: Maybe<&2, Ac.Cut>) -> {Ac.plain(s, m) == DashAccess.sp_unbracketed(s, m) : Ac.Authority}:
  match m:
    case None{}:
      dab.plain_check(s, None{})
    case Some{p}:
      match p:
        case Ac.Cut{+h, +t}:
          dab.plain_check(h, Some{t})

def dab.form(b: Bool, +s: String) -> {Ac.split.form(b, s) == DashAccess.sp_authority.form(b, s) : Ac.Authority}:
  match b:
    case True{}:
      %dab.close(s) : {Ac.bracket(Ac.close(s)) == DashAccess.sp_bracketed(_) : Ac.Authority}
      dab.bracket(Ac.close(s))
    case False{}:
      %dab.last(s) : {Ac.plain(s, Ac.last(s)) == DashAccess.sp_unbracketed(s, _) : Ac.Authority}
      dab.plain(s, Ac.last(s))

def dab.ok(b: Bool, +c: Char, +t: String) -> {Ac.split.ok(b, c, t) == DashAccess.sp_cut(Ac.NoAuthority{}, DashAccess.sp_authority.form(Char.is_eq(c, '['), SCon{c, t}), b) : Ac.Authority}:
  match b:
    case True{}:
      {==}
    case False{}:
      dab.form(Char.is_eq(c, '['), SCon{c, t})

# the authority a text is: the code's is the spec's
def dab.split(s: String) -> {Ac.split(s) == DashAccess.sp_authority(s) : Ac.Authority}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %dab.stops(SCon{c, t}) : {Ac.split.ok(Ac.stops(SCon{c, t}), c, t) == DashAccess.sp_cut(Ac.NoAuthority{}, DashAccess.sp_authority.form(Char.is_eq(c, '['), SCon{c, t}), _) : Ac.Authority}
      dab.ok(Ac.stops(SCon{c, t}), c, t)

# Origins
# -------

def dab.slashes_if(b: Bool, r: String) -> {Ac.sep.slashes(b, r) == DashAccess.sp_slashes.if(b, r) : Maybe<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def dab.rest(t: String) -> {Ac.sep.rest(t) == DashAccess.sp_slashes(t) : Maybe<&2, String>}:
  match t:
    case SNil{}:
      {==}
    case SCon{a, u}:
      match u:
        case SNil{}:
          {==}
        case SCon{b, r}:
          dab.slashes_if(Bool.and(Char.is_eq(a, '/'), Char.is_eq(b, '/')), r)

def dab.found(m: Maybe<&2, String>, c: Char, r: Maybe<&2, Ac.Cut>) -> {Ac.sep.found(m, c, r) == DashAccess.sp_split3.found(m, c, r) : Maybe<&2, Ac.Cut>}:
  match m:
    case Some{x}:
      {==}
    case None{}:
      dab.cons(c, r)

def dab.sep_at(b: Bool, c: Char, +t: String, r: Maybe<&2, Ac.Cut>) -> {Ac.sep.at(b, c, t, r) == DashAccess.sp_split3.at(b, c, t, r) : Maybe<&2, Ac.Cut>}:
  match b:
    case True{}:
      %dab.rest(t) : {Ac.sep.found(Ac.sep.rest(t), c, r) == DashAccess.sp_split3.found(_, c, r) : Maybe<&2, Ac.Cut>}
      dab.found(Ac.sep.rest(t), c, r)
    case False{}:
      dab.cons(c, r)

def dab.sep(s: String) -> {Ac.sep(s) == DashAccess.sp_split3(s) : Maybe<&2, Ac.Cut>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %dab.sep(t) : {Ac.sep.at(Char.is_eq(c, ':'), c, t, Ac.sep(t)) == DashAccess.sp_split3.at(Char.is_eq(c, ':'), c, t, _) : Maybe<&2, Ac.Cut>}
      dab.sep_at(Char.is_eq(c, ':'), c, t, Ac.sep(t))

def dab.scheme_of(a: Bool, b: Bool) -> {Ac.scheme.of(a, b) == DashAccess.sp_default.of(a, b) : Maybe<&2, Nat>}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def dab.scheme(+s: String) -> {Ac.scheme(s) == DashAccess.sp_default(s) : Maybe<&2, Nat>}:
  %dab.same(s, "http") : {Ac.scheme.of(Ac.same(s, "http"), Ac.same(s, "https")) == DashAccess.sp_default.of(_, DashAccess.sp_ci(s, "https")) : Maybe<&2, Nat>}
  %dab.same(s, "https") : {Ac.scheme.of(Ac.same(s, "http"), Ac.same(s, "https")) == DashAccess.sp_default.of(Ac.same(s, "http"), _) : Maybe<&2, Nat>}
  dab.scheme_of(Ac.same(s, "http"), Ac.same(s, "https"))

def dab.or(m: Maybe<&2, Nat>, d: Nat) -> {Ac.port_or(m, d) == DashAccess.sp_or(m, d) : Nat}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      {==}

def dab.pair(+d: Nat, a: Ac.Authority, b: Ac.Authority) -> {Ac.origin.pair(d, a, b) == DashAccess.sp_match(d, a, b) : Bool}:
  match a b:
    case Ac.HostPort{+n, +p} Ac.HostPort{+m, +q}:
      %dab.same(n, m) : {Bool.and(Ac.same(n, m), Nat.is_eq(Ac.port_or(p, d), Ac.port_or(q, d))) == Bool.and(_, Nat.is_eq(DashAccess.sp_or(p, d), DashAccess.sp_or(q, d))) : Bool}
      %dab.or(p, d) : {Bool.and(Ac.same(n, m), Nat.is_eq(Ac.port_or(p, d), Ac.port_or(q, d))) == Bool.and(Ac.same(n, m), Nat.is_eq(_, DashAccess.sp_or(q, d))) : Bool}
      %dab.or(q, d) : {Bool.and(Ac.same(n, m), Nat.is_eq(Ac.port_or(p, d), Ac.port_or(q, d))) == Bool.and(Ac.same(n, m), Nat.is_eq(Ac.port_or(p, d), _)) : Bool}
      {==}
    case Ac.HostPort{n, p} Ac.NoAuthority{}:
      {==}
    case Ac.NoAuthority{} Ac.HostPort{m, q}:
      {==}
    case Ac.NoAuthority{} Ac.NoAuthority{}:
      {==}

def dab.oport(dm: Maybe<&2, Nat>, +au: String, +h: String) -> {Ac.origin.port(dm, au, h) == DashAccess.sp_origin.port(dm, au, h) : Bool}:
  match dm:
    case None{}:
      {==}
    case Some{+n}:
      %dab.split(au) : {Ac.origin.pair(n, Ac.split(au), Ac.split(h)) == DashAccess.sp_match(n, _, DashAccess.sp_authority(h)) : Bool}
      %dab.split(h) : {Ac.origin.pair(n, Ac.split(au), Ac.split(h)) == DashAccess.sp_match(n, Ac.split(au), _) : Bool}
      dab.pair(n, Ac.split(au), Ac.split(h))

def dab.ocut(m: Maybe<&2, Ac.Cut>, +h: String) -> {Ac.origin.sep(m, h) == DashAccess.sp_origin.cut(m, h) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{p}:
      match p:
        case Ac.Cut{+sc, +au}:
          %dab.scheme(sc) : {Ac.origin.port(Ac.scheme(sc), au, h) == DashAccess.sp_origin.port(_, au, h) : Bool}
          dab.oport(Ac.scheme(sc), au, h)

# Hosts
# -----

def dab.host_of(a: Ac.Authority, +al: List<&2, String>) -> {Ac.host_allowed.of(a, al) == DashAccess.sp_host.of(a, al) : Bool}:
  match a:
    case Ac.HostPort{+n, p}:
      %dab.among(n, Ac.loopback()) : {Bool.or(Ac.among(n, Ac.loopback()), Ac.among(n, al)) == Bool.or(_, DashAccess.sp_any_ci(n, al)) : Bool}
      %dab.among(n, al) : {Bool.or(Ac.among(n, Ac.loopback()), Ac.among(n, al)) == Bool.or(Ac.among(n, Ac.loopback()), _) : Bool}
      {==}
    case Ac.NoAuthority{}:
      {==}
