# eukhe: lemmas the proofs of the auth_read entry share
# A request Rust writes, with any input after it, reads back through the
# entry's decoder (ar.spell_go); the entry answers the verdict the laws
# spell (ar.reply); every input the decoder reads is such a request, read
# stage by stage with the wire's exactness laws (ar.x.*); every error the
# entry answers is its one error form (ar.refuse).

import Base
import ../../bend/auth_flight.bend as F
import ../../bend/ffi_auth_read.bend as FR
import ../../bend/wire.bend as Wr
import ../../laws/auth_read.bend as AuthRead
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire
import ../base/logic/string.bend as LLogicString
import ../base/logic/list.bend as LLogicList
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits

# Logic
# -----

def ar.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

# True is not False
def ar.absurd(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : ar.BD(_, Unit, G)
  Unit{}

# both halves hold
def ar.and(+a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# The verdict
# -----------

def ar.load_fresh(b: Bool) -> {FR.put_verdict(F.judge.fresh(F.AskLoad{}, b)) == AuthRead.ar_pick(b, 0n, 1n) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ar.check_fresh(b: Bool) -> {FR.put_verdict(F.judge.fresh(F.AskCheck{}, b)) == AuthRead.ar_pick(b, 0n, 1n) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ar.store_fresh(b: Bool) -> {FR.put_verdict(F.judge.fresh(F.AskStore{}, b)) == AuthRead.ar_pick(b, 3n, 4n) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the reply the entry spells is the laws' reply
def ar.reply(a: F.Ask, +now: Nat, r: F.Read) -> {FR.put_verdict(F.judge(F.Query{a, now, r})) == AuthRead.ar_reply(a, now, r) : String}:
  match a:
    case F.AskLoad{}:
      match r:
        case F.Unread{}:
          {==}
        case F.NoCred{}:
          {==}
        case F.NotOauth{}:
          {==}
        case F.Oauth{+e}:
          ar.load_fresh(Nat.is_lt(now, e))
    case F.AskCheck{}:
      match r:
        case F.Unread{}:
          {==}
        case F.NoCred{}:
          {==}
        case F.NotOauth{}:
          {==}
        case F.Oauth{+e}:
          ar.check_fresh(Nat.is_lt(now, e))
    case F.AskStore{}:
      match r:
        case F.Unread{}:
          {==}
        case F.NoCred{}:
          {==}
        case F.NotOauth{}:
          {==}
        case F.Oauth{+e}:
          ar.store_fresh(Nat.is_lt(now, e))

# no verdict opens with 'E'
def ar.verdict_ok(v: F.Verdict) -> {LawsBase.wire_opens_err(FR.put_verdict(v)) == False{} : Bool}:
  match v:
    case F.Serve{}:
      {==}
    case F.Refresh{}:
      {==}
    case F.Refuse{}:
      {==}
    case F.KeepPeer{}:
      {==}
    case F.Write{}:
      {==}

# Spellings with input after them
# -------------------------------

# what a read found, as Rust writes it, then x
def ar.read_then(r: F.Read, x: String) -> String:
  match r:
    case F.Unread{}:
      Wr.put_nat(0n, x)
    case F.NoCred{}:
      Wr.put_nat(1n, x)
    case F.NotOauth{}:
      Wr.put_nat(2n, x)
    case F.Oauth{e}:
      Wr.put_nat(3n, Wr.put_nat(e, x))

# the request Rust writes, then x
def ar.spell_then(a: F.Ask, now: Nat, r: F.Read, x: String) -> String:
  Wr.put_nat(AuthRead.ar_ask_tag(a), Wr.put_nat(now, ar.read_then(r, x)))

def ar.read_nil(r: F.Read) -> {ar.read_then(r, "") == AuthRead.ar_spell_read(r) : String}:
  match r:
    case F.Unread{}:
      {==}
    case F.NoCred{}:
      {==}
    case F.NotOauth{}:
      {==}
    case F.Oauth{e}:
      {==}

def ar.spell_nil(+a: F.Ask, +now: Nat, +r: F.Read) -> {ar.spell_then(a, now, r, "") == AuthRead.ar_spell(a, now, r) : String}:
  Equal.cong(String, String, z => Wr.put_nat(AuthRead.ar_ask_tag(a), Wr.put_nat(now, z)), ar.read_then(r, ""), AuthRead.ar_spell_read(r), ar.read_nil(r))

# the digits before acc, then x: the digits before acc then x
def ar.emit_app(ds: List<&2, Nat>, acc: String, +x: String) -> {String.append(LLogicString.wn_emit(ds, acc), x) == LLogicString.wn_emit(ds, String.append(acc, x)) : String}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, t}:
      ar.emit_app(t, SCon{Wr.dchar(d), acc}, x)

# a Nat then s, then x: the Nat then s then x
def ar.nat_app(+n: Nat, +s: String, +x: String) -> {String.append(Wr.put_nat(n, s), x) == Wr.put_nat(n, String.append(s, x)) : String}:
  %Equal.sym(String, Wr.put_nat(n, s), LLogicString.wn_emit(LLogicList.wn_full(n), SCon{',', s}), LWire.wn_put_emit(n, s)) : {String.append(_, x) == Wr.put_nat(n, String.append(s, x)) : String}
  %Equal.sym(String, Wr.put_nat(n, String.append(s, x)), LLogicString.wn_emit(LLogicList.wn_full(n), SCon{',', String.append(s, x)}), LWire.wn_put_emit(n, String.append(s, x))) : {String.append(LLogicString.wn_emit(LLogicList.wn_full(n), SCon{',', s}), x) == _ : String}
  ar.emit_app(LLogicList.wn_full(n), SCon{',', s}, x)

def ar.read_app(r: F.Read, +x: String) -> {String.append(AuthRead.ar_spell_read(r), x) == ar.read_then(r, x) : String}:
  match r:
    case F.Unread{}:
      ar.nat_app(0n, "", x)
    case F.NoCred{}:
      ar.nat_app(1n, "", x)
    case F.NotOauth{}:
      ar.nat_app(2n, "", x)
    case F.Oauth{+e}:
      Equal.trans(String, String.append(Wr.put_nat(3n, Wr.put_nat(e, "")), x), Wr.put_nat(3n, String.append(Wr.put_nat(e, ""), x)), Wr.put_nat(3n, Wr.put_nat(e, x)), ar.nat_app(3n, Wr.put_nat(e, ""), x), Equal.cong(String, String, z => Wr.put_nat(3n, z), String.append(Wr.put_nat(e, ""), x), Wr.put_nat(e, x), ar.nat_app(e, "", x)))

# a request Rust writes with x after it is the request then x
def ar.spell_app(+a: F.Ask, +now: Nat, +r: F.Read, +x: String) -> {String.append(AuthRead.ar_spell(a, now, r), x) == ar.spell_then(a, now, r, x) : String}:
  +t = AuthRead.ar_ask_tag(a)
  +sr = AuthRead.ar_spell_read(r)
  Equal.trans(String, String.append(Wr.put_nat(t, Wr.put_nat(now, sr)), x), Wr.put_nat(t, String.append(Wr.put_nat(now, sr), x)), ar.spell_then(a, now, r, x), ar.nat_app(t, Wr.put_nat(now, sr), x),
    Equal.cong(String, String, z => Wr.put_nat(t, z), String.append(Wr.put_nat(now, sr), x), Wr.put_nat(now, ar.read_then(r, x)),
      Equal.trans(String, String.append(Wr.put_nat(now, sr), x), Wr.put_nat(now, String.append(sr, x)), Wr.put_nat(now, ar.read_then(r, x)), ar.nat_app(now, sr, x),
        Equal.cong(String, String, z => Wr.put_nat(now, z), String.append(sr, x), ar.read_then(r, x), ar.read_app(r, x)))))

# Round trips
# -----------

# what a read found, as Rust writes it, reads back, x untouched
def ar.read_found(r: F.Read, +x: String, fr: {AuthRead.ar_read_fits(r) == True{} : Bool}) -> {Wr.Got{r, x} == FR.get_read(Wr.get_nat(ar.read_then(r, x))) : Wr.Dec<F.Read>}:
  match r:
    case F.Unread{}:
      %LWire.pw6.nat(0n, x, {==}) : {Wr.Got{F.Unread{}, x} == FR.get_read(_) : Wr.Dec<F.Read>}
      {==}
    case F.NoCred{}:
      %LWire.pw6.nat(1n, x, {==}) : {Wr.Got{F.NoCred{}, x} == FR.get_read(_) : Wr.Dec<F.Read>}
      {==}
    case F.NotOauth{}:
      %LWire.pw6.nat(2n, x, {==}) : {Wr.Got{F.NotOauth{}, x} == FR.get_read(_) : Wr.Dec<F.Read>}
      {==}
    case F.Oauth{+e}:
      %LWire.pw6.nat(3n, Wr.put_nat(e, x), {==}) : {Wr.Got{F.Oauth{e}, x} == FR.get_read(_) : Wr.Dec<F.Read>}
      %LWire.pw6.nat(e, x, fr) : {Wr.Got{F.Oauth{e}, x} == FR.get_read.oauth(_) : Wr.Dec<F.Read>}
      {==}

# the clock and what the read found read back
def ar.spell_now(+a: F.Ask, +now: Nat, +r: F.Read, +x: String, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, fr: {AuthRead.ar_read_fits(r) == True{} : Bool}) -> {Wr.Got{F.Query{a, now, r}, x} == FR.get_query.now(a, Wr.get_nat(Wr.put_nat(now, ar.read_then(r, x)))) : Wr.Dec<F.Query>}:
  %LWire.pw6.nat(now, ar.read_then(r, x), fnow) : {Wr.Got{F.Query{a, now, r}, x} == FR.get_query.now(a, _) : Wr.Dec<F.Query>}
  %ar.read_found(r, x, fr) : {Wr.Got{F.Query{a, now, r}, x} == FR.get_query.read(a, now, _) : Wr.Dec<F.Query>}
  {==}

# every request Rust writes reads back, the input after it untouched
def ar.spell_go(a: F.Ask, +now: Nat, +r: F.Read, +x: String, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, fr: {AuthRead.ar_read_fits(r) == True{} : Bool}) -> {Wr.Got{F.Query{a, now, r}, x} == FR.get_query(Wr.get_nat(ar.spell_then(a, now, r, x))) : Wr.Dec<F.Query>}:
  match a:
    case F.AskLoad{}:
      %LWire.pw6.nat(0n, Wr.put_nat(now, ar.read_then(r, x)), {==}) : {Wr.Got{F.Query{F.AskLoad{}, now, r}, x} == FR.get_query(_) : Wr.Dec<F.Query>}
      ar.spell_now(F.AskLoad{}, now, r, x, fnow, fr)
    case F.AskCheck{}:
      %LWire.pw6.nat(1n, Wr.put_nat(now, ar.read_then(r, x)), {==}) : {Wr.Got{F.Query{F.AskCheck{}, now, r}, x} == FR.get_query(_) : Wr.Dec<F.Query>}
      ar.spell_now(F.AskCheck{}, now, r, x, fnow, fr)
    case F.AskStore{}:
      %LWire.pw6.nat(2n, Wr.put_nat(now, ar.read_then(r, x)), {==}) : {Wr.Got{F.Query{F.AskStore{}, now, r}, x} == FR.get_query(_) : Wr.Dec<F.Query>}
      ar.spell_now(F.AskStore{}, now, r, x, fnow, fr)

# on every request Rust writes, the entry answers the laws' reply
def ar.answers_fwd(+a: F.Ask, +now: Nat, +r: F.Read, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, fr: {AuthRead.ar_read_fits(r) == True{} : Bool}) -> {FR.ffi(AuthRead.ar_spell(a, now, r)) == AuthRead.ar_reply(a, now, r) : String}:
  %ar.spell_nil(a, now, r) : {FR.ffi(_) == AuthRead.ar_reply(a, now, r) : String}
  %ar.spell_go(a, now, r, "", fnow, fr) : {FR.ffi.go(_) == AuthRead.ar_reply(a, now, r) : String}
  ar.reply(a, now, r)

def ar.answers(+a: F.Ask, +now: Nat, +r: F.Read, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, fr: {AuthRead.ar_read_fits(r) == True{} : Bool}) -> {AuthRead.ar_reply(a, now, r) == FR.ffi(AuthRead.ar_spell(a, now, r)) : String}:
  Equal.sym(String, FR.ffi(AuthRead.ar_spell(a, now, r)), AuthRead.ar_reply(a, now, r), ar.answers_fwd(a, now, r, fnow, fr))

# a request Rust writes with more input after it answers the error form
def ar.left_over(+a: F.Ask, +now: Nat, +r: F.Read, +c: Char, +t: String, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, fr: {AuthRead.ar_read_fits(r) == True{} : Bool}) -> {FR.ffi(String.append(AuthRead.ar_spell(a, now, r), SCon{c, t})) == Wr.err("auth_read: malformed request") : String}:
  %Equal.sym(String, String.append(AuthRead.ar_spell(a, now, r), SCon{c, t}), ar.spell_then(a, now, r, SCon{c, t}), ar.spell_app(a, now, r, SCon{c, t})) : {FR.ffi(_) == Wr.err("auth_read: malformed request") : String}
  %ar.spell_go(a, now, r, SCon{c, t}, fnow, fr) : {FR.ffi.go(_) == Wr.err("auth_read: malformed request") : String}
  {==}

# Decoded requests are spelled
# ----------------------------

# the query q read with rr left is the request Rust writes then rr, its
# clock and expiry within the wire
def ar.QP(s: String, q: F.Query, rr: String) -> Type:
  match q:
    case F.Query{a, now, r}:
      {s == ar.spell_then(a, now, r, rr) : String} & {AuthRead.ar_fits_q(F.Query{a, now, r}) == True{} : Bool}

def ar.RP(s: String, d: Wr.Dec<F.Query>) -> Type:
  match d:
    case Wr.Got{q, rr}:
      ar.QP(s, q, rr)
    case Wr.Bad{}:
      Unit

# s is the tag and the clock then s1, and s1 is y
def ar.then2(-s: String, +t: Nat, +now: Nat, -s1: String, -y: String, pre: {s == Wr.put_nat(t, Wr.put_nat(now, s1)) : String}, e: {s1 == y : String}) -> {s == Wr.put_nat(t, Wr.put_nat(now, y)) : String}:
  Equal.trans(String, s, Wr.put_nat(t, Wr.put_nat(now, s1)), Wr.put_nat(t, Wr.put_nat(now, y)), pre, Equal.cong(String, String, z => Wr.put_nat(t, Wr.put_nat(now, z)), s1, y, e))

def ar.x.oauth(-s: String, +a: F.Ask, +now: Nat, +s2: String, pre: {s == Wr.put_nat(AuthRead.ar_ask_tag(a), Wr.put_nat(now, Wr.put_nat(3n, s2))) : String}, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> ar.RP(s, FR.get_query.read(a, now, FR.get_read.oauth(d))):
  match d:
    case Wr.Got{+e, +s3}:
      +ee = ed
      (ar.then2(s, AuthRead.ar_ask_tag(a), now, Wr.put_nat(3n, s2), Wr.put_nat(3n, Wr.put_nat(e, s3)), pre, Equal.cong(String, String, z => Wr.put_nat(3n, z), s2, Wr.put_nat(e, s3), Wire.wire_nat_exact(s2, e, s3, ee))),
        ar.and(LawsBase.wire_fits(e), LawsBase.wire_fits(now), Wire.wire_nat_decoded_fits(s2, e, s3, ee), fnow))
    case Wr.Bad{}:
      Unit{}

def ar.x.found(t: Nat, -s: String, +a: F.Ask, +now: Nat, -s1: String, +s2: String, pre: {s == Wr.put_nat(AuthRead.ar_ask_tag(a), Wr.put_nat(now, s1)) : String}, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, e1: {s1 == Wr.put_nat(t, s2) : String}) -> ar.RP(s, FR.get_query.read(a, now, FR.get_read.tag(t, s2))):
  match t:
    case 0n:
      (ar.then2(s, AuthRead.ar_ask_tag(a), now, s1, Wr.put_nat(0n, s2), pre, e1), fnow)
    case 1n:
      (ar.then2(s, AuthRead.ar_ask_tag(a), now, s1, Wr.put_nat(1n, s2), pre, e1), fnow)
    case 2n:
      (ar.then2(s, AuthRead.ar_ask_tag(a), now, s1, Wr.put_nat(2n, s2), pre, e1), fnow)
    case 3n:
      ar.x.oauth(s, a, now, s2, ar.then2(s, AuthRead.ar_ask_tag(a), now, s1, Wr.put_nat(3n, s2), pre, e1), fnow, Wr.get_nat(s2), {==})
    case 4n+p:
      Unit{}

def ar.x.read(-s: String, +a: F.Ask, +now: Nat, +s1: String, pre: {s == Wr.put_nat(AuthRead.ar_ask_tag(a), Wr.put_nat(now, s1)) : String}, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> ar.RP(s, FR.get_query.read(a, now, FR.get_read(d))):
  match d:
    case Wr.Got{+t, +s2}:
      ar.x.found(t, s, a, now, s1, s2, pre, fnow, Wire.wire_nat_exact(s1, t, s2, ed))
    case Wr.Bad{}:
      Unit{}

def ar.x.now(-s: String, +a: F.Ask, +s0: String, pre: {s == Wr.put_nat(AuthRead.ar_ask_tag(a), s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> ar.RP(s, FR.get_query.now(a, d)):
  match d:
    case Wr.Got{+now, +s1}:
      +ee = ed
      +pre2 = Equal.trans(String, s, Wr.put_nat(AuthRead.ar_ask_tag(a), s0), Wr.put_nat(AuthRead.ar_ask_tag(a), Wr.put_nat(now, s1)), pre, Equal.cong(String, String, z => Wr.put_nat(AuthRead.ar_ask_tag(a), z), s0, Wr.put_nat(now, s1), Wire.wire_nat_exact(s0, now, s1, ee)))
      ar.x.read(s, a, now, s1, pre2, Wire.wire_nat_decoded_fits(s0, now, s1, ee), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def ar.x.tag(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ar.RP(s, FR.get_query(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          ar.x.now(s, F.AskLoad{}, s0, Wire.wire_nat_exact(s, 0n, s0, ed), Wr.get_nat(s0), {==})
        case 1n:
          ar.x.now(s, F.AskCheck{}, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_nat(s0), {==})
        case 2n:
          ar.x.now(s, F.AskStore{}, s0, Wire.wire_nat_exact(s, 2n, s0, ed), Wr.get_nat(s0), {==})
        case 3n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def ar.T(s: String) -> Type:
  Sigma<&1, &1, F.Query, q => {s == AuthRead.ar_spell_q(q) : String} & {AuthRead.ar_fits_q(q) == True{} : Bool}>

def ar.top_q(-s: String, q: F.Query, qp: ar.QP(s, q, "")) -> ar.T(s):
  match q:
    case F.Query{+a, +now, +r}:
      (e, f) = qp
      (F.Query{a, now, r}, (Equal.trans(String, s, ar.spell_then(a, now, r, ""), AuthRead.ar_spell(a, now, r), e, ar.spell_nil(a, now, r)), f))

# a value answered: a request read whole, nothing left
def ar.top(-s: String, d: Wr.Dec<F.Query>, rp: ar.RP(s, d), ok: {LawsBase.wire_opens_err(FR.ffi.go(d)) == False{} : Bool}) -> ar.T(s):
  match d:
    case Wr.Got{q, rest}:
      match rest:
        case SNil{}:
          ar.top_q(s, q, rp)
        case SCon{y, z}:
          ar.absurd(ar.T(s), ok)
    case Wr.Bad{}:
      ar.absurd(ar.T(s), ok)

# an answer that opens with 'E' is the one error form
def ar.refuse(d: Wr.Dec<F.Query>, bad: {LawsBase.wire_opens_err(FR.ffi.go(d)) == True{} : Bool}) -> {FR.ffi.go(d) == Wr.err("auth_read: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          ar.absurd({FR.put_verdict(F.judge(q)) == Wr.err("auth_read: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FR.put_verdict(F.judge(q))), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FR.put_verdict(F.judge(q))), True{}, bad), ar.verdict_ok(F.judge(q))))
        case SCon{y, z}:
          {==}
    case Wr.Bad{}:
      {==}
