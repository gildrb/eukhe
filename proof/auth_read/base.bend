# eukhe: lemmas the proofs of the auth_read entry share
# The entry (bend/ffi_auth_read.bend) reads every input as the laws'
# reader does, answers the laws' reply, and reads back every request Rust
# writes.

import Base
import ../../bend/auth_flight.bend as F
import ../../bend/ffi_auth_read.bend as FR
import ../../bend/wire.bend as Wr
import ../../laws/auth_read.bend as AuthRead
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire

# Maybe
# -----

def ar.MD(-A: Data, m: Maybe<&2, A>, n: Type, s: Type) -> Type:
  match m:
    case None{}:
      n
    case Some{x}:
      s

# a None that is a Some proves anything
def ar.none_some(-A: Data, -G: Type, -x: A, e: {None{} == Some{x} : Maybe<&2, A>}) -> G:
  %e : ar.MD(A, _, Unit, G)
  Unit{}

# a Some that is a None proves anything
def ar.some_none(-A: Data, -G: Type, -x: A, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  %e : ar.MD(A, _, G, Unit)
  Unit{}

def ar.some_inj(-A: Data, +d: A, -x: A, -y: A, e: {Some{x} == Some{y} : Maybe<&2, A>}) -> {x == y : A}:
  Equal.cong(Maybe<&2, A>, A, m => Maybe.default(&2, A, m, d), Some{x}, Some{y}, e)

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
def ar.reply(q: F.Query) -> {FR.put_verdict(F.judge(q)) == AuthRead.ar_reply_q(q) : String}:
  match q:
    case F.Query{a, +now, r}:
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

# The reader
# ----------

def ar.oauth(r: Wr.Dec<Nat>) -> {AuthRead.ar_read.oauth(r) == FR.get_read.oauth(r) : Wr.Dec<F.Read>}:
  match r:
    case Wr.Got{e, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ar.found(t: Nat, +s: String) -> {AuthRead.ar_read.found(t, s) == FR.get_read.tag(t, s) : Wr.Dec<F.Read>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      ar.oauth(Wr.get_nat(s))
    case 4n+p:
      {==}

def ar.read(r: Wr.Dec<Nat>) -> {AuthRead.ar_read.read(r) == FR.get_read(r) : Wr.Dec<F.Read>}:
  match r:
    case Wr.Got{t, s}:
      ar.found(t, s)
    case Wr.Bad{}:
      {==}

def ar.query(+a: F.Ask, +now: Nat, r: Wr.Dec<F.Read>) -> {AuthRead.ar_read.query(a, now, r) == FR.get_query.read(a, now, r) : Wr.Dec<F.Query>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ar.now(+a: F.Ask, r: Wr.Dec<Nat>) -> {AuthRead.ar_read.now(a, r) == FR.get_query.now(a, r) : Wr.Dec<F.Query>}:
  match r:
    case Wr.Got{+now, +s}:
      %ar.read(Wr.get_nat(s)) : {AuthRead.ar_read.query(a, now, AuthRead.ar_read.read(Wr.get_nat(s))) == FR.get_query.read(a, now, _) : Wr.Dec<F.Query>}
      ar.query(a, now, AuthRead.ar_read.read(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def ar.tag(t: Nat, +s: String) -> {AuthRead.ar_read.tag(t, s) == FR.get_query.tag(t, s) : Wr.Dec<F.Query>}:
  match t:
    case 0n:
      ar.now(F.AskLoad{}, Wr.get_nat(s))
    case 1n:
      ar.now(F.AskCheck{}, Wr.get_nat(s))
    case 2n:
      ar.now(F.AskStore{}, Wr.get_nat(s))
    case 3n+p:
      {==}

# the entry reads every request as the laws' reader does
def ar.go(r: Wr.Dec<Nat>) -> {AuthRead.ar_read.go(r) == FR.get_query(r) : Wr.Dec<F.Query>}:
  match r:
    case Wr.Got{t, s}:
      ar.tag(t, s)
    case Wr.Bad{}:
      {==}

# The call
# --------

def ar.ffi_fin(b: Bool, +x: F.Query, -q: F.Query, got: {AuthRead.ar_whole(b, x) == Some{q} : Maybe<&2, F.Query>}) -> {FR.ffi.fin(b, x) == AuthRead.ar_reply_q(q) : String}:
  match b:
    case True{}:
      %ar.some_inj(F.Query, x, x, q, got) : {FR.put_verdict(F.judge(x)) == AuthRead.ar_reply_q(_) : String}
      ar.reply(x)
    case False{}:
      ar.none_some(F.Query, {FR.ffi.fin(False{}, x) == AuthRead.ar_reply_q(q) : String}, q, got)

def ar.ffi_got(r: Wr.Dec<F.Query>, -q: F.Query, got: {AuthRead.ar_read.whole(r) == Some{q} : Maybe<&2, F.Query>}) -> {FR.ffi.go(r) == AuthRead.ar_reply_q(q) : String}:
  match r:
    case Wr.Got{x, s}:
      ar.ffi_fin(Wr.end(s), x, q, got)
    case Wr.Bad{}:
      ar.none_some(F.Query, {FR.ffi.go(Wr.Bad{}) == AuthRead.ar_reply_q(q) : String}, q, got)

# a whole request gets the verdict on it
def ar.ffi_reads(+s: String, -q: F.Query, got: {AuthRead.ar_read(s) == Some{q} : Maybe<&2, F.Query>}) -> {FR.ffi(s) == AuthRead.ar_reply_q(q) : String}:
  %ar.go(Wr.get_nat(s)) : {FR.ffi.go(_) == AuthRead.ar_reply_q(q) : String}
  ar.ffi_got(AuthRead.ar_read.go(Wr.get_nat(s)), q, got)

def ar.ffi_bad_fin(b: Bool, -x: F.Query, no: {AuthRead.ar_whole(b, x) == None{} : Maybe<&2, F.Query>}) -> {FR.ffi.fin(b, x) == SCon{'E', SCon{' ', "auth_read: malformed request"}} : String}:
  match b:
    case True{}:
      ar.some_none(F.Query, {FR.ffi.fin(True{}, x) == SCon{'E', SCon{' ', "auth_read: malformed request"}} : String}, x, no)
    case False{}:
      {==}

def ar.ffi_bad(r: Wr.Dec<F.Query>, no: {AuthRead.ar_read.whole(r) == None{} : Maybe<&2, F.Query>}) -> {FR.ffi.go(r) == SCon{'E', SCon{' ', "auth_read: malformed request"}} : String}:
  match r:
    case Wr.Got{x, s}:
      ar.ffi_bad_fin(Wr.end(s), x, no)
    case Wr.Bad{}:
      {==}

# Round trips
# -----------

# what a read found, as Rust writes it, reads back
def ar.read_found(r: F.Read, fr: {AuthRead.ar_read_fits(r) == True{} : Bool}) -> {Wr.Got{r, ""} == AuthRead.ar_read.read(Wr.get_nat(AuthRead.ar_spell_read(r))) : Wr.Dec<F.Read>}:
  match r:
    case F.Unread{}:
      {==}
    case F.NoCred{}:
      {==}
    case F.NotOauth{}:
      {==}
    case F.Oauth{+e}:
      %LWire.pw6.nat(3n, Wr.put_nat(e, ""), {==}) : {Wr.Got{F.Oauth{e}, ""} == AuthRead.ar_read.read(_) : Wr.Dec<F.Read>}
      %LWire.pw6.nat(e, "", fr) : {Wr.Got{F.Oauth{e}, ""} == AuthRead.ar_read.oauth(_) : Wr.Dec<F.Read>}
      {==}

# the clock and what the read found, as Rust writes them, read back
def ar.spell_now(+a: F.Ask, +now: Nat, +r: F.Read, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, fr: {AuthRead.ar_read_fits(r) == True{} : Bool}) -> {Wr.Got{F.Query{a, now, r}, ""} == AuthRead.ar_read.now(a, Wr.get_nat(Wr.put_nat(now, AuthRead.ar_spell_read(r)))) : Wr.Dec<F.Query>}:
  %LWire.pw6.nat(now, AuthRead.ar_spell_read(r), fnow) : {Wr.Got{F.Query{a, now, r}, ""} == AuthRead.ar_read.now(a, _) : Wr.Dec<F.Query>}
  %ar.read_found(r, fr) : {Wr.Got{F.Query{a, now, r}, ""} == AuthRead.ar_read.query(a, now, _) : Wr.Dec<F.Query>}
  {==}

# every request Rust writes reads back
def ar.spell_go(a: F.Ask, +now: Nat, +r: F.Read, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, fr: {AuthRead.ar_read_fits(r) == True{} : Bool}) -> {Wr.Got{F.Query{a, now, r}, ""} == AuthRead.ar_read.go(Wr.get_nat(AuthRead.ar_spell(a, now, r))) : Wr.Dec<F.Query>}:
  match a:
    case F.AskLoad{}:
      %LWire.pw6.nat(0n, Wr.put_nat(now, AuthRead.ar_spell_read(r)), {==}) : {Wr.Got{F.Query{F.AskLoad{}, now, r}, ""} == AuthRead.ar_read.go(_) : Wr.Dec<F.Query>}
      ar.spell_now(F.AskLoad{}, now, r, fnow, fr)
    case F.AskCheck{}:
      %LWire.pw6.nat(1n, Wr.put_nat(now, AuthRead.ar_spell_read(r)), {==}) : {Wr.Got{F.Query{F.AskCheck{}, now, r}, ""} == AuthRead.ar_read.go(_) : Wr.Dec<F.Query>}
      ar.spell_now(F.AskCheck{}, now, r, fnow, fr)
    case F.AskStore{}:
      %LWire.pw6.nat(2n, Wr.put_nat(now, AuthRead.ar_spell_read(r)), {==}) : {Wr.Got{F.Query{F.AskStore{}, now, r}, ""} == AuthRead.ar_read.go(_) : Wr.Dec<F.Query>}
      ar.spell_now(F.AskStore{}, now, r, fnow, fr)

def ar.read_spell(+a: F.Ask, +now: Nat, +r: F.Read, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, fr: {AuthRead.ar_read_fits(r) == True{} : Bool}) -> {AuthRead.ar_read(AuthRead.ar_spell(a, now, r)) == Some{F.Query{a, now, r}} : Maybe<&2, F.Query>}:
  %ar.spell_go(a, now, r, fnow, fr) : {AuthRead.ar_read.whole(_) == Some{F.Query{a, now, r}} : Maybe<&2, F.Query>}
  {==}

# on every request Rust writes, the entry answers the laws' reply
def ar.answers(+a: F.Ask, +now: Nat, +r: F.Read, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, fr: {AuthRead.ar_read_fits(r) == True{} : Bool}) -> {AuthRead.ar_reply(a, now, r) == FR.ffi(AuthRead.ar_spell(a, now, r)) : String}:
  Equal.sym(String, FR.ffi(AuthRead.ar_spell(a, now, r)), AuthRead.ar_reply(a, now, r), ar.ffi_reads(AuthRead.ar_spell(a, now, r), F.Query{a, now, r}, ar.read_spell(a, now, r, fnow, fr)))
