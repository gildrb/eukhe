# eukhe: the proof of LAW staging_entry_exact
#
# PROOF of LAW staging_entry_exact: each decoder of bend/ffi_staging.bend
# answers Got{x, rest} only for an input that is the spec's spelling of x
# before rest, with x within the wire (ex.*: a predicate per decoder
# answer, carried stage by stage with the wire's exactness laws
# wire_nat_exact, wire_str_exact, wire_bool_exact and their fits
# wire_nat_decoded_fits, ex.str_fits). The entry answers a value only
# for a request read whole with nothing left: that input is the spelled
# request (ex.top).

import Base
import ../../bend/ffi_staging.bend as FSg
import ../../bend/staging.bend as Sg
import ../../bend/listing.bend as Ls
import ../../bend/wire.bend as Wr
import ../../laws/staging.bend as Staging
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_nat_too_long.bend as PWireNatTooLong
import ../wire/wire_str_exact.bend as PWireStrExact
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../base/wire.bend as LWire
import ../base/logic/string.bend as LLogicString
import ./staging_entry_answers.bend as PA

# Logic
# -----

def ex.DT(-A: Data, d: Wr.Dec<A>, G: Type) -> Type:
  match d:
    case Wr.Got{x, r}:
      Unit
    case Wr.Bad{}:
      G

# a decoder answered Got and Bad
def ex.got_bad(-A: Data, -G: Type, -x: A, -r: String, e: {Wr.Got{x, r} == Wr.Bad{} : Wr.Dec<A>}) -> G:
  %e : ex.DT(A, _, G)
  Unit{}

def ex.tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  PA.se.ft(G, Equal.sym(Bool, True{}, False{}, e))

# Primitives
# ----------

def ex.NP(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ex.nat.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ex.NP(s, d):
  match d:
    case Wr.Got{+n, +r}:
      +e2 = ed
      (Wire.wire_nat_exact(s, n, r, e2), Wire.wire_nat_decoded_fits(s, n, r, e2))
    case Wr.Bad{}:
      Unit{}

def ex.nat(+s: String) -> ex.NP(s, Wr.get_nat(s)):
  ex.nat.at(s, Wr.get_nat(s), {==})

# a decoded string's length fits: a longer one's count is refused
def ex.str_fits.at(b: Bool, +s: String, +a: String, +r: String, eb: {LawsBase.wire_fits(String.length(a)) == b : Bool}, e1: {s == Wr.put_str(a, r) : String}, ed: {Wr.get_str(s) == Wr.Got{a, r} : Wr.Dec<String>}) -> {LawsBase.wire_fits(String.length(a)) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      +x = LLogicString.wr_app(a, r)
      +c1 = Equal.trans(Wr.Dec<String>, Wr.Got{a, r}, Wr.get_str(s), Wr.get_str(Wr.put_str(a, r)), Equal.sym(Wr.Dec<String>, Wr.get_str(s), Wr.Got{a, r}, ed), Equal.cong(String, Wr.Dec<String>, z => Wr.get_str(z), s, Wr.put_str(a, r), e1))
      +c2 = Equal.trans(Wr.Dec<String>, Wr.Got{a, r}, Wr.get_str(Wr.put_str(a, r)), Wr.get_str(Wr.put_nat(String.length(a), x)), c1, Equal.cong(String, Wr.Dec<String>, z => Wr.get_str(z), Wr.put_str(a, r), Wr.put_nat(String.length(a), x), LWire.wr_put_str(a, r)))
      +c3 = Equal.trans(Wr.Dec<String>, Wr.Got{a, r}, Wr.get_str(Wr.put_nat(String.length(a), x)), Wr.Bad{}, c2, Equal.cong(Wr.Dec<Nat>, Wr.Dec<String>, z => Wr.get_str.go(z), Wr.get_nat(Wr.put_nat(String.length(a), x)), Wr.Bad{}, Wire.wire_nat_too_long(String.length(a), x, eb)))
      ex.got_bad(String, {LawsBase.wire_fits(String.length(a)) == True{} : Bool}, a, r, c3)

def ex.SP(s: String, d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {s == Wr.put_str(a, r) : String} & {LawsBase.wire_fits(String.length(a)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ex.str.at(+s: String, d: Wr.Dec<String>, ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> ex.SP(s, d):
  match d:
    case Wr.Got{+a, +r}:
      +e2 = ed
      +e1 = Wire.wire_str_exact(s, a, r, e2)
      (e1, ex.str_fits.at(LawsBase.wire_fits(String.length(a)), s, a, r, {==}, e1, e2))
    case Wr.Bad{}:
      Unit{}

def ex.str(+s: String) -> ex.SP(s, Wr.get_str(s)):
  ex.str.at(s, Wr.get_str(s), {==})

def ex.BP(s: String, d: Wr.Dec<Bool>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == Wr.put_bool(b, r) : String}
    case Wr.Bad{}:
      Unit

def ex.bool.at(+s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> ex.BP(s, d):
  match d:
    case Wr.Got{+b, +r}:
      Wire.wire_bool_exact(s, b, r, ed)
    case Wr.Bad{}:
      Unit{}

def ex.bool(+s: String) -> ex.BP(s, Wr.get_bool(s)):
  ex.bool.at(s, Wr.get_bool(s), {==})

def ex.and_tt(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

# s is the tag t then s1, and s1 is x: s is the tag t then x
def ex.after(-s: String, +t: Nat, -s1: String, -x: String, pre: {s == Wr.put_nat(t, s1) : String}, e: {s1 == x : String}) -> {s == Wr.put_nat(t, x) : String}:
  Equal.trans(String, s, Wr.put_nat(t, s1), Wr.put_nat(t, x), pre, Equal.cong(String, String, z => Wr.put_nat(t, z), s1, x, e))

# Names
# -----

def ex.NF(n: Sg.Name) -> Type:
  match n:
    case Sg.Utf{a}:
      {LawsBase.wire_fits(String.length(a)) == True{} : Bool}
    case Sg.Raw{}:
      Unit

def ex.NmP(s: String, d: Wr.Dec<Sg.Name>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Staging.sp_w_name(n, r) : String} & ex.NF(n)
    case Wr.Bad{}:
      Unit

def ex.name.utf(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<String>, sp: ex.SP(s1, d)) -> ex.NmP(s, FSg.get_name.utf(d)):
  match d:
    case Wr.Got{+a, +r}:
      (e, f) = sp
      (ex.after(s, 0n, s1, Wr.put_str(a, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def ex.name.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> ex.NmP(s, FSg.get_name.tag(t, s1)):
  match t:
    case 0n:
      ex.name.utf(s, s1, pre, Wr.get_str(s1), ex.str(s1))
    case 1n+p:
      match p:
        case 0n:
          (pre, Unit{})
        case 1n+q:
          Unit{}

def ex.name.go(-s: String, d: Wr.Dec<Nat>, np: ex.NP(s, d)) -> ex.NmP(s, FSg.get_name.go(d)):
  match d:
    case Wr.Got{t, s1}:
      (e, f) = np
      ex.name.tag(t, s1, s, e)
    case Wr.Bad{}:
      Unit{}

def ex.name(+s: String) -> ex.NmP(s, FSg.get_name(s)):
  ex.name.go(s, Wr.get_nat(s), ex.nat(s))

# Forms
# -----

def ex.FmP(s: String, d: Wr.Dec<Sg.Form>) -> Type:
  match d:
    case Wr.Got{k, r}:
      {s == Staging.sp_w_form(k, r) : String}
    case Wr.Bad{}:
      Unit

def ex.form.dir(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Bool>, bp: ex.BP(s1, d)) -> ex.FmP(s, FSg.get_form.dir(d)):
  match d:
    case Wr.Got{+m, +r}:
      ex.after(s, 0n, s1, Wr.put_bool(m, r), pre, bp)
    case Wr.Bad{}:
      Unit{}

def ex.form.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> ex.FmP(s, FSg.get_form.tag(t, s1)):
  match t:
    case 0n:
      ex.form.dir(s, s1, pre, Wr.get_bool(s1), ex.bool(s1))
    case 1n+p:
      match p:
        case 0n:
          pre
        case 1n+q:
          match q:
            case 0n:
              pre
            case 1n+u:
              Unit{}

def ex.form.go(-s: String, d: Wr.Dec<Nat>, np: ex.NP(s, d)) -> ex.FmP(s, FSg.get_form.go(d)):
  match d:
    case Wr.Got{t, s1}:
      (e, f) = np
      ex.form.tag(t, s1, s, e)
    case Wr.Bad{}:
      Unit{}

def ex.form(+s: String) -> ex.FmP(s, FSg.get_form(s)):
  ex.form.go(s, Wr.get_nat(s), ex.nat(s))

# Seen
# ----

def ex.SeP(s: String, d: Wr.Dec<Sg.Seen>) -> Type:
  match d:
    case Wr.Got{e, r}:
      {s == Staging.sp_w_seen(e, r) : String} & {Staging.sp_fit_seen(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ex.nf(n: Sg.Name, -k: Sg.Form, nf: ex.NF(n)) -> {Staging.sp_fit_seen(Sg.Seen{n, k}) == True{} : Bool}:
  match n:
    case Sg.Utf{a}:
      nf
    case Sg.Raw{}:
      {==}

def ex.seen.form(-s: String, +n: Sg.Name, -s1: String, pre: {s == Staging.sp_w_name(n, s1) : String}, nf: ex.NF(n), d: Wr.Dec<Sg.Form>, fp: ex.FmP(s1, d)) -> ex.SeP(s, FSg.get_seen.form(n, d)):
  match d:
    case Wr.Got{+k, +r}:
      (Equal.trans(String, s, Staging.sp_w_name(n, s1), Staging.sp_w_name(n, Staging.sp_w_form(k, r)), pre, Equal.cong(String, String, z => Staging.sp_w_name(n, z), s1, Staging.sp_w_form(k, r), fp)), ex.nf(n, k, nf))
    case Wr.Bad{}:
      Unit{}

def ex.seen.go(-s: String, d: Wr.Dec<Sg.Name>, nmp: ex.NmP(s, d)) -> ex.SeP(s, FSg.get_seen.go(d)):
  match d:
    case Wr.Got{+n, +s1}:
      (e, nf) = nmp
      ex.seen.form(s, n, s1, e, nf, FSg.get_form(s1), ex.form(s1))
    case Wr.Bad{}:
      Unit{}

def ex.seen(+s: String) -> ex.SeP(s, FSg.get_seen(s)):
  ex.seen.go(s, FSg.get_name(s), ex.name(s))

# Time
# ----

def ex.TP(s: String, d: Wr.Dec<Sg.Time>) -> Type:
  match d:
    case Wr.Got{t, r}:
      {s == Staging.sp_w_time(t, r) : String} & {Staging.sp_fit_time(t) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ex.time.nanos(-s: String, +secs: Nat, -s1: String, pre: {s == Wr.put_nat(secs, s1) : String}, fs: {LawsBase.wire_fits(secs) == True{} : Bool}, d: Wr.Dec<Nat>, np: ex.NP(s1, d)) -> ex.TP(s, FSg.get_time.nanos(secs, d)):
  match d:
    case Wr.Got{+n, +r}:
      (e, fn) = np
      (ex.after(s, secs, s1, Wr.put_nat(n, r), pre, e), ex.and_tt(LawsBase.wire_fits(secs), LawsBase.wire_fits(n), fs, fn))
    case Wr.Bad{}:
      Unit{}

def ex.time.go(-s: String, d: Wr.Dec<Nat>, np: ex.NP(s, d)) -> ex.TP(s, FSg.get_time.go(d)):
  match d:
    case Wr.Got{+secs, +s1}:
      (e, f) = np
      ex.time.nanos(s, secs, s1, e, f, Wr.get_nat(s1), ex.nat(s1))
    case Wr.Bad{}:
      Unit{}

def ex.time(+s: String) -> ex.TP(s, FSg.get_time(s)):
  ex.time.go(s, Wr.get_nat(s), ex.nat(s))

# Cwd
# ---

def ex.CP(s: String, d: Wr.Dec<Maybe<&2, String>>) -> Type:
  match d:
    case Wr.Got{c, r}:
      {s == Staging.sp_w_cwd(c, r) : String} & {Staging.sp_fit_cwd(c) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ex.cwd.some(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, sp: ex.SP(s1, d)) -> ex.CP(s, FSg.get_cwd.some(d)):
  match d:
    case Wr.Got{+a, +r}:
      (e, f) = sp
      (ex.after(s, 1n, s1, Wr.put_str(a, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def ex.cwd.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> ex.CP(s, FSg.get_cwd.tag(t, s1)):
  match t:
    case 0n:
      (pre, {==})
    case 1n+p:
      match p:
        case 0n:
          ex.cwd.some(s, s1, pre, Wr.get_str(s1), ex.str(s1))
        case 1n+q:
          Unit{}

def ex.cwd.go(-s: String, d: Wr.Dec<Nat>, np: ex.NP(s, d)) -> ex.CP(s, FSg.get_cwd.go(d)):
  match d:
    case Wr.Got{t, s1}:
      (e, f) = np
      ex.cwd.tag(t, s1, s, e)
    case Wr.Bad{}:
      Unit{}

def ex.cwd(+s: String) -> ex.CP(s, FSg.get_cwd(s)):
  ex.cwd.go(s, Wr.get_nat(s), ex.nat(s))

# Cand and lock
# -------------

def ex.CaP(s: String, d: Wr.Dec<Sg.Cand>) -> Type:
  match d:
    case Wr.Got{c, r}:
      {s == Staging.sp_w_cand(c, r) : String}
    case Wr.Bad{}:
      Unit

def ex.cand.tag(t: Nat, s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> ex.CaP(s, FSg.get_cand.tag(t, s1)):
  match t:
    case 0n:
      pre
    case 1n+p:
      match p:
        case 0n:
          pre
        case 1n+q:
          Unit{}

def ex.cand(-s: String, d: Wr.Dec<Nat>, np: ex.NP(s, d)) -> ex.CaP(s, FSg.get_cand.go(d)):
  match d:
    case Wr.Got{t, s1}:
      (e, f) = np
      ex.cand.tag(t, s1, s, e)
    case Wr.Bad{}:
      Unit{}

def ex.LkP(s: String, d: Wr.Dec<Sg.Lock>) -> Type:
  match d:
    case Wr.Got{l, r}:
      {s == Staging.sp_w_lock(l, r) : String}
    case Wr.Bad{}:
      Unit

def ex.lock.tag(t: Nat, s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> ex.LkP(s, FSg.get_lock.tag(t, s1)):
  match t:
    case 0n:
      pre
    case 1n+p:
      match p:
        case 0n:
          pre
        case 1n+q:
          match q:
            case 0n:
              pre
            case 1n+u:
              Unit{}

def ex.lock(-s: String, d: Wr.Dec<Nat>, np: ex.NP(s, d)) -> ex.LkP(s, FSg.get_lock.go(d)):
  match d:
    case Wr.Got{t, s1}:
      (e, f) = np
      ex.lock.tag(t, s1, s, e)
    case Wr.Bad{}:
      Unit{}

# Lists of seens
# ------------

def ex.seens_PL(s: String, m: Nat, d: Wr.Dec<List<&2, Sg.Seen>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      ({s == PA.se.seens_items(xs, r) : String} & {List.length(&2, Sg.Seen, xs) == 1n+m : Nat}) & {Staging.sp_fit_seens.all(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ex.seens_step(-s: String, +x: Sg.Seen, +s3: String, -k: Nat, ex1: {s == Staging.sp_w_seen(x, s3) : String}, fx: {Staging.sp_fit_seen(x) == True{} : Bool},
  d: Wr.Dec<List<&2, Sg.Seen>>, ih: ex.seens_PL(s3, k, d)) -> ex.seens_PL(s, 1n+k, Wr.get_list.cons(Sg.Seen, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (h, fa) = ih
      (e1, e2) = h
      ((Equal.trans(String, s, Staging.sp_w_seen(x, s3), Staging.sp_w_seen(x, PA.se.seens_items(ys, r)), ex1,
          Equal.cong(String, String, z => Staging.sp_w_seen(x, z), s3, PA.se.seens_items(ys, r), e1)),
        Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Sg.Seen, ys), 1n+k, e2)),
        ex.and_tt(Staging.sp_fit_seen(x), Staging.sp_fit_seens.all(ys), fx, fa))
    case Wr.Bad{}:
      Unit{}

def ex.seens_loop(m: Nat, cur: Wr.Dec<Sg.Seen>, +s: String, xp: ex.SeP(s, cur)) -> ex.seens_PL(s, m, Wr.get_list.go(~Sg.Seen, ~FSg.get_seen, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = xp
      ((e, {==}), ex.and_tt(Staging.sp_fit_seen(x), True{}, f, {==}))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = xp
      ex.seens_step(s, x, s3, k, e, f, Wr.get_list.go(~Sg.Seen, ~FSg.get_seen, k, FSg.get_seen(s3)), ex.seens_loop(k, FSg.get_seen(s3), s3, ex.seen(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def ex.seens_TP(s: String, d: Wr.Dec<List<&2, Sg.Seen>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_list(~Sg.Seen, ~Staging.sp_w_seen, xs, r) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, Sg.Seen, xs)), Staging.sp_fit_seens.all(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ex.seens_conv2(-s: String, +s2: String, +m: Nat, +xs: List<&2, Sg.Seen>, +r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, fm: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  e1: {s2 == PA.se.seens_items(xs, r) : String}, +e2: {List.length(&2, Sg.Seen, xs) == 1n+m : Nat}, fa: {Staging.sp_fit_seens.all(xs) == True{} : Bool}) ->
  ({s == Wr.put_list(~Sg.Seen, ~Staging.sp_w_seen, xs, r) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, Sg.Seen, xs)), Staging.sp_fit_seens.all(xs)) == True{} : Bool}):
    +a1 = Equal.cong(String, String, z => Wr.put_nat(1n+m, z), s2, PA.se.seens_items(xs, r), e1)
    +a2 = Equal.cong(Nat, String, n => Wr.put_nat(n, PA.se.seens_items(xs, r)), 1n+m, List.length(&2, Sg.Seen, xs), Equal.sym(Nat, List.length(&2, Sg.Seen, xs), 1n+m, e2))
    +a3 = Equal.sym(String, Wr.put_list(~Sg.Seen, ~Staging.sp_w_seen, xs, r), Wr.put_nat(List.length(&2, Sg.Seen, xs), PA.se.seens_items(xs, r)), PA.se.seens_put(xs, r))
    (Equal.trans(String, s, Wr.put_nat(1n+m, s2), Wr.put_list(~Sg.Seen, ~Staging.sp_w_seen, xs, r), en,
      Equal.trans(String, Wr.put_nat(1n+m, s2), Wr.put_nat(1n+m, PA.se.seens_items(xs, r)), Wr.put_list(~Sg.Seen, ~Staging.sp_w_seen, xs, r), a1,
        Equal.trans(String, Wr.put_nat(1n+m, PA.se.seens_items(xs, r)), Wr.put_nat(List.length(&2, Sg.Seen, xs), PA.se.seens_items(xs, r)), Wr.put_list(~Sg.Seen, ~Staging.sp_w_seen, xs, r), a2, a3))),
     ex.and_tt(LawsBase.wire_fits(List.length(&2, Sg.Seen, xs)), Staging.sp_fit_seens.all(xs), Equal.trans(Bool, LawsBase.wire_fits(List.length(&2, Sg.Seen, xs)), LawsBase.wire_fits(1n+m), True{}, Equal.cong(Nat, Bool, n => LawsBase.wire_fits(n), List.length(&2, Sg.Seen, xs), 1n+m, e2), fm), fa))

def ex.seens_conv(-s: String, +s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fm: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  d: Wr.Dec<List<&2, Sg.Seen>>, pl: ex.seens_PL(s2, m, d)) -> ex.seens_TP(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (h, fa) = pl
      (e1, e2) = h
      ex.seens_conv2(s, s2, m, xs, r, en, fm, e1, e2, fa)
    case Wr.Bad{}:
      Unit{}

def ex.seens_nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> ex.seens_TP(s, Wr.get_list.start(~Sg.Seen, ~FSg.get_seen, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      ex.seens_conv(s, s2, m, en, fn, Wr.get_list.go(~Sg.Seen, ~FSg.get_seen, m, FSg.get_seen(s2)), ex.seens_loop(m, FSg.get_seen(s2), s2, ex.seen(s2)))

def ex.seens_top(-s: String, d: Wr.Dec<Nat>, np: ex.NP(s, d)) -> ex.seens_TP(s, Wr.get_list.start(~Sg.Seen, ~FSg.get_seen, d)):
  match d:
    case Wr.Got{+n, +s2}:
      (e, f) = np
      ex.seens_nat(s, n, s2, e, f)
    case Wr.Bad{}:
      Unit{}

def ex.seens(+s: String) -> ex.seens_TP(s, Wr.get_list(~Sg.Seen, ~FSg.get_seen, s)):
  ex.seens_top(s, Wr.get_nat(s), ex.nat(s))

# Lists of times
# ------------

def ex.times_PL(s: String, m: Nat, d: Wr.Dec<List<&2, Sg.Time>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      ({s == PA.se.times_items(xs, r) : String} & {List.length(&2, Sg.Time, xs) == 1n+m : Nat}) & {Staging.sp_fit_times.all(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ex.times_step(-s: String, +x: Sg.Time, +s3: String, -k: Nat, ex1: {s == Staging.sp_w_time(x, s3) : String}, fx: {Staging.sp_fit_time(x) == True{} : Bool},
  d: Wr.Dec<List<&2, Sg.Time>>, ih: ex.times_PL(s3, k, d)) -> ex.times_PL(s, 1n+k, Wr.get_list.cons(Sg.Time, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (h, fa) = ih
      (e1, e2) = h
      ((Equal.trans(String, s, Staging.sp_w_time(x, s3), Staging.sp_w_time(x, PA.se.times_items(ys, r)), ex1,
          Equal.cong(String, String, z => Staging.sp_w_time(x, z), s3, PA.se.times_items(ys, r), e1)),
        Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Sg.Time, ys), 1n+k, e2)),
        ex.and_tt(Staging.sp_fit_time(x), Staging.sp_fit_times.all(ys), fx, fa))
    case Wr.Bad{}:
      Unit{}

def ex.times_loop(m: Nat, cur: Wr.Dec<Sg.Time>, +s: String, xp: ex.TP(s, cur)) -> ex.times_PL(s, m, Wr.get_list.go(~Sg.Time, ~FSg.get_time, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = xp
      ((e, {==}), ex.and_tt(Staging.sp_fit_time(x), True{}, f, {==}))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = xp
      ex.times_step(s, x, s3, k, e, f, Wr.get_list.go(~Sg.Time, ~FSg.get_time, k, FSg.get_time(s3)), ex.times_loop(k, FSg.get_time(s3), s3, ex.time(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def ex.times_TP(s: String, d: Wr.Dec<List<&2, Sg.Time>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_list(~Sg.Time, ~Staging.sp_w_time, xs, r) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, Sg.Time, xs)), Staging.sp_fit_times.all(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ex.times_conv2(-s: String, +s2: String, +m: Nat, +xs: List<&2, Sg.Time>, +r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, fm: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  e1: {s2 == PA.se.times_items(xs, r) : String}, +e2: {List.length(&2, Sg.Time, xs) == 1n+m : Nat}, fa: {Staging.sp_fit_times.all(xs) == True{} : Bool}) ->
  ({s == Wr.put_list(~Sg.Time, ~Staging.sp_w_time, xs, r) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, Sg.Time, xs)), Staging.sp_fit_times.all(xs)) == True{} : Bool}):
    +a1 = Equal.cong(String, String, z => Wr.put_nat(1n+m, z), s2, PA.se.times_items(xs, r), e1)
    +a2 = Equal.cong(Nat, String, n => Wr.put_nat(n, PA.se.times_items(xs, r)), 1n+m, List.length(&2, Sg.Time, xs), Equal.sym(Nat, List.length(&2, Sg.Time, xs), 1n+m, e2))
    +a3 = Equal.sym(String, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, xs, r), Wr.put_nat(List.length(&2, Sg.Time, xs), PA.se.times_items(xs, r)), PA.se.times_put(xs, r))
    (Equal.trans(String, s, Wr.put_nat(1n+m, s2), Wr.put_list(~Sg.Time, ~Staging.sp_w_time, xs, r), en,
      Equal.trans(String, Wr.put_nat(1n+m, s2), Wr.put_nat(1n+m, PA.se.times_items(xs, r)), Wr.put_list(~Sg.Time, ~Staging.sp_w_time, xs, r), a1,
        Equal.trans(String, Wr.put_nat(1n+m, PA.se.times_items(xs, r)), Wr.put_nat(List.length(&2, Sg.Time, xs), PA.se.times_items(xs, r)), Wr.put_list(~Sg.Time, ~Staging.sp_w_time, xs, r), a2, a3))),
     ex.and_tt(LawsBase.wire_fits(List.length(&2, Sg.Time, xs)), Staging.sp_fit_times.all(xs), Equal.trans(Bool, LawsBase.wire_fits(List.length(&2, Sg.Time, xs)), LawsBase.wire_fits(1n+m), True{}, Equal.cong(Nat, Bool, n => LawsBase.wire_fits(n), List.length(&2, Sg.Time, xs), 1n+m, e2), fm), fa))

def ex.times_conv(-s: String, +s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fm: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  d: Wr.Dec<List<&2, Sg.Time>>, pl: ex.times_PL(s2, m, d)) -> ex.times_TP(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (h, fa) = pl
      (e1, e2) = h
      ex.times_conv2(s, s2, m, xs, r, en, fm, e1, e2, fa)
    case Wr.Bad{}:
      Unit{}

def ex.times_nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> ex.times_TP(s, Wr.get_list.start(~Sg.Time, ~FSg.get_time, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      ex.times_conv(s, s2, m, en, fn, Wr.get_list.go(~Sg.Time, ~FSg.get_time, m, FSg.get_time(s2)), ex.times_loop(m, FSg.get_time(s2), s2, ex.time(s2)))

def ex.times_top(-s: String, d: Wr.Dec<Nat>, np: ex.NP(s, d)) -> ex.times_TP(s, Wr.get_list.start(~Sg.Time, ~FSg.get_time, d)):
  match d:
    case Wr.Got{+n, +s2}:
      (e, f) = np
      ex.times_nat(s, n, s2, e, f)
    case Wr.Bad{}:
      Unit{}

def ex.times(+s: String) -> ex.times_TP(s, Wr.get_list(~Sg.Time, ~FSg.get_time, s)):
  ex.times_top(s, Wr.get_nat(s), ex.nat(s))

# Obs
# ---

def ex.ObP(s: String, d: Wr.Dec<Ls.Obs>) -> Type:
  match d:
    case Wr.Got{o, r}:
      {s == Staging.sp_w_obs(o, r) : String} & {Staging.sp_fit_obs(o) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ex.obs.times(-s: String, +e: Sg.Seen, +c: Maybe<&2, String>, -s2: String, pre: {s == Staging.sp_w_seen(e, Staging.sp_w_cwd(c, s2)) : String}, fe: {Staging.sp_fit_seen(e) == True{} : Bool}, fc: {Staging.sp_fit_cwd(c) == True{} : Bool},
  d: Wr.Dec<List<&2, Sg.Time>>, tp: ex.times_TP(s2, d)) -> ex.ObP(s, FSg.get_obs.times(e, c, d)):
  match d:
    case Wr.Got{+ts, +r}:
      (et, ft) = tp
      (Equal.trans(String, s, Staging.sp_w_seen(e, Staging.sp_w_cwd(c, s2)), Staging.sp_w_seen(e, Staging.sp_w_cwd(c, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, ts, r))), pre,
          Equal.cong(String, String, z => Staging.sp_w_seen(e, Staging.sp_w_cwd(c, z)), s2, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, ts, r), et)),
        ex.and_tt(Staging.sp_fit_seen(e), Bool.and(Staging.sp_fit_cwd(c), Staging.sp_fit_times(ts)), fe, ex.and_tt(Staging.sp_fit_cwd(c), Staging.sp_fit_times(ts), fc, ft)))
    case Wr.Bad{}:
      Unit{}

def ex.obs.cwd(-s: String, +e: Sg.Seen, -s1: String, pre: {s == Staging.sp_w_seen(e, s1) : String}, fe: {Staging.sp_fit_seen(e) == True{} : Bool}, d: Wr.Dec<Maybe<&2, String>>, cp: ex.CP(s1, d)) -> ex.ObP(s, FSg.get_obs.cwd(e, d)):
  match d:
    case Wr.Got{+c, +s2}:
      (ec, fc) = cp
      ex.obs.times(s, e, c, s2, Equal.trans(String, s, Staging.sp_w_seen(e, s1), Staging.sp_w_seen(e, Staging.sp_w_cwd(c, s2)), pre, Equal.cong(String, String, z => Staging.sp_w_seen(e, z), s1, Staging.sp_w_cwd(c, s2), ec)), fe, fc,
        Wr.get_list(~Sg.Time, ~FSg.get_time, s2), ex.times(s2))
    case Wr.Bad{}:
      Unit{}

def ex.obs.go(-s: String, d: Wr.Dec<Sg.Seen>, sp: ex.SeP(s, d)) -> ex.ObP(s, FSg.get_obs.go(d)):
  match d:
    case Wr.Got{+e, +s1}:
      (ee, fe) = sp
      ex.obs.cwd(s, e, s1, ee, fe, FSg.get_cwd(s1), ex.cwd(s1))
    case Wr.Bad{}:
      Unit{}

def ex.obs(+s: String) -> ex.ObP(s, FSg.get_obs(s)):
  ex.obs.go(s, FSg.get_seen(s), ex.seen(s))

# Lists of obss
# ------------

def ex.obss_PL(s: String, m: Nat, d: Wr.Dec<List<&2, Ls.Obs>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      ({s == PA.se.obss_items(xs, r) : String} & {List.length(&2, Ls.Obs, xs) == 1n+m : Nat}) & {Staging.sp_fit_obss.all(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ex.obss_step(-s: String, +x: Ls.Obs, +s3: String, -k: Nat, ex1: {s == Staging.sp_w_obs(x, s3) : String}, fx: {Staging.sp_fit_obs(x) == True{} : Bool},
  d: Wr.Dec<List<&2, Ls.Obs>>, ih: ex.obss_PL(s3, k, d)) -> ex.obss_PL(s, 1n+k, Wr.get_list.cons(Ls.Obs, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (h, fa) = ih
      (e1, e2) = h
      ((Equal.trans(String, s, Staging.sp_w_obs(x, s3), Staging.sp_w_obs(x, PA.se.obss_items(ys, r)), ex1,
          Equal.cong(String, String, z => Staging.sp_w_obs(x, z), s3, PA.se.obss_items(ys, r), e1)),
        Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Ls.Obs, ys), 1n+k, e2)),
        ex.and_tt(Staging.sp_fit_obs(x), Staging.sp_fit_obss.all(ys), fx, fa))
    case Wr.Bad{}:
      Unit{}

def ex.obss_loop(m: Nat, cur: Wr.Dec<Ls.Obs>, +s: String, xp: ex.ObP(s, cur)) -> ex.obss_PL(s, m, Wr.get_list.go(~Ls.Obs, ~FSg.get_obs, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = xp
      ((e, {==}), ex.and_tt(Staging.sp_fit_obs(x), True{}, f, {==}))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = xp
      ex.obss_step(s, x, s3, k, e, f, Wr.get_list.go(~Ls.Obs, ~FSg.get_obs, k, FSg.get_obs(s3)), ex.obss_loop(k, FSg.get_obs(s3), s3, ex.obs(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def ex.obss_TP(s: String, d: Wr.Dec<List<&2, Ls.Obs>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_list(~Ls.Obs, ~Staging.sp_w_obs, xs, r) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, Ls.Obs, xs)), Staging.sp_fit_obss.all(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ex.obss_conv2(-s: String, +s2: String, +m: Nat, +xs: List<&2, Ls.Obs>, +r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, fm: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  e1: {s2 == PA.se.obss_items(xs, r) : String}, +e2: {List.length(&2, Ls.Obs, xs) == 1n+m : Nat}, fa: {Staging.sp_fit_obss.all(xs) == True{} : Bool}) ->
  ({s == Wr.put_list(~Ls.Obs, ~Staging.sp_w_obs, xs, r) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, Ls.Obs, xs)), Staging.sp_fit_obss.all(xs)) == True{} : Bool}):
    +a1 = Equal.cong(String, String, z => Wr.put_nat(1n+m, z), s2, PA.se.obss_items(xs, r), e1)
    +a2 = Equal.cong(Nat, String, n => Wr.put_nat(n, PA.se.obss_items(xs, r)), 1n+m, List.length(&2, Ls.Obs, xs), Equal.sym(Nat, List.length(&2, Ls.Obs, xs), 1n+m, e2))
    +a3 = Equal.sym(String, Wr.put_list(~Ls.Obs, ~Staging.sp_w_obs, xs, r), Wr.put_nat(List.length(&2, Ls.Obs, xs), PA.se.obss_items(xs, r)), PA.se.obss_put(xs, r))
    (Equal.trans(String, s, Wr.put_nat(1n+m, s2), Wr.put_list(~Ls.Obs, ~Staging.sp_w_obs, xs, r), en,
      Equal.trans(String, Wr.put_nat(1n+m, s2), Wr.put_nat(1n+m, PA.se.obss_items(xs, r)), Wr.put_list(~Ls.Obs, ~Staging.sp_w_obs, xs, r), a1,
        Equal.trans(String, Wr.put_nat(1n+m, PA.se.obss_items(xs, r)), Wr.put_nat(List.length(&2, Ls.Obs, xs), PA.se.obss_items(xs, r)), Wr.put_list(~Ls.Obs, ~Staging.sp_w_obs, xs, r), a2, a3))),
     ex.and_tt(LawsBase.wire_fits(List.length(&2, Ls.Obs, xs)), Staging.sp_fit_obss.all(xs), Equal.trans(Bool, LawsBase.wire_fits(List.length(&2, Ls.Obs, xs)), LawsBase.wire_fits(1n+m), True{}, Equal.cong(Nat, Bool, n => LawsBase.wire_fits(n), List.length(&2, Ls.Obs, xs), 1n+m, e2), fm), fa))

def ex.obss_conv(-s: String, +s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fm: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  d: Wr.Dec<List<&2, Ls.Obs>>, pl: ex.obss_PL(s2, m, d)) -> ex.obss_TP(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (h, fa) = pl
      (e1, e2) = h
      ex.obss_conv2(s, s2, m, xs, r, en, fm, e1, e2, fa)
    case Wr.Bad{}:
      Unit{}

def ex.obss_nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> ex.obss_TP(s, Wr.get_list.start(~Ls.Obs, ~FSg.get_obs, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      ex.obss_conv(s, s2, m, en, fn, Wr.get_list.go(~Ls.Obs, ~FSg.get_obs, m, FSg.get_obs(s2)), ex.obss_loop(m, FSg.get_obs(s2), s2, ex.obs(s2)))

def ex.obss_top(-s: String, d: Wr.Dec<Nat>, np: ex.NP(s, d)) -> ex.obss_TP(s, Wr.get_list.start(~Ls.Obs, ~FSg.get_obs, d)):
  match d:
    case Wr.Got{+n, +s2}:
      (e, f) = np
      ex.obss_nat(s, n, s2, e, f)
    case Wr.Bad{}:
      Unit{}

def ex.obss(+s: String) -> ex.obss_TP(s, Wr.get_list(~Ls.Obs, ~FSg.get_obs, s)):
  ex.obss_top(s, Wr.get_nat(s), ex.nat(s))

# The request
# -----------

def ex.RP(s: String, d: Wr.Dec<FSg.Req>) -> Type:
  match d:
    case Wr.Got{r, rest}:
      {s == Staging.sp_w_req(r, rest) : String} & {Staging.sp_fit_req(r) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ex.publish(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Bool>, bp: ex.BP(s1, d)) -> ex.RP(s, FSg.get_publish(d)):
  match d:
    case Wr.Got{+b, +r}:
      (ex.after(s, 0n, s1, Wr.put_bool(b, r), pre, bp), {==})
    case Wr.Bad{}:
      Unit{}

def ex.meet(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<List<&2, Sg.Seen>>, lp: ex.seens_TP(s1, d)) -> ex.RP(s, FSg.get_meet(d)):
  match d:
    case Wr.Got{+es, +r}:
      (e, f) = lp
      (ex.after(s, 1n, s1, Wr.put_list(~Sg.Seen, ~Staging.sp_w_seen, es, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def ex.scan(-s: String, -s1: String, pre: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<List<&2, Sg.Seen>>, lp: ex.seens_TP(s1, d)) -> ex.RP(s, FSg.get_scan(d)):
  match d:
    case Wr.Got{+es, +r}:
      (e, f) = lp
      (ex.after(s, 3n, s1, Wr.put_list(~Sg.Seen, ~Staging.sp_w_seen, es, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def ex.rows(-s: String, -s1: String, pre: {s == Wr.put_nat(4n, s1) : String}, d: Wr.Dec<List<&2, Ls.Obs>>, lp: ex.obss_TP(s1, d)) -> ex.RP(s, FSg.get_rows(d)):
  match d:
    case Wr.Got{+os, +r}:
      (e, f) = lp
      (ex.after(s, 4n, s1, Wr.put_list(~Ls.Obs, ~Staging.sp_w_obs, os, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def ex.judge.inner(-s: String, +c: Sg.Cand, +l: Sg.Lock, +now: Sg.Time, +own: Sg.Time, -s5: String,
  pre: {s == Wr.put_nat(2n, Staging.sp_w_cand(c, Staging.sp_w_lock(l, Staging.sp_w_time(now, Staging.sp_w_time(own, s5))))) : String},
  fnow: {Staging.sp_fit_time(now) == True{} : Bool}, fown: {Staging.sp_fit_time(own) == True{} : Bool},
  d: Wr.Dec<List<&2, Sg.Time>>, lp: ex.times_TP(s5, d)) -> ex.RP(s, FSg.get_judge.inner(c, l, now, own, d)):
  match d:
    case Wr.Got{+ts, +r}:
      (e, f) = lp
      (Equal.trans(String, s, Wr.put_nat(2n, Staging.sp_w_cand(c, Staging.sp_w_lock(l, Staging.sp_w_time(now, Staging.sp_w_time(own, s5))))), Staging.sp_w_req(FSg.Judge{c, l, now, own, ts}, r), pre,
          Equal.cong(String, String, z => Wr.put_nat(2n, Staging.sp_w_cand(c, Staging.sp_w_lock(l, Staging.sp_w_time(now, Staging.sp_w_time(own, z))))), s5, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, ts, r), e)),
        ex.and_tt(Staging.sp_fit_time(now), Bool.and(Staging.sp_fit_time(own), Staging.sp_fit_times(ts)), fnow, ex.and_tt(Staging.sp_fit_time(own), Staging.sp_fit_times(ts), fown, f)))
    case Wr.Bad{}:
      Unit{}

def ex.judge.own(-s: String, +c: Sg.Cand, +l: Sg.Lock, +now: Sg.Time, -s4: String,
  pre: {s == Wr.put_nat(2n, Staging.sp_w_cand(c, Staging.sp_w_lock(l, Staging.sp_w_time(now, s4)))) : String},
  fnow: {Staging.sp_fit_time(now) == True{} : Bool}, d: Wr.Dec<Sg.Time>, tp: ex.TP(s4, d)) -> ex.RP(s, FSg.get_judge.own(c, l, now, d)):
  match d:
    case Wr.Got{+own, +s5}:
      (e, f) = tp
      ex.judge.inner(s, c, l, now, own, s5,
        Equal.trans(String, s, Wr.put_nat(2n, Staging.sp_w_cand(c, Staging.sp_w_lock(l, Staging.sp_w_time(now, s4)))), Wr.put_nat(2n, Staging.sp_w_cand(c, Staging.sp_w_lock(l, Staging.sp_w_time(now, Staging.sp_w_time(own, s5))))), pre,
          Equal.cong(String, String, z => Wr.put_nat(2n, Staging.sp_w_cand(c, Staging.sp_w_lock(l, Staging.sp_w_time(now, z)))), s4, Staging.sp_w_time(own, s5), e)),
        fnow, f, Wr.get_list(~Sg.Time, ~FSg.get_time, s5), ex.times(s5))
    case Wr.Bad{}:
      Unit{}

def ex.judge.now(-s: String, +c: Sg.Cand, +l: Sg.Lock, -s3: String,
  pre: {s == Wr.put_nat(2n, Staging.sp_w_cand(c, Staging.sp_w_lock(l, s3))) : String},
  d: Wr.Dec<Sg.Time>, tp: ex.TP(s3, d)) -> ex.RP(s, FSg.get_judge.now(c, l, d)):
  match d:
    case Wr.Got{+now, +s4}:
      (e, f) = tp
      ex.judge.own(s, c, l, now, s4,
        Equal.trans(String, s, Wr.put_nat(2n, Staging.sp_w_cand(c, Staging.sp_w_lock(l, s3))), Wr.put_nat(2n, Staging.sp_w_cand(c, Staging.sp_w_lock(l, Staging.sp_w_time(now, s4)))), pre,
          Equal.cong(String, String, z => Wr.put_nat(2n, Staging.sp_w_cand(c, Staging.sp_w_lock(l, z))), s3, Staging.sp_w_time(now, s4), e)),
        f, FSg.get_time(s4), ex.time(s4))
    case Wr.Bad{}:
      Unit{}

def ex.judge.lock(-s: String, +c: Sg.Cand, -s2: String,
  pre: {s == Wr.put_nat(2n, Staging.sp_w_cand(c, s2)) : String},
  d: Wr.Dec<Sg.Lock>, lp: ex.LkP(s2, d)) -> ex.RP(s, FSg.get_judge.lock(c, d)):
  match d:
    case Wr.Got{+l, +s3}:
      ex.judge.now(s, c, l, s3,
        Equal.trans(String, s, Wr.put_nat(2n, Staging.sp_w_cand(c, s2)), Wr.put_nat(2n, Staging.sp_w_cand(c, Staging.sp_w_lock(l, s3))), pre,
          Equal.cong(String, String, z => Wr.put_nat(2n, Staging.sp_w_cand(c, z)), s2, Staging.sp_w_lock(l, s3), lp)),
        FSg.get_time(s3), ex.time(s3))
    case Wr.Bad{}:
      Unit{}

def ex.judge(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Sg.Cand>, cp: ex.CaP(s1, d)) -> ex.RP(s, FSg.get_judge(d)):
  match d:
    case Wr.Got{+c, +s2}:
      ex.judge.lock(s, c, s2, ex.after(s, 2n, s1, Staging.sp_w_cand(c, s2), pre, cp), FSg.get_lock.go(Wr.get_nat(s2)), ex.lock(s2, Wr.get_nat(s2), ex.nat(s2)))
    case Wr.Bad{}:
      Unit{}

def ex.req.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> ex.RP(s, FSg.get_req.tag(t, s1)):
  match t:
    case 0n:
      ex.publish(s, s1, pre, Wr.get_bool(s1), ex.bool(s1))
    case 1n+a:
      match a:
        case 0n:
          ex.meet(s, s1, pre, Wr.get_list(~Sg.Seen, ~FSg.get_seen, s1), ex.seens(s1))
        case 1n+b:
          match b:
            case 0n:
              ex.judge(s, s1, pre, FSg.get_cand.go(Wr.get_nat(s1)), ex.cand(s1, Wr.get_nat(s1), ex.nat(s1)))
            case 1n+c:
              match c:
                case 0n:
                  ex.scan(s, s1, pre, Wr.get_list(~Sg.Seen, ~FSg.get_seen, s1), ex.seens(s1))
                case 1n+e:
                  match e:
                    case 0n:
                      ex.rows(s, s1, pre, Wr.get_list(~Ls.Obs, ~FSg.get_obs, s1), ex.obss(s1))
                    case 1n+f:
                      Unit{}

def ex.req.go(-s: String, d: Wr.Dec<Nat>, np: ex.NP(s, d)) -> ex.RP(s, FSg.get_req.go(d)):
  match d:
    case Wr.Got{t, s1}:
      (e, f) = np
      ex.req.tag(t, s1, s, e)
    case Wr.Bad{}:
      Unit{}

def ex.req(+s: String) -> ex.RP(s, FSg.get_req(s)):
  ex.req.go(s, Wr.get_nat(s), ex.nat(s))

# a value answered: a request read whole, nothing left
def ex.top(-s: String, d: Wr.Dec<FSg.Req>, rp: ex.RP(s, d), ok: {LawsBase.wire_opens_err(FSg.answer(d)) == False{} : Bool}) -> Sigma<&1, &1, FSg.Req, r => {s == Staging.sp_w_req(r, "") : String} & {Staging.sp_fit_req(r) == True{} : Bool}>:
  match d:
    case Wr.Got{+r, rest}:
      match rest:
        case SNil{}:
          (r, rp)
        case SCon{x, y}:
          ex.tf(Sigma<&1, &1, FSg.Req, r2 => {s == Staging.sp_w_req(r2, "") : String} & {Staging.sp_fit_req(r2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      ex.tf(Sigma<&1, &1, FSg.Req, r2 => {s == Staging.sp_w_req(r2, "") : String} & {Staging.sp_fit_req(r2) == True{} : Bool}>, ok)

def Staging.staging_entry_exact(s, ok):
  ex.top(s, FSg.get_req(s), ex.req(s), ok)
