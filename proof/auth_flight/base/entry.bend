# eukhe: lemmas the proofs of the auth_flight entry share
# The entry (bend/ffi_auth_flight.bend) reads back every event spelled as
# the laws spell it (ae.get), reads nothing else (ae.spelled), spells
# every reply as the laws' speller does (ae.out), and its desk
# (F.desk.step) is the proofs' restated desk (D.af_desk, ae.desk).

import Base
import ../../../bend/auth_flight.bend as F
import ../../../bend/ffi_auth_flight.bend as FA
import ../../../bend/wire.bend as Wr
import ../../../laws/auth_flight/entry.bend as AuthFlightEntry
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_str_exact.bend as PWireStrExact
import ../../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ../../base/wire.bend as LWire
import ./desk.bend as D

# Maybe
# -----

def ae.MD(-A: Data, m: Maybe<&2, A>, n: Type, s: Type) -> Type:
  match m:
    case None{}:
      n
    case Some{x}:
      s

# a None that is a Some proves anything
def ae.none_some(-A: Data, -G: Type, -x: A, e: {None{} == Some{x} : Maybe<&2, A>}) -> G:
  %e : ae.MD(A, _, Unit, G)
  Unit{}

# The reader
# ----------

# what a found is on the wire reads back as that found, the rest untouched
def ae.what_back(+k: Nat, fd: F.Fd, +r: String) -> {FA.get_ev.what(k, AuthFlightEntry.af_what(fd), r) == Wr.Got{F.Found{k, fd}, r} : Wr.Dec<F.DEv>}:
  match fd:
    case F.LoadFresh{}:
      {==}
    case F.LoadExpired{}:
      {==}
    case F.LoadFailed{}:
      {==}
    case F.CheckFresh{}:
      {==}
    case F.CheckExpired{}:
      {==}
    case F.FetchOk{}:
      {==}
    case F.FetchFailed{}:
      {==}
    case F.Stored{}:
      {==}

# what a found is on the wire fits it
def ae.what_fits(fd: F.Fd) -> {LawsBase.wire_fits(AuthFlightEntry.af_what(fd)) == True{} : Bool}:
  match fd:
    case F.LoadFresh{}:
      {==}
    case F.LoadExpired{}:
      {==}
    case F.LoadFailed{}:
      {==}
    case F.CheckFresh{}:
      {==}
    case F.CheckExpired{}:
      {==}
    case F.FetchOk{}:
      {==}
    case F.FetchFailed{}:
      {==}
    case F.Stored{}:
      {==}

# every event Rust writes (within the wire) reads back, the rest untouched
def ae.get(e: F.DEv, +r: String, +fits: {AuthFlightEntry.af_ev_fits(e) == True{} : Bool}) -> {FA.get_ev(Wr.get_nat(AuthFlightEntry.af_spell_ev(e, r))) == Wr.Got{e, r} : Wr.Dec<F.DEv>}:
  match e:
    case F.Comes{+p}:
      %LWire.pw6.nat(0n, Wr.put_str(p, r), {==}) : {FA.get_ev(_) == Wr.Got{F.Comes{p}, r} : Wr.Dec<F.DEv>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(p, r)), Wr.Got{p, r}, Wire.wire_str_round_trip(p, r, fits)) : {FA.get_ev.comes(_) == Wr.Got{F.Comes{p}, r} : Wr.Dec<F.DEv>}
      {==}
    case F.Found{+k, +fd}:
      %LWire.pw6.nat(1n, Wr.put_nat(k, Wr.put_nat(AuthFlightEntry.af_what(fd), r)), {==}) : {FA.get_ev(_) == Wr.Got{F.Found{k, fd}, r} : Wr.Dec<F.DEv>}
      %LWire.pw6.nat(k, Wr.put_nat(AuthFlightEntry.af_what(fd), r), fits) : {FA.get_ev.caller(_) == Wr.Got{F.Found{k, fd}, r} : Wr.Dec<F.DEv>}
      %LWire.pw6.nat(AuthFlightEntry.af_what(fd), r, ae.what_fits(fd)) : {FA.get_ev.found(k, _) == Wr.Got{F.Found{k, fd}, r} : Wr.Dec<F.DEv>}
      ae.what_back(k, fd, r)
    case F.Unwinds{+k}:
      %LWire.pw6.nat(2n, Wr.put_nat(k, r), {==}) : {FA.get_ev(_) == Wr.Got{F.Unwinds{k}, r} : Wr.Dec<F.DEv>}
      %LWire.pw6.nat(k, r, fits) : {FA.get_ev.unwind(_) == Wr.Got{F.Unwinds{k}, r} : Wr.Dec<F.DEv>}
      {==}
    case F.Joiners{+p}:
      %LWire.pw6.nat(3n, Wr.put_str(p, r), {==}) : {FA.get_ev(_) == Wr.Got{F.Joiners{p}, r} : Wr.Dec<F.DEv>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(p, r)), Wr.Got{p, r}, Wire.wire_str_round_trip(p, r, fits)) : {FA.get_ev.joiners(_) == Wr.Got{F.Joiners{p}, r} : Wr.Dec<F.DEv>}
      {==}

# What the decoder read was spelled: the input is the event read, spelled
# as the laws spell it, then the rest read after it, and the event fits
def ae.Spelled(s: String, r: Wr.Dec<F.DEv>) -> Type:
  match r:
    case Wr.Got{e, t}:
      ({s == AuthFlightEntry.af_spell_ev(e, t) : String} & {AuthFlightEntry.af_ev_fits(e) == True{} : Bool})
    case Wr.Bad{}:
      Unit

# s is a tag, a Nat, a Nat, then rest: chained
def ae.chain(-s: String, -s1: String, -s2: String, +t: Nat, +k: Nat, +w: Nat, +s3: String, h: {s == Wr.put_nat(t, s1) : String}, h2: {s1 == Wr.put_nat(k, s2) : String}, h3: {s2 == Wr.put_nat(w, s3) : String}) -> {s == Wr.put_nat(t, Wr.put_nat(k, Wr.put_nat(w, s3))) : String}:
  %h3 : {s == Wr.put_nat(t, Wr.put_nat(k, _)) : String}
  %h2 : {s == Wr.put_nat(t, _) : String}
  h

# s is a tag, a Nat, then rest: chained
def ae.chain2(-s: String, -s1: String, +t: Nat, +k: Nat, +s2: String, h: {s == Wr.put_nat(t, s1) : String}, h2: {s1 == Wr.put_nat(k, s2) : String}) -> {s == Wr.put_nat(t, Wr.put_nat(k, s2)) : String}:
  %h2 : {s == Wr.put_nat(t, _) : String}
  h

# s is a tag, a string, then rest: chained
def ae.chain_str(-s: String, -s1: String, +t: Nat, +p: String, +s2: String, h: {s == Wr.put_nat(t, s1) : String}, h2: {s1 == Wr.put_str(p, s2) : String}) -> {s == Wr.put_nat(t, Wr.put_str(p, s2)) : String}:
  %h2 : {s == Wr.put_nat(t, _) : String}
  h

def ae.sp_what(-s: String, -s1: String, -s2: String, +k: Nat, w: Nat, +s3: String, h: {s == Wr.put_nat(1n, s1) : String}, h2: {s1 == Wr.put_nat(k, s2) : String}, h3: {s2 == Wr.put_nat(w, s3) : String}, +fk: {LawsBase.wire_fits(k) == True{} : Bool}) -> ae.Spelled(s, FA.get_ev.what(k, w, s3)):
  match w:
    case 0n:
      (ae.chain(s, s1, s2, 1n, k, 0n, s3, h, h2, h3), fk)
    case 1n:
      (ae.chain(s, s1, s2, 1n, k, 1n, s3, h, h2, h3), fk)
    case 2n:
      (ae.chain(s, s1, s2, 1n, k, 2n, s3, h, h2, h3), fk)
    case 3n:
      (ae.chain(s, s1, s2, 1n, k, 3n, s3, h, h2, h3), fk)
    case 4n:
      (ae.chain(s, s1, s2, 1n, k, 4n, s3, h, h2, h3), fk)
    case 5n:
      (ae.chain(s, s1, s2, 1n, k, 5n, s3, h, h2, h3), fk)
    case 6n:
      (ae.chain(s, s1, s2, 1n, k, 6n, s3, h, h2, h3), fk)
    case 7n:
      (ae.chain(s, s1, s2, 1n, k, 7n, s3, h, h2, h3), fk)
    case 8n+q:
      Unit{}

def ae.sp_found(-s: String, -s1: String, +s2: String, +k: Nat, r: Wr.Dec<Nat>, +e: {Wr.get_nat(s2) == r : Wr.Dec<Nat>}, h: {s == Wr.put_nat(1n, s1) : String}, h2: {s1 == Wr.put_nat(k, s2) : String}, +fk: {LawsBase.wire_fits(k) == True{} : Bool}) -> ae.Spelled(s, FA.get_ev.found(k, r)):
  match r:
    case Wr.Got{+w, +s3}:
      ae.sp_what(s, s1, s2, k, w, s3, h, h2, Wire.wire_nat_exact(s2, w, s3, e), fk)
    case Wr.Bad{}:
      Unit{}

def ae.sp_caller(-s: String, +s1: String, r: Wr.Dec<Nat>, +e: {Wr.get_nat(s1) == r : Wr.Dec<Nat>}, h: {s == Wr.put_nat(1n, s1) : String}) -> ae.Spelled(s, FA.get_ev.caller(r)):
  match r:
    case Wr.Got{+k, +s2}:
      ae.sp_found(s, s1, s2, k, Wr.get_nat(s2), {==}, h, Wire.wire_nat_exact(s1, k, s2, e), Wire.wire_nat_decoded_fits(s1, k, s2, e))
    case Wr.Bad{}:
      Unit{}

def ae.sp_unwind(-s: String, +s1: String, r: Wr.Dec<Nat>, +e: {Wr.get_nat(s1) == r : Wr.Dec<Nat>}, h: {s == Wr.put_nat(2n, s1) : String}) -> ae.Spelled(s, FA.get_ev.unwind(r)):
  match r:
    case Wr.Got{+k, +s2}:
      (ae.chain2(s, s1, 2n, k, s2, h, Wire.wire_nat_exact(s1, k, s2, e)), Wire.wire_nat_decoded_fits(s1, k, s2, e))
    case Wr.Bad{}:
      Unit{}

def ae.sp_comes(-s: String, +s1: String, r: Wr.Dec<String>, +e: {Wr.get_str(s1) == r : Wr.Dec<String>}, h: {s == Wr.put_nat(0n, s1) : String}) -> ae.Spelled(s, FA.get_ev.comes(r)):
  match r:
    case Wr.Got{+p, +s2}:
      (ae.chain_str(s, s1, 0n, p, s2, h, Wire.wire_str_exact(s1, p, s2, e)), Wire.wire_str_decoded_fits(s1, p, s2, e))
    case Wr.Bad{}:
      Unit{}

def ae.sp_joiners(-s: String, +s1: String, r: Wr.Dec<String>, +e: {Wr.get_str(s1) == r : Wr.Dec<String>}, h: {s == Wr.put_nat(3n, s1) : String}) -> ae.Spelled(s, FA.get_ev.joiners(r)):
  match r:
    case Wr.Got{+p, +s2}:
      (ae.chain_str(s, s1, 3n, p, s2, h, Wire.wire_str_exact(s1, p, s2, e)), Wire.wire_str_decoded_fits(s1, p, s2, e))
    case Wr.Bad{}:
      Unit{}

def ae.sp_tag(-s: String, t: Nat, +s1: String, h: {s == Wr.put_nat(t, s1) : String}) -> ae.Spelled(s, FA.get_ev.tag(t, s1)):
  match t:
    case 0n:
      ae.sp_comes(s, s1, Wr.get_str(s1), {==}, h)
    case 1n:
      ae.sp_caller(s, s1, Wr.get_nat(s1), {==}, h)
    case 2n:
      ae.sp_unwind(s, s1, Wr.get_nat(s1), {==}, h)
    case 3n:
      ae.sp_joiners(s, s1, Wr.get_str(s1), {==}, h)
    case 4n+q:
      Unit{}

def ae.sp_top(+s: String, r: Wr.Dec<Nat>, +e: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> ae.Spelled(s, FA.get_ev(r)):
  match r:
    case Wr.Got{+t, +s1}:
      ae.sp_tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, e))
    case Wr.Bad{}:
      Unit{}

# whatever the entry's decoder reads from s was spelled
def ae.spelled(+s: String) -> ae.Spelled(s, FA.get_ev(Wr.get_nat(s))):
  ae.sp_top(s, Wr.get_nat(s), {==})

# The reply
# ---------

def ae.act(a: F.Act, rest: String) -> {FA.put_act(a, rest) == AuthFlightEntry.af_spell_act(a, rest) : String}:
  match a:
    case F.DoLoad{}:
      {==}
    case F.DoCheck{}:
      {==}
    case F.DoFetch{}:
      {==}
    case F.DoStore{}:
      {==}
    case F.DoWait{}:
      {==}
    case F.DoDone{}:
      {==}
    case F.DoFail{e}:
      {==}

def ae.tos(xs: List<&2, F.To>, +rest: String) -> {FA.put_tos(xs, rest) == AuthFlightEntry.af_spell_tos(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.To{+k, a}:
          %ae.tos(t, rest) : {Wr.put_nat(k, FA.put_act(a, FA.put_tos(t, rest))) == Wr.put_nat(k, AuthFlightEntry.af_spell_act(a, _)) : String}
          %ae.act(a, FA.put_tos(t, rest)) : {Wr.put_nat(k, FA.put_act(a, FA.put_tos(t, rest))) == Wr.put_nat(k, _) : String}
          {==}

def ae.out(o: F.DOut) -> {FA.put_out(o) == AuthFlightEntry.af_spell_out(o) : String}:
  match o:
    case F.Acts{+xs}:
      %ae.tos(xs, "") : {Wr.put_nat(List.length(&2, F.To, xs), FA.put_tos(xs, "")) == Wr.put_nat(List.length(&2, F.To, xs), _) : String}
      {==}
    case F.Joined{j}:
      match j:
        case None{}:
          {==}
        case Some{n}:
          {==}
    case F.Off{}:
      {==}

# The desk
# --------

def ae.find_at(hit: Bool, x: F.Cl, r: Maybe<&2, F.Cl>) -> {F.find.at(hit, x, r) == AuthFlightEntry.af_find.pick(hit, x, r) : Maybe<&2, F.Cl>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def ae.find(+k: Nat, cs: List<&2, F.Cl>) -> {F.find(k, cs) == AuthFlightEntry.af_find(k, cs) : Maybe<&2, F.Cl>}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j, +p, +a}:
          %ae.find(k, t) : {F.find.at(Nat.is_eq(j, k), F.Cl{j, p, a}, F.find(k, t)) == AuthFlightEntry.af_find.pick(Nat.is_eq(j, k), F.Cl{j, p, a}, _) : Maybe<&2, F.Cl>}
          ae.find_at(Nat.is_eq(j, k), F.Cl{j, p, a}, F.find(k, t))

def ae.set_at(hit: Bool, x: F.Cl, +a: F.At, t: List<&2, F.Cl>, r: List<&2, F.Cl>) -> {F.set.at(hit, x, a, t, r) == D.af_set.pick(hit, x, a, t, r) : List<&2, F.Cl>}:
  match hit:
    case True{}:
      match x:
        case F.Cl{j, p, o}:
          {==}
    case False{}:
      {==}

def ae.set(+k: Nat, +a: F.At, cs: List<&2, F.Cl>) -> {F.set(k, a, cs) == D.af_set(k, a, cs) : List<&2, F.Cl>}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j, +p, +o}:
          %ae.set(k, a, t) : {F.set.at(Nat.is_eq(j, k), F.Cl{j, p, o}, a, t, F.set(k, a, t)) == D.af_set.pick(Nat.is_eq(j, k), F.Cl{j, p, o}, a, t, _) : List<&2, F.Cl>}
          ae.set_at(Nat.is_eq(j, k), F.Cl{j, p, o}, a, t, F.set(k, a, t))

def ae.cut_at(hit: Bool, x: F.Cl, t: List<&2, F.Cl>, r: List<&2, F.Cl>) -> {F.cut.at(hit, x, t, r) == D.af_cut.pick(hit, x, t, r) : List<&2, F.Cl>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def ae.cut(+k: Nat, cs: List<&2, F.Cl>) -> {F.cut(k, cs) == D.af_cut(k, cs) : List<&2, F.Cl>}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j, +p, +o}:
          %ae.cut(k, t) : {F.cut.at(Nat.is_eq(j, k), F.Cl{j, p, o}, t, F.cut(k, t)) == D.af_cut.pick(Nat.is_eq(j, k), F.Cl{j, p, o}, t, _) : List<&2, F.Cl>}
          ae.cut_at(Nat.is_eq(j, k), F.Cl{j, p, o}, t, F.cut(k, t))

def ae.waits(+p: String, x: F.Cl) -> {F.waits(p, x) == AuthFlightEntry.af_waits(p, x) : Bool}:
  match x:
    case F.Cl{j, q, a}:
      match a:
        case F.Loads{}:
          {==}
        case F.Checks{}:
          {==}
        case F.Fetches{}:
          {==}
        case F.Stores{}:
          {==}
        case F.Waits{}:
          {==}

def ae.lead(+p: String, x: F.Cl) -> {F.lead(p, x) == AuthFlightEntry.af_lead(p, x) : Bool}:
  match x:
    case F.Cl{j, q, a}:
      match a:
        case F.Loads{}:
          {==}
        case F.Checks{}:
          {==}
        case F.Fetches{}:
          {==}
        case F.Stores{}:
          {==}
        case F.Waits{}:
          {==}

def ae.inflight(+p: String, cs: List<&2, F.Cl>) -> {F.inflight(p, cs) == AuthFlightEntry.af_inflight(p, cs) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +x <> +t:
      %ae.inflight(p, t) : {Bool.or(F.lead(p, x), F.inflight(p, t)) == Bool.or(AuthFlightEntry.af_lead(p, x), _) : Bool}
      %ae.lead(p, x) : {Bool.or(F.lead(p, x), F.inflight(p, t)) == Bool.or(_, F.inflight(p, t)) : Bool}
      {==}

def ae.unwait_at(hit: Bool, x: F.Cl, r: List<&2, F.Cl>) -> {F.unwait.at(hit, x, r) == D.af_unwait.pick(hit, x, r) : List<&2, F.Cl>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def ae.unwait(+p: String, cs: List<&2, F.Cl>) -> {F.unwait(p, cs) == D.af_unwait(p, cs) : List<&2, F.Cl>}:
  match cs:
    case Nil{}:
      {==}
    case +x <> +t:
      %ae.unwait(p, t) : {F.unwait.at(F.waits(p, x), x, F.unwait(p, t)) == D.af_unwait.pick(AuthFlightEntry.af_waits(p, x), x, _) : List<&2, F.Cl>}
      %ae.waits(p, x) : {F.unwait.at(F.waits(p, x), x, F.unwait(p, t)) == D.af_unwait.pick(_, x, F.unwait(p, t)) : List<&2, F.Cl>}
      ae.unwait_at(F.waits(p, x), x, F.unwait(p, t))

def ae.wake_at(hit: Bool, x: F.Cl, +a: F.Act, r: List<&2, F.To>) -> {F.wake.at(hit, x, a, r) == D.af_wake.pick(hit, x, a, r) : List<&2, F.To>}:
  match hit:
    case True{}:
      match x:
        case F.Cl{j, q, o}:
          {==}
    case False{}:
      {==}

def ae.wake(+p: String, +a: F.Act, cs: List<&2, F.Cl>) -> {F.wake(p, a, cs) == D.af_wake(p, a, cs) : List<&2, F.To>}:
  match cs:
    case Nil{}:
      {==}
    case +x <> +t:
      %ae.wake(p, a, t) : {F.wake.at(F.waits(p, x), x, a, F.wake(p, a, t)) == D.af_wake.pick(AuthFlightEntry.af_waits(p, x), x, a, _) : List<&2, F.To>}
      %ae.waits(p, x) : {F.wake.at(F.waits(p, x), x, a, F.wake(p, a, t)) == D.af_wake.pick(_, x, a, F.wake(p, a, t)) : List<&2, F.To>}
      ae.wake_at(F.waits(p, x), x, a, F.wake(p, a, t))

def ae.joined_at(hit: Bool, r: Nat) -> {F.joined.at(hit, r) == Nat.add(AuthFlightEntry.af_bit(hit), r) : Nat}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def ae.joined(+p: String, cs: List<&2, F.Cl>) -> {F.joined(p, cs) == D.af_joined(p, cs) : Nat}:
  match cs:
    case Nil{}:
      {==}
    case +x <> +t:
      %ae.joined(p, t) : {F.joined.at(F.waits(p, x), F.joined(p, t)) == Nat.add(AuthFlightEntry.af_bit(AuthFlightEntry.af_waits(p, x)), _) : Nat}
      %ae.waits(p, x) : {F.joined.at(F.waits(p, x), F.joined(p, t)) == Nat.add(AuthFlightEntry.af_bit(_), F.joined(p, t)) : Nat}
      ae.joined_at(F.waits(p, x), F.joined(p, t))

def ae.leads(a: F.At) -> {F.leads(a) == AuthFlightEntry.af_leads(a) : Bool}:
  match a:
    case F.Loads{}:
      {==}
    case F.Checks{}:
      {==}
    case F.Fetches{}:
      {==}
    case F.Stores{}:
      {==}
    case F.Waits{}:
      {==}

def ae.stage(a: F.At) -> {F.At.tag(a) == AuthFlightEntry.af_stage(a) : Nat}:
  match a:
    case F.Loads{}:
      {==}
    case F.Checks{}:
      {==}
    case F.Fetches{}:
      {==}
    case F.Stores{}:
      {==}
    case F.Waits{}:
      {==}

def ae.fd_stage(fd: F.Fd) -> {F.Fd.tag(fd) == AuthFlightEntry.af_fd_stage(fd) : Nat}:
  match fd:
    case F.LoadFresh{}:
      {==}
    case F.LoadExpired{}:
      {==}
    case F.LoadFailed{}:
      {==}
    case F.CheckFresh{}:
      {==}
    case F.CheckExpired{}:
      {==}
    case F.FetchOk{}:
      {==}
    case F.FetchFailed{}:
      {==}
    case F.Stored{}:
      {==}

# the desk's test of a found is the laws' af_takes
def ae.takes(+a: F.At, +fd: F.Fd) -> {Nat.is_eq(F.At.tag(a), F.Fd.tag(fd)) == AuthFlightEntry.af_takes(a, fd) : Bool}:
  %ae.stage(a) : {Nat.is_eq(F.At.tag(a), F.Fd.tag(fd)) == Nat.is_eq(_, AuthFlightEntry.af_fd_stage(fd)) : Bool}
  %ae.fd_stage(fd) : {Nat.is_eq(F.At.tag(a), F.Fd.tag(fd)) == Nat.is_eq(F.At.tag(a), _) : Bool}
  {==}

def ae.land(+k: Nat, +p: String, +cs: List<&2, F.Cl>, +m: Nat) -> {F.land(k, p, cs, m) == D.af_land(k, p, cs, m) : F.DRes}:
  %ae.cut(k, cs) : {F.land(k, p, cs, m) == F.DRes{F.Desk{D.af_unwait(p, _), m}, F.Acts{F.To{k, F.DoDone{}} <> D.af_wake(p, F.DoDone{}, _)}} : F.DRes}
  %ae.unwait(p, F.cut(k, cs)) : {F.land(k, p, cs, m) == F.DRes{F.Desk{_, m}, F.Acts{F.To{k, F.DoDone{}} <> D.af_wake(p, F.DoDone{}, F.cut(k, cs))}} : F.DRes}
  %ae.wake(p, F.DoDone{}, F.cut(k, cs)) : {F.land(k, p, cs, m) == F.DRes{F.Desk{F.unwait(p, F.cut(k, cs)), m}, F.Acts{F.To{k, F.DoDone{}} <> _}} : F.DRes}
  {==}

def ae.board(fl: Bool, +k: Nat, +cs: List<&2, F.Cl>, +m: Nat) -> {F.board(fl, k, cs, m) == D.af_board(fl, k, cs, m) : F.DRes}:
  match fl:
    case True{}:
      %ae.set(k, F.Waits{}, cs) : {F.board(True{}, k, cs, m) == F.DRes{F.Desk{_, m}, F.Acts{[F.To{k, F.DoWait{}}]}} : F.DRes}
      {==}
    case False{}:
      %ae.set(k, F.Checks{}, cs) : {F.board(False{}, k, cs, m) == F.DRes{F.Desk{_, m}, F.Acts{[F.To{k, F.DoCheck{}}]}} : F.DRes}
      {==}

def ae.found_go(fd: F.Fd, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +m: Nat) -> {F.found.go(fd, k, p, cs, m) == D.af_found(fd, k, p, cs, m) : F.DRes}:
  match fd:
    case F.LoadFresh{}:
      %ae.cut(k, cs) : {F.found.go(F.LoadFresh{}, k, p, cs, m) == F.DRes{F.Desk{_, m}, F.Acts{[F.To{k, F.DoDone{}}]}} : F.DRes}
      {==}
    case F.LoadExpired{}:
      %ae.inflight(p, cs) : {F.found.go(F.LoadExpired{}, k, p, cs, m) == D.af_board(_, k, cs, m) : F.DRes}
      ae.board(F.inflight(p, cs), k, cs, m)
    case F.LoadFailed{}:
      %ae.cut(k, cs) : {F.found.go(F.LoadFailed{}, k, p, cs, m) == F.DRes{F.Desk{_, m}, F.Acts{[F.To{k, F.DoDone{}}]}} : F.DRes}
      {==}
    case F.CheckFresh{}:
      ae.land(k, p, cs, m)
    case F.CheckExpired{}:
      %ae.set(k, F.Fetches{}, cs) : {F.found.go(F.CheckExpired{}, k, p, cs, m) == F.DRes{F.Desk{_, m}, F.Acts{[F.To{k, F.DoFetch{}}]}} : F.DRes}
      {==}
    case F.FetchOk{}:
      %ae.set(k, F.Stores{}, cs) : {F.found.go(F.FetchOk{}, k, p, cs, m) == F.DRes{F.Desk{_, m}, F.Acts{[F.To{k, F.DoStore{}}]}} : F.DRes}
      {==}
    case F.FetchFailed{}:
      ae.land(k, p, cs, m)
    case F.Stored{}:
      ae.land(k, p, cs, m)

def ae.found_fit(fit: Bool, fd: F.Fd, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +m: Nat) -> {F.found.fit(fit, fd, k, p, cs, m) == D.af_found_fit(fit, fd, k, p, cs, m) : F.DRes}:
  match fit:
    case True{}:
      ae.found_go(fd, k, p, cs, m)
    case False{}:
      {==}

def ae.d_found(r: Maybe<&2, F.Cl>, +fd: F.Fd, +k: Nat, +cs: List<&2, F.Cl>, +m: Nat) -> {F.found(r, fd, k, cs, m) == D.af_found_at(r, fd, k, cs, m) : F.DRes}:
  match r:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case F.Cl{j, +p, +a}:
          %ae.takes(a, fd) : {F.found.fit(Nat.is_eq(F.At.tag(a), F.Fd.tag(fd)), fd, k, p, cs, m) == D.af_found_fit(_, fd, k, p, cs, m) : F.DRes}
          ae.found_fit(Nat.is_eq(F.At.tag(a), F.Fd.tag(fd)), fd, k, p, cs, m)

def ae.unwind_at(lead: Bool, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +m: Nat) -> {F.unwind.at(lead, k, p, cs, m) == D.af_unwind_lead(lead, k, p, cs, m) : F.DRes}:
  match lead:
    case True{}:
      %ae.cut(k, cs) : {F.unwind.at(True{}, k, p, cs, m) == F.DRes{F.Desk{D.af_unwait(p, _), m}, F.Acts{D.af_wake(p, F.DoFail{AuthFlightEntry.af_gone(p)}, _)}} : F.DRes}
      %ae.unwait(p, F.cut(k, cs)) : {F.unwind.at(True{}, k, p, cs, m) == F.DRes{F.Desk{_, m}, F.Acts{D.af_wake(p, F.DoFail{AuthFlightEntry.af_gone(p)}, F.cut(k, cs))}} : F.DRes}
      %ae.wake(p, F.DoFail{AuthFlightEntry.af_gone(p)}, F.cut(k, cs)) : {F.unwind.at(True{}, k, p, cs, m) == F.DRes{F.Desk{F.unwait(p, F.cut(k, cs)), m}, F.Acts{_}} : F.DRes}
      {==}
    case False{}:
      %ae.cut(k, cs) : {F.unwind.at(False{}, k, p, cs, m) == F.DRes{F.Desk{_, m}, F.Acts{Nil{}}} : F.DRes}
      {==}

def ae.d_unwind(r: Maybe<&2, F.Cl>, +k: Nat, +cs: List<&2, F.Cl>, +m: Nat) -> {F.unwind(r, k, cs, m) == D.af_unwind_at(r, k, cs, m) : F.DRes}:
  match r:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case F.Cl{j, +p, +a}:
          %ae.leads(a) : {F.unwind.at(F.leads(a), k, p, cs, m) == D.af_unwind_lead(_, k, p, cs, m) : F.DRes}
          ae.unwind_at(F.leads(a), k, p, cs, m)

def ae.d_joiners(fl: Bool, +p: String, +cs: List<&2, F.Cl>) -> {F.joiners(fl, p, cs) == D.af_joiners(fl, p, cs) : Maybe<&2, Nat>}:
  match fl:
    case True{}:
      %ae.joined(p, cs) : {F.joiners(True{}, p, cs) == Some{_} : Maybe<&2, Nat>}
      {==}
    case False{}:
      {==}

# the desk is the proofs' restated desk, function by function
def ae.desk(d: F.Desk, e: F.DEv) -> {F.desk.step(d, e) == D.af_desk(d, e) : F.DRes}:
  match d:
    case F.Desk{+cs, +m}:
      match e:
        case F.Comes{p}:
          {==}
        case F.Found{+k, +fd}:
          %ae.find(k, cs) : {F.found(F.find(k, cs), fd, k, cs, m) == D.af_found_at(_, fd, k, cs, m) : F.DRes}
          ae.d_found(F.find(k, cs), fd, k, cs, m)
        case F.Unwinds{+k}:
          %ae.find(k, cs) : {F.unwind(F.find(k, cs), k, cs, m) == D.af_unwind_at(_, k, cs, m) : F.DRes}
          ae.d_unwind(F.find(k, cs), k, cs, m)
        case F.Joiners{+p}:
          %ae.inflight(p, cs) : {F.DRes{F.Desk{cs, m}, F.Joined{F.joiners(F.inflight(p, cs), p, cs)}} == F.DRes{F.Desk{cs, m}, F.Joined{D.af_joiners(_, p, cs)}} : F.DRes}
          %ae.d_joiners(F.inflight(p, cs), p, cs) : {F.DRes{F.Desk{cs, m}, F.Joined{F.joiners(F.inflight(p, cs), p, cs)}} == F.DRes{F.Desk{cs, m}, F.Joined{_}} : F.DRes}
          {==}

# The stepper
# -----------

def ae.put(r: F.DRes) -> {FA.step.put(r) == AuthFlightEntry.af_step_of(r) : FA.St & String}:
  match r:
    case F.DRes{+d, o}:
      %ae.out(o) : {(FA.Open{d}, FA.put_out(o)) == (FA.Open{d}, _) : FA.St & String}
      {==}

# a spelled event that fits, then rest: the entry ends its read there
def ae.step_spelled(+d: F.Desk, +e: F.DEv, +r: String, +fits: {AuthFlightEntry.af_ev_fits(e) == True{} : Bool}) -> {FA.step(FA.Open{d}, AuthFlightEntry.af_spell_ev(e, r)) == FA.step.fin(Wr.end(r), d, e) : FA.St & String}:
  %Equal.sym(Wr.Dec<F.DEv>, FA.get_ev(Wr.get_nat(AuthFlightEntry.af_spell_ev(e, r))), Wr.Got{e, r}, ae.get(e, r, fits)) : {FA.step.go(d, _) == FA.step.fin(Wr.end(r), d, e) : FA.St & String}
  {==}

# a spelled event that fits steps the desk, its reply spelled
def ae.answers_code(+d: F.Desk, +e: F.DEv, +fits: {AuthFlightEntry.af_ev_fits(e) == True{} : Bool}) -> {FA.step(FA.Open{d}, AuthFlightEntry.af_spell_ev(e, "")) == AuthFlightEntry.af_step_of(F.desk.step(d, e)) : FA.St & String}:
  Equal.trans(FA.St & String, FA.step(FA.Open{d}, AuthFlightEntry.af_spell_ev(e, "")), FA.step.fin(Wr.end(""), d, e), AuthFlightEntry.af_step_of(F.desk.step(d, e)), ae.step_spelled(d, e, "", fits), ae.put(F.desk.step(d, e)))

# a spelled event that fits steps the desk as the proofs' restated desk
def ae.answers(+d: F.Desk, +e: F.DEv, +fits: {AuthFlightEntry.af_ev_fits(e) == True{} : Bool}) -> {FA.step(FA.Open{d}, AuthFlightEntry.af_spell_ev(e, "")) == AuthFlightEntry.af_step_of(D.af_desk(d, e)) : FA.St & String}:
  %ae.desk(d, e) : {FA.step(FA.Open{d}, AuthFlightEntry.af_spell_ev(e, "")) == AuthFlightEntry.af_step_of(_) : FA.St & String}
  ae.answers_code(d, e, fits)

# Absurd premises
# ---------------

def ae.BB(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

# False is not True
def ae.ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : ae.BB(_, G, Unit)
  Unit{}

# True is not False
def ae.tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : ae.BB(_, Unit, G)
  Unit{}

# a spelled event that fits steps the desk as the laws' desk, turned
# around (to rewrite the entry's step into the laws' desk)
def ae.answers_r(+d: F.Desk, +e: F.DEv, fits: {AuthFlightEntry.af_ev_fits(e) == True{} : Bool}) -> {AuthFlightEntry.af_step_of(D.af_desk(d, e)) == FA.step(FA.Open{d}, AuthFlightEntry.af_spell_ev(e, "")) : FA.St & String}:
  Equal.sym(FA.St & String, FA.step(FA.Open{d}, AuthFlightEntry.af_spell_ev(e, "")), AuthFlightEntry.af_step_of(D.af_desk(d, e)), ae.answers(d, e, fits))

# a premise on the first live caller numbered k, turned around
def ae.at_r(+k: Nat, +cs: List<&2, F.Cl>, +x: F.Cl, at: {AuthFlightEntry.af_find(k, cs) == Some{x} : Maybe<&2, F.Cl>}) -> {Some{x} == AuthFlightEntry.af_find(k, cs) : Maybe<&2, F.Cl>}:
  Equal.sym(Maybe<&2, F.Cl>, AuthFlightEntry.af_find(k, cs), Some{x}, at)
