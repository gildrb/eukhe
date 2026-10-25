# eukhe: lemmas the proofs of the auth_flight entry share
# The entry (bend/ffi_auth_flight.bend) reads every input as the laws'
# reader does, spells every reply as the laws' speller does, and its desk
# (F.desk.step) is the laws' desk (af_desk), function by function.

import Base
import ../../../bend/auth_flight.bend as F
import ../../../bend/ffi_auth_flight.bend as FA
import ../../../bend/wire.bend as Wr
import ../../../laws/auth_flight/entry.bend as AuthFlightEntry
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../base/wire.bend as LWire

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

# a Some that is a None proves anything
def ae.some_none(-A: Data, -G: Type, -x: A, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  %e : ae.MD(A, _, G, Unit)
  Unit{}

def ae.some_inj(-A: Data, +d: A, -x: A, -y: A, e: {Some{x} == Some{y} : Maybe<&2, A>}) -> {x == y : A}:
  Equal.cong(Maybe<&2, A>, A, m => Maybe.default(&2, A, m, d), Some{x}, Some{y}, e)

# The reader
# ----------

def ae.what(k: Nat, t: Nat, s: String) -> {AuthFlightEntry.af_read_ev.what(k, t, s) == FA.get_ev.what(k, t, s) : Wr.Dec<F.DEv>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n+q:
      {==}

def ae.found(k: Nat, r: Wr.Dec<Nat>) -> {AuthFlightEntry.af_read_ev.found(k, r) == FA.get_ev.found(k, r) : Wr.Dec<F.DEv>}:
  match r:
    case Wr.Got{t, s}:
      ae.what(k, t, s)
    case Wr.Bad{}:
      {==}

def ae.caller(r: Wr.Dec<Nat>) -> {AuthFlightEntry.af_read_ev.caller(r) == FA.get_ev.caller(r) : Wr.Dec<F.DEv>}:
  match r:
    case Wr.Got{k, s}:
      ae.found(k, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def ae.unwind(r: Wr.Dec<Nat>) -> {AuthFlightEntry.af_read_ev.unwind(r) == FA.get_ev.unwind(r) : Wr.Dec<F.DEv>}:
  match r:
    case Wr.Got{k, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ae.comes(r: Wr.Dec<String>) -> {AuthFlightEntry.af_read_ev.comes(r) == FA.get_ev.comes(r) : Wr.Dec<F.DEv>}:
  match r:
    case Wr.Got{p, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ae.joiners(r: Wr.Dec<String>) -> {AuthFlightEntry.af_read_ev.joiners(r) == FA.get_ev.joiners(r) : Wr.Dec<F.DEv>}:
  match r:
    case Wr.Got{p, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ae.tag(t: Nat, s: String) -> {AuthFlightEntry.af_read_ev.tag(t, s) == FA.get_ev.tag(t, s) : Wr.Dec<F.DEv>}:
  match t:
    case 0n:
      ae.comes(Wr.get_str(s))
    case 1n:
      ae.caller(Wr.get_nat(s))
    case 2n:
      ae.unwind(Wr.get_nat(s))
    case 3n:
      ae.joiners(Wr.get_str(s))
    case 4n+p:
      {==}

# the entry reads every event as the laws' reader does
def ae.ev(r: Wr.Dec<Nat>) -> {AuthFlightEntry.af_read_ev.go(r) == FA.get_ev(r) : Wr.Dec<F.DEv>}:
  match r:
    case Wr.Got{t, s}:
      ae.tag(t, s)
    case Wr.Bad{}:
      {==}

# every event Rust writes reads back
def ae.read_what(+k: Nat, fd: F.Fd) -> {AuthFlightEntry.af_read_ev.whole(AuthFlightEntry.af_read_ev.what(k, AuthFlightEntry.af_what(fd), "")) == Some{F.Found{k, fd}} : Maybe<&2, F.DEv>}:
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

def ae.read_ev_spell(e: F.DEv, +fits: {AuthFlightEntry.af_ev_fits(e) == True{} : Bool}) -> {AuthFlightEntry.af_read_ev(AuthFlightEntry.af_spell_ev(e)) == Some{e} : Maybe<&2, F.DEv>}:
  match e:
    case F.Comes{+p}:
      %LWire.pw6.nat(0n, Wr.put_str(p, ""), {==}) : {AuthFlightEntry.af_read_ev.whole(AuthFlightEntry.af_read_ev.go(_)) == Some{F.Comes{p}} : Maybe<&2, F.DEv>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(p, "")), Wr.Got{p, ""}, Wire.wire_str_round_trip(p, "", fits)) : {AuthFlightEntry.af_read_ev.whole(AuthFlightEntry.af_read_ev.comes(_)) == Some{F.Comes{p}} : Maybe<&2, F.DEv>}
      {==}
    case F.Found{+k, +fd}:
      %LWire.pw6.nat(1n, Wr.put_nat(k, Wr.put_nat(AuthFlightEntry.af_what(fd), "")), {==}) : {AuthFlightEntry.af_read_ev.whole(AuthFlightEntry.af_read_ev.go(_)) == Some{F.Found{k, fd}} : Maybe<&2, F.DEv>}
      %LWire.pw6.nat(k, Wr.put_nat(AuthFlightEntry.af_what(fd), ""), fits) : {AuthFlightEntry.af_read_ev.whole(AuthFlightEntry.af_read_ev.caller(_)) == Some{F.Found{k, fd}} : Maybe<&2, F.DEv>}
      %LWire.pw6.nat(AuthFlightEntry.af_what(fd), "", ae.what_fits(fd)) : {AuthFlightEntry.af_read_ev.whole(AuthFlightEntry.af_read_ev.found(k, _)) == Some{F.Found{k, fd}} : Maybe<&2, F.DEv>}
      ae.read_what(k, fd)
    case F.Unwinds{+k}:
      %LWire.pw6.nat(2n, Wr.put_nat(k, ""), {==}) : {AuthFlightEntry.af_read_ev.whole(AuthFlightEntry.af_read_ev.go(_)) == Some{F.Unwinds{k}} : Maybe<&2, F.DEv>}
      %LWire.pw6.nat(k, "", fits) : {AuthFlightEntry.af_read_ev.whole(AuthFlightEntry.af_read_ev.unwind(_)) == Some{F.Unwinds{k}} : Maybe<&2, F.DEv>}
      {==}
    case F.Joiners{+p}:
      %LWire.pw6.nat(3n, Wr.put_str(p, ""), {==}) : {AuthFlightEntry.af_read_ev.whole(AuthFlightEntry.af_read_ev.go(_)) == Some{F.Joiners{p}} : Maybe<&2, F.DEv>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(p, "")), Wr.Got{p, ""}, Wire.wire_str_round_trip(p, "", fits)) : {AuthFlightEntry.af_read_ev.whole(AuthFlightEntry.af_read_ev.joiners(_)) == Some{F.Joiners{p}} : Maybe<&2, F.DEv>}
      {==}

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

def ae.set_at(hit: Bool, x: F.Cl, +a: F.At, t: List<&2, F.Cl>, r: List<&2, F.Cl>) -> {F.set.at(hit, x, a, t, r) == AuthFlightEntry.af_set.pick(hit, x, a, t, r) : List<&2, F.Cl>}:
  match hit:
    case True{}:
      match x:
        case F.Cl{j, p, o}:
          {==}
    case False{}:
      {==}

def ae.set(+k: Nat, +a: F.At, cs: List<&2, F.Cl>) -> {F.set(k, a, cs) == AuthFlightEntry.af_set(k, a, cs) : List<&2, F.Cl>}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j, +p, +o}:
          %ae.set(k, a, t) : {F.set.at(Nat.is_eq(j, k), F.Cl{j, p, o}, a, t, F.set(k, a, t)) == AuthFlightEntry.af_set.pick(Nat.is_eq(j, k), F.Cl{j, p, o}, a, t, _) : List<&2, F.Cl>}
          ae.set_at(Nat.is_eq(j, k), F.Cl{j, p, o}, a, t, F.set(k, a, t))

def ae.cut_at(hit: Bool, x: F.Cl, t: List<&2, F.Cl>, r: List<&2, F.Cl>) -> {F.cut.at(hit, x, t, r) == AuthFlightEntry.af_cut.pick(hit, x, t, r) : List<&2, F.Cl>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def ae.cut(+k: Nat, cs: List<&2, F.Cl>) -> {F.cut(k, cs) == AuthFlightEntry.af_cut(k, cs) : List<&2, F.Cl>}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j, +p, +o}:
          %ae.cut(k, t) : {F.cut.at(Nat.is_eq(j, k), F.Cl{j, p, o}, t, F.cut(k, t)) == AuthFlightEntry.af_cut.pick(Nat.is_eq(j, k), F.Cl{j, p, o}, t, _) : List<&2, F.Cl>}
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

def ae.unwait_at(hit: Bool, x: F.Cl, r: List<&2, F.Cl>) -> {F.unwait.at(hit, x, r) == AuthFlightEntry.af_unwait.pick(hit, x, r) : List<&2, F.Cl>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def ae.unwait(+p: String, cs: List<&2, F.Cl>) -> {F.unwait(p, cs) == AuthFlightEntry.af_unwait(p, cs) : List<&2, F.Cl>}:
  match cs:
    case Nil{}:
      {==}
    case +x <> +t:
      %ae.unwait(p, t) : {F.unwait.at(F.waits(p, x), x, F.unwait(p, t)) == AuthFlightEntry.af_unwait.pick(AuthFlightEntry.af_waits(p, x), x, _) : List<&2, F.Cl>}
      %ae.waits(p, x) : {F.unwait.at(F.waits(p, x), x, F.unwait(p, t)) == AuthFlightEntry.af_unwait.pick(_, x, F.unwait(p, t)) : List<&2, F.Cl>}
      ae.unwait_at(F.waits(p, x), x, F.unwait(p, t))

def ae.wake_at(hit: Bool, x: F.Cl, +a: F.Act, r: List<&2, F.To>) -> {F.wake.at(hit, x, a, r) == AuthFlightEntry.af_wake.pick(hit, x, a, r) : List<&2, F.To>}:
  match hit:
    case True{}:
      match x:
        case F.Cl{j, q, o}:
          {==}
    case False{}:
      {==}

def ae.wake(+p: String, +a: F.Act, cs: List<&2, F.Cl>) -> {F.wake(p, a, cs) == AuthFlightEntry.af_wake(p, a, cs) : List<&2, F.To>}:
  match cs:
    case Nil{}:
      {==}
    case +x <> +t:
      %ae.wake(p, a, t) : {F.wake.at(F.waits(p, x), x, a, F.wake(p, a, t)) == AuthFlightEntry.af_wake.pick(AuthFlightEntry.af_waits(p, x), x, a, _) : List<&2, F.To>}
      %ae.waits(p, x) : {F.wake.at(F.waits(p, x), x, a, F.wake(p, a, t)) == AuthFlightEntry.af_wake.pick(_, x, a, F.wake(p, a, t)) : List<&2, F.To>}
      ae.wake_at(F.waits(p, x), x, a, F.wake(p, a, t))

def ae.joined_at(hit: Bool, r: Nat) -> {F.joined.at(hit, r) == Nat.add(AuthFlightEntry.af_bit(hit), r) : Nat}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def ae.joined(+p: String, cs: List<&2, F.Cl>) -> {F.joined(p, cs) == AuthFlightEntry.af_joined(p, cs) : Nat}:
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

def ae.land(+k: Nat, +p: String, +cs: List<&2, F.Cl>, +m: Nat) -> {F.land(k, p, cs, m) == AuthFlightEntry.af_land(k, p, cs, m) : F.DRes}:
  %ae.cut(k, cs) : {F.land(k, p, cs, m) == F.DRes{F.Desk{AuthFlightEntry.af_unwait(p, _), m}, F.Acts{F.To{k, F.DoDone{}} <> AuthFlightEntry.af_wake(p, F.DoDone{}, _)}} : F.DRes}
  %ae.unwait(p, F.cut(k, cs)) : {F.land(k, p, cs, m) == F.DRes{F.Desk{_, m}, F.Acts{F.To{k, F.DoDone{}} <> AuthFlightEntry.af_wake(p, F.DoDone{}, F.cut(k, cs))}} : F.DRes}
  %ae.wake(p, F.DoDone{}, F.cut(k, cs)) : {F.land(k, p, cs, m) == F.DRes{F.Desk{F.unwait(p, F.cut(k, cs)), m}, F.Acts{F.To{k, F.DoDone{}} <> _}} : F.DRes}
  {==}

def ae.board(fl: Bool, +k: Nat, +cs: List<&2, F.Cl>, +m: Nat) -> {F.board(fl, k, cs, m) == AuthFlightEntry.af_board(fl, k, cs, m) : F.DRes}:
  match fl:
    case True{}:
      %ae.set(k, F.Waits{}, cs) : {F.board(True{}, k, cs, m) == F.DRes{F.Desk{_, m}, F.Acts{[F.To{k, F.DoWait{}}]}} : F.DRes}
      {==}
    case False{}:
      %ae.set(k, F.Checks{}, cs) : {F.board(False{}, k, cs, m) == F.DRes{F.Desk{_, m}, F.Acts{[F.To{k, F.DoCheck{}}]}} : F.DRes}
      {==}

def ae.found_go(fd: F.Fd, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +m: Nat) -> {F.found.go(fd, k, p, cs, m) == AuthFlightEntry.af_found(fd, k, p, cs, m) : F.DRes}:
  match fd:
    case F.LoadFresh{}:
      %ae.cut(k, cs) : {F.found.go(F.LoadFresh{}, k, p, cs, m) == F.DRes{F.Desk{_, m}, F.Acts{[F.To{k, F.DoDone{}}]}} : F.DRes}
      {==}
    case F.LoadExpired{}:
      %ae.inflight(p, cs) : {F.found.go(F.LoadExpired{}, k, p, cs, m) == AuthFlightEntry.af_board(_, k, cs, m) : F.DRes}
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

def ae.found_fit(fit: Bool, fd: F.Fd, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +m: Nat) -> {F.found.fit(fit, fd, k, p, cs, m) == AuthFlightEntry.af_found_fit(fit, fd, k, p, cs, m) : F.DRes}:
  match fit:
    case True{}:
      ae.found_go(fd, k, p, cs, m)
    case False{}:
      {==}

def ae.d_found(r: Maybe<&2, F.Cl>, +fd: F.Fd, +k: Nat, +cs: List<&2, F.Cl>, +m: Nat) -> {F.found(r, fd, k, cs, m) == AuthFlightEntry.af_found_at(r, fd, k, cs, m) : F.DRes}:
  match r:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case F.Cl{j, +p, +a}:
          %ae.takes(a, fd) : {F.found.fit(Nat.is_eq(F.At.tag(a), F.Fd.tag(fd)), fd, k, p, cs, m) == AuthFlightEntry.af_found_fit(_, fd, k, p, cs, m) : F.DRes}
          ae.found_fit(Nat.is_eq(F.At.tag(a), F.Fd.tag(fd)), fd, k, p, cs, m)

def ae.unwind_at(lead: Bool, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +m: Nat) -> {F.unwind.at(lead, k, p, cs, m) == AuthFlightEntry.af_unwind_lead(lead, k, p, cs, m) : F.DRes}:
  match lead:
    case True{}:
      %ae.cut(k, cs) : {F.unwind.at(True{}, k, p, cs, m) == F.DRes{F.Desk{AuthFlightEntry.af_unwait(p, _), m}, F.Acts{AuthFlightEntry.af_wake(p, F.DoFail{AuthFlightEntry.af_gone(p)}, _)}} : F.DRes}
      %ae.unwait(p, F.cut(k, cs)) : {F.unwind.at(True{}, k, p, cs, m) == F.DRes{F.Desk{_, m}, F.Acts{AuthFlightEntry.af_wake(p, F.DoFail{AuthFlightEntry.af_gone(p)}, F.cut(k, cs))}} : F.DRes}
      %ae.wake(p, F.DoFail{AuthFlightEntry.af_gone(p)}, F.cut(k, cs)) : {F.unwind.at(True{}, k, p, cs, m) == F.DRes{F.Desk{F.unwait(p, F.cut(k, cs)), m}, F.Acts{_}} : F.DRes}
      {==}
    case False{}:
      %ae.cut(k, cs) : {F.unwind.at(False{}, k, p, cs, m) == F.DRes{F.Desk{_, m}, F.Acts{Nil{}}} : F.DRes}
      {==}

def ae.d_unwind(r: Maybe<&2, F.Cl>, +k: Nat, +cs: List<&2, F.Cl>, +m: Nat) -> {F.unwind(r, k, cs, m) == AuthFlightEntry.af_unwind_at(r, k, cs, m) : F.DRes}:
  match r:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case F.Cl{j, +p, +a}:
          %ae.leads(a) : {F.unwind.at(F.leads(a), k, p, cs, m) == AuthFlightEntry.af_unwind_lead(_, k, p, cs, m) : F.DRes}
          ae.unwind_at(F.leads(a), k, p, cs, m)

def ae.d_joiners(fl: Bool, +p: String, +cs: List<&2, F.Cl>) -> {F.joiners(fl, p, cs) == AuthFlightEntry.af_joiners(fl, p, cs) : Maybe<&2, Nat>}:
  match fl:
    case True{}:
      %ae.joined(p, cs) : {F.joiners(True{}, p, cs) == Some{_} : Maybe<&2, Nat>}
      {==}
    case False{}:
      {==}

# the entry's desk is the laws' desk
def ae.desk(d: F.Desk, e: F.DEv) -> {F.desk.step(d, e) == AuthFlightEntry.af_desk(d, e) : F.DRes}:
  match d:
    case F.Desk{+cs, +m}:
      match e:
        case F.Comes{p}:
          {==}
        case F.Found{+k, +fd}:
          %ae.find(k, cs) : {F.found(F.find(k, cs), fd, k, cs, m) == AuthFlightEntry.af_found_at(_, fd, k, cs, m) : F.DRes}
          ae.d_found(F.find(k, cs), fd, k, cs, m)
        case F.Unwinds{+k}:
          %ae.find(k, cs) : {F.unwind(F.find(k, cs), k, cs, m) == AuthFlightEntry.af_unwind_at(_, k, cs, m) : F.DRes}
          ae.d_unwind(F.find(k, cs), k, cs, m)
        case F.Joiners{+p}:
          %ae.inflight(p, cs) : {F.DRes{F.Desk{cs, m}, F.Joined{F.joiners(F.inflight(p, cs), p, cs)}} == F.DRes{F.Desk{cs, m}, F.Joined{AuthFlightEntry.af_joiners(_, p, cs)}} : F.DRes}
          %ae.d_joiners(F.inflight(p, cs), p, cs) : {F.DRes{F.Desk{cs, m}, F.Joined{F.joiners(F.inflight(p, cs), p, cs)}} == F.DRes{F.Desk{cs, m}, F.Joined{_}} : F.DRes}
          {==}

# The stepper
# -----------

def ae.put(r: F.DRes) -> {FA.step.put(r) == AuthFlightEntry.af_step_of(r) : FA.St & String}:
  match r:
    case F.DRes{+d, o}:
      %ae.out(o) : {(FA.Open{d}, FA.put_out(o)) == (FA.Open{d}, _) : FA.St & String}
      {==}

def ae.step_fin(b: Bool, +d: F.Desk, +x: F.DEv, -e: F.DEv, got: {AuthFlightEntry.af_whole(F.DEv, b, x) == Some{e} : Maybe<&2, F.DEv>}) -> {FA.step.fin(b, d, x) == AuthFlightEntry.af_step_of(AuthFlightEntry.af_desk(d, e)) : FA.St & String}:
  match b:
    case True{}:
      %ae.some_inj(F.DEv, x, x, e, got) : {FA.step.put(F.desk.step(d, x)) == AuthFlightEntry.af_step_of(AuthFlightEntry.af_desk(d, _)) : FA.St & String}
      %ae.desk(d, x) : {FA.step.put(F.desk.step(d, x)) == AuthFlightEntry.af_step_of(_) : FA.St & String}
      ae.put(F.desk.step(d, x))
    case False{}:
      ae.none_some(F.DEv, {FA.step.fin(False{}, d, x) == AuthFlightEntry.af_step_of(AuthFlightEntry.af_desk(d, e)) : FA.St & String}, e, got)

def ae.step_got(r: Wr.Dec<F.DEv>, +d: F.Desk, -e: F.DEv, got: {AuthFlightEntry.af_read_ev.whole(r) == Some{e} : Maybe<&2, F.DEv>}) -> {FA.step.go(d, r) == AuthFlightEntry.af_step_of(AuthFlightEntry.af_desk(d, e)) : FA.St & String}:
  match r:
    case Wr.Got{x, s}:
      ae.step_fin(Wr.end(s), d, x, e, got)
    case Wr.Bad{}:
      ae.none_some(F.DEv, {FA.step.go(d, Wr.Bad{}) == AuthFlightEntry.af_step_of(AuthFlightEntry.af_desk(d, e)) : FA.St & String}, e, got)

# a whole event steps the desk as the laws' desk
def ae.step_reads(+d: F.Desk, +s: String, -e: F.DEv, got: {AuthFlightEntry.af_read_ev(s) == Some{e} : Maybe<&2, F.DEv>}) -> {FA.step(FA.Open{d}, s) == AuthFlightEntry.af_step_of(AuthFlightEntry.af_desk(d, e)) : FA.St & String}:
  %ae.ev(Wr.get_nat(s)) : {FA.step.go(d, _) == AuthFlightEntry.af_step_of(AuthFlightEntry.af_desk(d, e)) : FA.St & String}
  ae.step_got(AuthFlightEntry.af_read_ev.go(Wr.get_nat(s)), d, e, got)

def ae.step_bad_fin(b: Bool, +d: F.Desk, -x: F.DEv, no: {AuthFlightEntry.af_whole(F.DEv, b, x) == None{} : Maybe<&2, F.DEv>}) -> {FA.step.fin(b, d, x) == (FA.Open{d}, SCon{'E', SCon{' ', "auth_flight: malformed event"}}) : FA.St & String}:
  match b:
    case True{}:
      ae.some_none(F.DEv, {FA.step.fin(True{}, d, x) == (FA.Open{d}, SCon{'E', SCon{' ', "auth_flight: malformed event"}}) : FA.St & String}, x, no)
    case False{}:
      {==}

def ae.step_bad(r: Wr.Dec<F.DEv>, +d: F.Desk, no: {AuthFlightEntry.af_read_ev.whole(r) == None{} : Maybe<&2, F.DEv>}) -> {FA.step.go(d, r) == (FA.Open{d}, SCon{'E', SCon{' ', "auth_flight: malformed event"}}) : FA.St & String}:
  match r:
    case Wr.Got{x, s}:
      ae.step_bad_fin(Wr.end(s), d, x, no)
    case Wr.Bad{}:
      {==}

# a spelled event that fits steps the desk as the laws' desk
def ae.answers(+d: F.Desk, +e: F.DEv, fits: {AuthFlightEntry.af_ev_fits(e) == True{} : Bool}) -> {FA.step(FA.Open{d}, AuthFlightEntry.af_spell_ev(e)) == AuthFlightEntry.af_step_of(AuthFlightEntry.af_desk(d, e)) : FA.St & String}:
  ae.step_reads(d, AuthFlightEntry.af_spell_ev(e), e, ae.read_ev_spell(e, fits))

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
def ae.answers_r(+d: F.Desk, +e: F.DEv, fits: {AuthFlightEntry.af_ev_fits(e) == True{} : Bool}) -> {AuthFlightEntry.af_step_of(AuthFlightEntry.af_desk(d, e)) == FA.step(FA.Open{d}, AuthFlightEntry.af_spell_ev(e)) : FA.St & String}:
  Equal.sym(FA.St & String, FA.step(FA.Open{d}, AuthFlightEntry.af_spell_ev(e)), AuthFlightEntry.af_step_of(AuthFlightEntry.af_desk(d, e)), ae.answers(d, e, fits))

# a premise on the first live caller numbered k, turned around
def ae.at_r(+k: Nat, +cs: List<&2, F.Cl>, +x: F.Cl, at: {AuthFlightEntry.af_find(k, cs) == Some{x} : Maybe<&2, F.Cl>}) -> {Some{x} == AuthFlightEntry.af_find(k, cs) : Maybe<&2, F.Cl>}:
  Equal.sym(Maybe<&2, F.Cl>, AuthFlightEntry.af_find(k, cs), Some{x}, at)
