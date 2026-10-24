# eukhe: lemmas the proofs of the auth_flight entry share
# The entry (bend/ffi_auth_flight.bend) reads every input as the laws'
# readers do, answers the laws' reply, and its book is the laws' book.

import Base
import ../../../bend/auth_flight.bend as F
import ../../../bend/ffi_auth_flight.bend as FA
import ../../../bend/wire.bend as Wr
import ../../../laws/auth_flight.bend as AuthFlight
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../base/logic/bool.bend as LLogicBool
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

# The call
# --------

# the reply the entry spells is the laws' reply
def ae.reply(io: F.Io) -> {FA.put_next(F.next(io)) == AuthFlight.af_reply_io(io) : String}:
  match io:
    case F.LoadFresh{}:
      {==}
    case F.LoadExpired{}:
      {==}
    case F.LoadFailed{}:
      {==}
    case F.CheckFresh{f}:
      {==}
    case F.CheckExpired{f}:
      {==}
    case F.FetchOk{f}:
      {==}
    case F.FetchFailed{f}:
      {==}
    case F.Stored{f}:
      {==}

def ae.io_of0(r: Wr.Dec<Nat>) -> {AuthFlight.af_read_io.flight(3n, r) == FA.get_io.of(0n, r) : Wr.Dec<F.Io>}:
  match r:
    case Wr.Got{f, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ae.io_of1(r: Wr.Dec<Nat>) -> {AuthFlight.af_read_io.flight(4n, r) == FA.get_io.of(1n, r) : Wr.Dec<F.Io>}:
  match r:
    case Wr.Got{f, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ae.io_of2(r: Wr.Dec<Nat>) -> {AuthFlight.af_read_io.flight(5n, r) == FA.get_io.of(2n, r) : Wr.Dec<F.Io>}:
  match r:
    case Wr.Got{f, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ae.io_of3(r: Wr.Dec<Nat>) -> {AuthFlight.af_read_io.flight(6n, r) == FA.get_io.of(3n, r) : Wr.Dec<F.Io>}:
  match r:
    case Wr.Got{f, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ae.io_of4(r: Wr.Dec<Nat>) -> {AuthFlight.af_read_io.flight(7n, r) == FA.get_io.of(4n, r) : Wr.Dec<F.Io>}:
  match r:
    case Wr.Got{f, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ae.io_bad(q: Nat, r: Wr.Dec<Nat>) -> {AuthFlight.af_read_io.flight(8n+q, r) == Wr.Bad{} : Wr.Dec<F.Io>}:
  match r:
    case Wr.Got{f, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ae.io_tag(t: Nat, s: String) -> {AuthFlight.af_read_io.tag(t, s) == FA.get_io.tag(t, s) : Wr.Dec<F.Io>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+p:
      match p:
        case 0n:
          ae.io_of0(Wr.get_nat(s))
        case 1n:
          ae.io_of1(Wr.get_nat(s))
        case 2n:
          ae.io_of2(Wr.get_nat(s))
        case 3n:
          ae.io_of3(Wr.get_nat(s))
        case 4n:
          ae.io_of4(Wr.get_nat(s))
        case 5n+q:
          ae.io_bad(q, Wr.get_nat(s))

# the entry reads every request as the laws' reader does
def ae.io(r: Wr.Dec<Nat>) -> {AuthFlight.af_read_io.go(r) == FA.get_io(r) : Wr.Dec<F.Io>}:
  match r:
    case Wr.Got{t, s}:
      ae.io_tag(t, s)
    case Wr.Bad{}:
      {==}

def ae.ffi_fin(b: Bool, +x: F.Io, -io: F.Io, got: {AuthFlight.af_whole(F.Io, b, x) == Some{io} : Maybe<&2, F.Io>}) -> {FA.ffi.fin(b, x) == AuthFlight.af_reply_io(io) : String}:
  match b:
    case True{}:
      %ae.some_inj(F.Io, x, x, io, got) : {FA.put_next(F.next(x)) == AuthFlight.af_reply_io(_) : String}
      ae.reply(x)
    case False{}:
      ae.none_some(F.Io, {FA.ffi.fin(False{}, x) == AuthFlight.af_reply_io(io) : String}, io, got)

def ae.ffi_got(r: Wr.Dec<F.Io>, -io: F.Io, got: {AuthFlight.af_read_io.whole(r) == Some{io} : Maybe<&2, F.Io>}) -> {FA.ffi.go(r) == AuthFlight.af_reply_io(io) : String}:
  match r:
    case Wr.Got{x, s}:
      ae.ffi_fin(Wr.end(s), x, io, got)
    case Wr.Bad{}:
      ae.none_some(F.Io, {FA.ffi.go(Wr.Bad{}) == AuthFlight.af_reply_io(io) : String}, io, got)

# a whole request gets the leg after its step
def ae.ffi_reads(+s: String, -io: F.Io, got: {AuthFlight.af_read_io(s) == Some{io} : Maybe<&2, F.Io>}) -> {FA.ffi(s) == AuthFlight.af_reply_io(io) : String}:
  %ae.io(Wr.get_nat(s)) : {FA.ffi.go(_) == AuthFlight.af_reply_io(io) : String}
  ae.ffi_got(AuthFlight.af_read_io.go(Wr.get_nat(s)), io, got)

def ae.ffi_bad_fin(b: Bool, -x: F.Io, no: {AuthFlight.af_whole(F.Io, b, x) == None{} : Maybe<&2, F.Io>}) -> {FA.ffi.fin(b, x) == SCon{'E', SCon{' ', "auth_flight: malformed request"}} : String}:
  match b:
    case True{}:
      ae.some_none(F.Io, {FA.ffi.fin(True{}, x) == SCon{'E', SCon{' ', "auth_flight: malformed request"}} : String}, x, no)
    case False{}:
      {==}

def ae.ffi_bad(r: Wr.Dec<F.Io>, no: {AuthFlight.af_read_io.whole(r) == None{} : Maybe<&2, F.Io>}) -> {FA.ffi.go(r) == SCon{'E', SCon{' ', "auth_flight: malformed request"}} : String}:
  match r:
    case Wr.Got{x, s}:
      ae.ffi_bad_fin(Wr.end(s), x, no)
    case Wr.Bad{}:
      {==}

# every request Rust writes reads back
def ae.read_io_spell(io: F.Io, fits: {AuthFlight.af_io_fits(io) == True{} : Bool}) -> {AuthFlight.af_read_io(AuthFlight.af_spell_io(io)) == Some{io} : Maybe<&2, F.Io>}:
  match io:
    case F.LoadFresh{}:
      {==}
    case F.LoadExpired{}:
      {==}
    case F.LoadFailed{}:
      {==}
    case F.CheckFresh{+f}:
      %LWire.pw6.nat(3n, Wr.put_nat(f, ""), {==}) : {AuthFlight.af_read_io.whole(AuthFlight.af_read_io.go(_)) == Some{F.CheckFresh{f}} : Maybe<&2, F.Io>}
      %LWire.pw6.nat(f, "", fits) : {AuthFlight.af_read_io.whole(AuthFlight.af_read_io.flight(3n, _)) == Some{F.CheckFresh{f}} : Maybe<&2, F.Io>}
      {==}
    case F.CheckExpired{+f}:
      %LWire.pw6.nat(4n, Wr.put_nat(f, ""), {==}) : {AuthFlight.af_read_io.whole(AuthFlight.af_read_io.go(_)) == Some{F.CheckExpired{f}} : Maybe<&2, F.Io>}
      %LWire.pw6.nat(f, "", fits) : {AuthFlight.af_read_io.whole(AuthFlight.af_read_io.flight(4n, _)) == Some{F.CheckExpired{f}} : Maybe<&2, F.Io>}
      {==}
    case F.FetchOk{+f}:
      %LWire.pw6.nat(5n, Wr.put_nat(f, ""), {==}) : {AuthFlight.af_read_io.whole(AuthFlight.af_read_io.go(_)) == Some{F.FetchOk{f}} : Maybe<&2, F.Io>}
      %LWire.pw6.nat(f, "", fits) : {AuthFlight.af_read_io.whole(AuthFlight.af_read_io.flight(5n, _)) == Some{F.FetchOk{f}} : Maybe<&2, F.Io>}
      {==}
    case F.FetchFailed{+f}:
      %LWire.pw6.nat(6n, Wr.put_nat(f, ""), {==}) : {AuthFlight.af_read_io.whole(AuthFlight.af_read_io.go(_)) == Some{F.FetchFailed{f}} : Maybe<&2, F.Io>}
      %LWire.pw6.nat(f, "", fits) : {AuthFlight.af_read_io.whole(AuthFlight.af_read_io.flight(6n, _)) == Some{F.FetchFailed{f}} : Maybe<&2, F.Io>}
      {==}
    case F.Stored{+f}:
      %LWire.pw6.nat(7n, Wr.put_nat(f, ""), {==}) : {AuthFlight.af_read_io.whole(AuthFlight.af_read_io.go(_)) == Some{F.Stored{f}} : Maybe<&2, F.Io>}
      %LWire.pw6.nat(f, "", fits) : {AuthFlight.af_read_io.whole(AuthFlight.af_read_io.flight(7n, _)) == Some{F.Stored{f}} : Maybe<&2, F.Io>}
      {==}

# The stepper: the reader
# -----------------------

def ae.ev_land(p: String, r: Wr.Dec<Nat>) -> {AuthFlight.af_read_ev.land(p, r) == FA.get_ev.land(p, r) : Wr.Dec<F.BEv>}:
  match r:
    case Wr.Got{f, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ae.ev_board(r: Wr.Dec<String>) -> {AuthFlight.af_read_ev.board(r) == FA.get_ev.named(0n, r) : Wr.Dec<F.BEv>}:
  match r:
    case Wr.Got{p, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ae.ev_landed(r: Wr.Dec<String>) -> {AuthFlight.af_read_ev.landed(r) == FA.get_ev.named(1n, r) : Wr.Dec<F.BEv>}:
  match r:
    case Wr.Got{p, s}:
      ae.ev_land(p, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def ae.ev_wait(r: Wr.Dec<Nat>) -> {AuthFlight.af_read_ev.wait(r) == FA.get_ev.wait(r) : Wr.Dec<F.BEv>}:
  match r:
    case Wr.Got{f, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ae.ev_joiners(r: Wr.Dec<String>) -> {AuthFlight.af_read_ev.joiners(r) == FA.get_ev.named(2n, r) : Wr.Dec<F.BEv>}:
  match r:
    case Wr.Got{p, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ae.ev_tag(t: Nat, s: String) -> {AuthFlight.af_read_ev.tag(t, s) == FA.get_ev.tag(t, s) : Wr.Dec<F.BEv>}:
  match t:
    case 0n:
      ae.ev_board(Wr.get_str(s))
    case 1n:
      ae.ev_landed(Wr.get_str(s))
    case 2n:
      ae.ev_wait(Wr.get_nat(s))
    case 3n:
      ae.ev_joiners(Wr.get_str(s))
    case 4n+p:
      {==}

# the entry reads every event as the laws' reader does
def ae.ev(r: Wr.Dec<Nat>) -> {AuthFlight.af_read_ev.go(r) == FA.get_ev(r) : Wr.Dec<F.BEv>}:
  match r:
    case Wr.Got{t, s}:
      ae.ev_tag(t, s)
    case Wr.Bad{}:
      {==}

# every event Rust writes reads back
def ae.read_ev_spell(e: F.BEv, +fits: {AuthFlight.af_ev_fits(e) == True{} : Bool}) -> {AuthFlight.af_read_ev(AuthFlight.af_spell_ev(e)) == Some{e} : Maybe<&2, F.BEv>}:
  match e:
    case F.EvBoard{+p}:
      %LWire.pw6.nat(0n, Wr.put_str(p, ""), {==}) : {AuthFlight.af_read_ev.whole(AuthFlight.af_read_ev.go(_)) == Some{F.EvBoard{p}} : Maybe<&2, F.BEv>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(p, "")), Wr.Got{p, ""}, Wire.wire_str_round_trip(p, "", fits)) : {AuthFlight.af_read_ev.whole(AuthFlight.af_read_ev.board(_)) == Some{F.EvBoard{p}} : Maybe<&2, F.BEv>}
      {==}
    case F.EvLand{+p, +f}:
      +hp = LLogicBool.wr_and_l(LawsBase.wire_fits(String.length(p)), LawsBase.wire_fits(f), fits)
      +hf = LLogicBool.wr_and_r(LawsBase.wire_fits(String.length(p)), LawsBase.wire_fits(f), fits)
      %LWire.pw6.nat(1n, Wr.put_str(p, Wr.put_nat(f, "")), {==}) : {AuthFlight.af_read_ev.whole(AuthFlight.af_read_ev.go(_)) == Some{F.EvLand{p, f}} : Maybe<&2, F.BEv>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(p, Wr.put_nat(f, ""))), Wr.Got{p, Wr.put_nat(f, "")}, Wire.wire_str_round_trip(p, Wr.put_nat(f, ""), hp)) : {AuthFlight.af_read_ev.whole(AuthFlight.af_read_ev.landed(_)) == Some{F.EvLand{p, f}} : Maybe<&2, F.BEv>}
      %LWire.pw6.nat(f, "", hf) : {AuthFlight.af_read_ev.whole(AuthFlight.af_read_ev.land(p, _)) == Some{F.EvLand{p, f}} : Maybe<&2, F.BEv>}
      {==}
    case F.EvWait{+f}:
      %LWire.pw6.nat(2n, Wr.put_nat(f, ""), {==}) : {AuthFlight.af_read_ev.whole(AuthFlight.af_read_ev.go(_)) == Some{F.EvWait{f}} : Maybe<&2, F.BEv>}
      %LWire.pw6.nat(f, "", fits) : {AuthFlight.af_read_ev.whole(AuthFlight.af_read_ev.wait(_)) == Some{F.EvWait{f}} : Maybe<&2, F.BEv>}
      {==}
    case F.EvJoiners{+p}:
      %LWire.pw6.nat(3n, Wr.put_str(p, ""), {==}) : {AuthFlight.af_read_ev.whole(AuthFlight.af_read_ev.go(_)) == Some{F.EvJoiners{p}} : Maybe<&2, F.BEv>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(p, "")), Wr.Got{p, ""}, Wire.wire_str_round_trip(p, "", fits)) : {AuthFlight.af_read_ev.whole(AuthFlight.af_read_ev.joiners(_)) == Some{F.EvJoiners{p}} : Maybe<&2, F.BEv>}
      {==}

# The stepper: the book
# ---------------------

def ae.fly_find_at(hit: Bool, x: F.Fly, r: Maybe<&2, F.Fly>) -> {F.fly.find.at(hit, x, r) == AuthFlight.af_fly.pick(hit, x, r) : Maybe<&2, F.Fly>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def ae.fly_find(+p: String, fs: List<&2, F.Fly>) -> {F.fly.find(p, fs) == AuthFlight.af_fly(p, fs) : Maybe<&2, F.Fly>}:
  match fs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Fly{+q, +f, +j}:
          %ae.fly_find(p, t) : {F.fly.find.at(String.eq(q, p), F.Fly{q, f, j}, F.fly.find(p, t)) == AuthFlight.af_fly.pick(String.eq(q, p), F.Fly{q, f, j}, _) : Maybe<&2, F.Fly>}
          ae.fly_find_at(String.eq(q, p), F.Fly{q, f, j}, F.fly.find(p, t))

def ae.fly_join_at(hit: Bool, x: F.Fly, t: List<&2, F.Fly>, r: List<&2, F.Fly>) -> {F.fly.join.at(hit, x, t, r) == AuthFlight.af_bump.pick(hit, x, t, r) : List<&2, F.Fly>}:
  match hit:
    case True{}:
      match x:
        case F.Fly{q, f, j}:
          {==}
    case False{}:
      {==}

def ae.fly_join(+p: String, fs: List<&2, F.Fly>) -> {F.fly.join(p, fs) == AuthFlight.af_bump(p, fs) : List<&2, F.Fly>}:
  match fs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Fly{+q, +f, +j}:
          %ae.fly_join(p, t) : {F.fly.join.at(String.eq(q, p), F.Fly{q, f, j}, t, F.fly.join(p, t)) == AuthFlight.af_bump.pick(String.eq(q, p), F.Fly{q, f, j}, t, _) : List<&2, F.Fly>}
          ae.fly_join_at(String.eq(q, p), F.Fly{q, f, j}, t, F.fly.join(p, t))

def ae.fly_drop_at(hit: Bool, x: F.Fly, t: List<&2, F.Fly>, r: List<&2, F.Fly>) -> {F.fly.drop.at(hit, x, t, r) == AuthFlight.af_unfly.pick(hit, x, t, r) : List<&2, F.Fly>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def ae.fly_drop(+p: String, fs: List<&2, F.Fly>) -> {F.fly.drop(p, fs) == AuthFlight.af_unfly(p, fs) : List<&2, F.Fly>}:
  match fs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Fly{+q, +f, +j}:
          %ae.fly_drop(p, t) : {F.fly.drop.at(String.eq(q, p), F.Fly{q, f, j}, t, F.fly.drop(p, t)) == AuthFlight.af_unfly.pick(String.eq(q, p), F.Fly{q, f, j}, t, _) : List<&2, F.Fly>}
          ae.fly_drop_at(String.eq(q, p), F.Fly{q, f, j}, t, F.fly.drop(p, t))

def ae.lnd_find_at(hit: Bool, x: F.Lnd, r: Maybe<&2, F.Lnd>) -> {F.lnd.find.at(hit, x, r) == AuthFlight.af_landed.pick(hit, x, r) : Maybe<&2, F.Lnd>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def ae.lnd_find(+f: Nat, ls: List<&2, F.Lnd>) -> {F.lnd.find(f, ls) == AuthFlight.af_landed(f, ls) : Maybe<&2, F.Lnd>}:
  match ls:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Lnd{+g, +w}:
          %ae.lnd_find(f, t) : {F.lnd.find.at(Nat.is_eq(g, f), F.Lnd{g, w}, F.lnd.find(f, t)) == AuthFlight.af_landed.pick(Nat.is_eq(g, f), F.Lnd{g, w}, _) : Maybe<&2, F.Lnd>}
          ae.lnd_find_at(Nat.is_eq(g, f), F.Lnd{g, w}, F.lnd.find(f, t))

def ae.lnd_less_at(hit: Bool, x: F.Lnd, t: List<&2, F.Lnd>, r: List<&2, F.Lnd>) -> {F.lnd.less.at(hit, x, t, r) == AuthFlight.af_one_less.pick(hit, x, t, r) : List<&2, F.Lnd>}:
  match hit:
    case True{}:
      match x:
        case F.Lnd{g, w}:
          {==}
    case False{}:
      {==}

def ae.lnd_less(+f: Nat, ls: List<&2, F.Lnd>) -> {F.lnd.less(f, ls) == AuthFlight.af_one_less(f, ls) : List<&2, F.Lnd>}:
  match ls:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Lnd{+g, +w}:
          %ae.lnd_less(f, t) : {F.lnd.less.at(Nat.is_eq(g, f), F.Lnd{g, w}, t, F.lnd.less(f, t)) == AuthFlight.af_one_less.pick(Nat.is_eq(g, f), F.Lnd{g, w}, t, _) : List<&2, F.Lnd>}
          ae.lnd_less_at(Nat.is_eq(g, f), F.Lnd{g, w}, t, F.lnd.less(f, t))

def ae.lnd_drop_at(hit: Bool, x: F.Lnd, t: List<&2, F.Lnd>, r: List<&2, F.Lnd>) -> {F.lnd.drop.at(hit, x, t, r) == AuthFlight.af_unland.pick(hit, x, t, r) : List<&2, F.Lnd>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def ae.lnd_drop(+f: Nat, ls: List<&2, F.Lnd>) -> {F.lnd.drop(f, ls) == AuthFlight.af_unland(f, ls) : List<&2, F.Lnd>}:
  match ls:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Lnd{+g, +w}:
          %ae.lnd_drop(f, t) : {F.lnd.drop.at(Nat.is_eq(g, f), F.Lnd{g, w}, t, F.lnd.drop(f, t)) == AuthFlight.af_unland.pick(Nat.is_eq(g, f), F.Lnd{g, w}, t, _) : List<&2, F.Lnd>}
          ae.lnd_drop_at(Nat.is_eq(g, f), F.Lnd{g, w}, t, F.lnd.drop(f, t))

def ae.board(m: Maybe<&2, F.Fly>, +p: String, +fs: List<&2, F.Fly>, ls: List<&2, F.Lnd>, +n: Nat) -> {F.book.board(m, p, fs, ls, n) == AuthFlight.af_board(m, p, fs, ls, n) : F.BRes}:
  match m:
    case Some{x}:
      match x:
        case F.Fly{q, f, j}:
          %ae.fly_join(p, fs) : {F.BRes{F.Book{F.fly.join(p, fs), ls, n}, F.OJoin{f}} == F.BRes{F.Book{_, ls, n}, F.OJoin{f}} : F.BRes}
          {==}
    case None{}:
      {==}

def ae.land(m: Maybe<&2, F.Fly>, +p: String, +f: Nat, +fs: List<&2, F.Fly>, +ls: List<&2, F.Lnd>, n: Nat) -> {F.book.land(m, p, f, fs, ls, n) == AuthFlight.af_land(m, p, f, fs, ls, n) : F.BRes}:
  match m:
    case Some{x}:
      match x:
        case F.Fly{q, g, j}:
          match j:
            case 0n:
              %ae.fly_drop(p, fs) : {F.BRes{F.Book{F.fly.drop(p, fs), ls, n}, F.ODropped{}} == F.BRes{F.Book{_, ls, n}, F.ODropped{}} : F.BRes}
              {==}
            case 1n+i:
              %ae.fly_drop(p, fs) : {F.BRes{F.Book{F.fly.drop(p, fs), F.Lnd{f, 1n+i} <> F.lnd.drop(f, ls), n}, F.OKept{}} == F.BRes{F.Book{_, F.Lnd{f, 1n+i} <> AuthFlight.af_unland(f, ls), n}, F.OKept{}} : F.BRes}
              %ae.lnd_drop(f, ls) : {F.BRes{F.Book{F.fly.drop(p, fs), F.Lnd{f, 1n+i} <> F.lnd.drop(f, ls), n}, F.OKept{}} == F.BRes{F.Book{F.fly.drop(p, fs), F.Lnd{f, 1n+i} <> _, n}, F.OKept{}} : F.BRes}
              {==}
    case None{}:
      {==}

def ae.wait(m: Maybe<&2, F.Lnd>, +f: Nat, fs: List<&2, F.Fly>, +ls: List<&2, F.Lnd>, n: Nat) -> {F.book.wait(m, f, fs, ls, n) == AuthFlight.af_wait(m, f, fs, ls, n) : F.BRes}:
  match m:
    case Some{x}:
      match x:
        case F.Lnd{g, w}:
          match w:
            case 0n:
              %ae.lnd_drop(f, ls) : {F.BRes{F.Book{fs, F.lnd.drop(f, ls), n}, F.OTakeLast{}} == F.BRes{F.Book{fs, _, n}, F.OTakeLast{}} : F.BRes}
              {==}
            case 1n:
              %ae.lnd_drop(f, ls) : {F.BRes{F.Book{fs, F.lnd.drop(f, ls), n}, F.OTakeLast{}} == F.BRes{F.Book{fs, _, n}, F.OTakeLast{}} : F.BRes}
              {==}
            case 2n+v:
              %ae.lnd_less(f, ls) : {F.BRes{F.Book{fs, F.lnd.less(f, ls), n}, F.OTake{}} == F.BRes{F.Book{fs, _, n}, F.OTake{}} : F.BRes}
              {==}
    case None{}:
      {==}

def ae.joiners(m: Maybe<&2, F.Fly>) -> {F.book.joiners(m) == AuthFlight.af_joiners(m) : F.BOut}:
  match m:
    case Some{x}:
      match x:
        case F.Fly{q, f, j}:
          {==}
    case None{}:
      {==}

# the entry's book is the laws' book
def ae.book(b: F.Book, e: F.BEv) -> {F.book.step(b, e) == AuthFlight.af_book(b, e) : F.BRes}:
  match b:
    case F.Book{+fs, +ls, +n}:
      match e:
        case F.EvBoard{+p}:
          %ae.fly_find(p, fs) : {F.book.board(F.fly.find(p, fs), p, fs, ls, n) == AuthFlight.af_board(_, p, fs, ls, n) : F.BRes}
          ae.board(F.fly.find(p, fs), p, fs, ls, n)
        case F.EvLand{+p, +f}:
          %ae.fly_find(p, fs) : {F.book.land(F.fly.find(p, fs), p, f, fs, ls, n) == AuthFlight.af_land(_, p, f, fs, ls, n) : F.BRes}
          ae.land(F.fly.find(p, fs), p, f, fs, ls, n)
        case F.EvWait{+f}:
          %ae.lnd_find(f, ls) : {F.book.wait(F.lnd.find(f, ls), f, fs, ls, n) == AuthFlight.af_wait(_, f, fs, ls, n) : F.BRes}
          ae.wait(F.lnd.find(f, ls), f, fs, ls, n)
        case F.EvJoiners{+p}:
          %ae.fly_find(p, fs) : {F.BRes{F.Book{fs, ls, n}, F.book.joiners(F.fly.find(p, fs))} == F.BRes{F.Book{fs, ls, n}, AuthFlight.af_joiners(_)} : F.BRes}
          %ae.joiners(F.fly.find(p, fs)) : {F.BRes{F.Book{fs, ls, n}, F.book.joiners(F.fly.find(p, fs))} == F.BRes{F.Book{fs, ls, n}, _} : F.BRes}
          {==}

# The stepper: the reply
# ----------------------

def ae.out(o: F.BOut) -> {FA.put_out(o) == AuthFlight.af_spell_out(o) : String}:
  match o:
    case F.OLead{f}:
      {==}
    case F.OJoin{f}:
      {==}
    case F.OKept{}:
      {==}
    case F.ODropped{}:
      {==}
    case F.ONotYet{}:
      {==}
    case F.OTake{}:
      {==}
    case F.OTakeLast{}:
      {==}
    case F.OJoiners{m}:
      match m:
        case None{}:
          {==}
        case Some{j}:
          {==}

def ae.put(r: F.BRes) -> {FA.step.put(r) == AuthFlight.af_step_of(r) : FA.St & String}:
  match r:
    case F.BRes{+b, o}:
      %ae.out(o) : {(FA.Open{b}, FA.put_out(o)) == (FA.Open{b}, _) : FA.St & String}
      {==}

def ae.step_fin(d: Bool, +b: F.Book, +x: F.BEv, -e: F.BEv, got: {AuthFlight.af_whole(F.BEv, d, x) == Some{e} : Maybe<&2, F.BEv>}) -> {FA.step.fin(d, b, x) == AuthFlight.af_step_of(AuthFlight.af_book(b, e)) : FA.St & String}:
  match d:
    case True{}:
      %ae.some_inj(F.BEv, x, x, e, got) : {FA.step.put(F.book.step(b, x)) == AuthFlight.af_step_of(AuthFlight.af_book(b, _)) : FA.St & String}
      %ae.book(b, x) : {FA.step.put(F.book.step(b, x)) == AuthFlight.af_step_of(_) : FA.St & String}
      ae.put(F.book.step(b, x))
    case False{}:
      ae.none_some(F.BEv, {FA.step.fin(False{}, b, x) == AuthFlight.af_step_of(AuthFlight.af_book(b, e)) : FA.St & String}, e, got)

def ae.step_got(r: Wr.Dec<F.BEv>, +b: F.Book, -e: F.BEv, got: {AuthFlight.af_read_ev.whole(r) == Some{e} : Maybe<&2, F.BEv>}) -> {FA.step.go(b, r) == AuthFlight.af_step_of(AuthFlight.af_book(b, e)) : FA.St & String}:
  match r:
    case Wr.Got{x, s}:
      ae.step_fin(Wr.end(s), b, x, e, got)
    case Wr.Bad{}:
      ae.none_some(F.BEv, {FA.step.go(b, Wr.Bad{}) == AuthFlight.af_step_of(AuthFlight.af_book(b, e)) : FA.St & String}, e, got)

# a whole event gets the book's answer
def ae.step_reads(+b: F.Book, +s: String, -e: F.BEv, got: {AuthFlight.af_read_ev(s) == Some{e} : Maybe<&2, F.BEv>}) -> {FA.step(FA.Open{b}, s) == AuthFlight.af_step_of(AuthFlight.af_book(b, e)) : FA.St & String}:
  %ae.ev(Wr.get_nat(s)) : {FA.step.go(b, _) == AuthFlight.af_step_of(AuthFlight.af_book(b, e)) : FA.St & String}
  ae.step_got(AuthFlight.af_read_ev.go(Wr.get_nat(s)), b, e, got)

def ae.step_bad_fin(d: Bool, +b: F.Book, -x: F.BEv, no: {AuthFlight.af_whole(F.BEv, d, x) == None{} : Maybe<&2, F.BEv>}) -> {FA.step.fin(d, b, x) == (FA.Open{b}, SCon{'E', SCon{' ', "auth_flight: malformed event"}}) : FA.St & String}:
  match d:
    case True{}:
      ae.some_none(F.BEv, {FA.step.fin(True{}, b, x) == (FA.Open{b}, SCon{'E', SCon{' ', "auth_flight: malformed event"}}) : FA.St & String}, x, no)
    case False{}:
      {==}

def ae.step_bad(r: Wr.Dec<F.BEv>, +b: F.Book, no: {AuthFlight.af_read_ev.whole(r) == None{} : Maybe<&2, F.BEv>}) -> {FA.step.go(b, r) == (FA.Open{b}, SCon{'E', SCon{' ', "auth_flight: malformed event"}}) : FA.St & String}:
  match r:
    case Wr.Got{x, s}:
      ae.step_bad_fin(Wr.end(s), b, x, no)
    case Wr.Bad{}:
      {==}
