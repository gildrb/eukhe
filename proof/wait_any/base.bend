# eukhe: lemmas the proofs of area wait_any share: Nat facts and the cap;
# the route; what is left to deliver (the laws' count of the code's
# steps); a spelled request that fits reads back whole through the
# entry's decoder

import Base
import ../../bend/wait_any.bend as Wa
import ../../bend/ffi_wait_any.bend as FWa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/wait_any.bend as WaitAny
import ../../spec/durable/wait_any.bend as WaSpec
import ../../spec/durable/wait_any_wire.bend as SpW
import ../base/staging.bend as LStg
import ../base/wire.bend as LWire
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip

# Nat
# ---

def wa.add_zero_r(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %wa.add_zero_r(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def wa.add_succ_r(n: Nat, +m: Nat) -> {Nat.add(n, 1n+m) == 1n+Nat.add(n, m) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %wa.add_succ_r(p, m) : {1n+Nat.add(p, 1n+m) == 1n+_ : Nat}
      {==}

# the first of a and b as c says
def wa.pick(c: Bool, a: Nat, b: Nat) -> Nat:
  match c:
    case True{}:
      a
    case False{}:
      b

def wa.pick_succ(c: Bool, a: Nat, b: Nat) -> {wa.pick(c, 1n+a, 1n+b) == 1n+wa.pick(c, a, b) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# the min is the smaller one
def wa.min_pick(+a: Nat, +b: Nat) -> {Nat.min(a, b) == wa.pick(Nat.is_le(a, b), a, b) : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      %Equal.sym(Nat, wa.pick(Nat.is_le(p, q), 1n+p, 1n+q), 1n+wa.pick(Nat.is_le(p, q), p, q), wa.pick_succ(Nat.is_le(p, q), p, q)) : {1n+Nat.min(p, q) == _ : Nat}
      %wa.min_pick(p, q) : {1n+Nat.min(p, q) == 1n+_ : Nat}
      {==}

def wa.pick_cap(c: Bool, t: Nat) -> {wa.pick(c, t, 1800n) == WaSpec.timeout.of(c, t) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def wa.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      wa.le_refl(p)

def wa.le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# the min is at most its right side
def wa.min_le_r(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}:
  match a b:
    case 0n q:
      wa.le_zero(q)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      wa.min_le_r(p, q)

# at most none is at most one
def wa.le01(n: Nat, h: {Nat.is_le(n, 0n) == True{} : Bool}) -> {Nat.is_le(n, 1n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      LStg.stg.absurdF({Nat.is_le(1n+p, 1n) == True{} : Bool}, h)

# S3: the route
def wa.route_eq(watched: Bool, wake: Bool) -> {Wa.route(watched, wake) == WaSpec.route(watched, wake) : Wa.Route}:
  match watched:
    case True{}:
      {==}
    case False{}:
      match wake:
        case True{}:
          {==}
        case False{}:
          {==}

# R4: what is left to deliver
# ---------------------------

# the deliveries a job in phase p may still make: one until it is sent
def wa.left(d: Wa.D) -> Nat:
  match d:
    case Wa.D{+w, p}:
      match p:
        case Wa.Live{}:
          1n
        case Wa.Kept{}:
          1n
        case Wa.Sent{}:
          0n

# a delivery state of w watchers placed as route r says
def wa.after_route(r: Wa.Route, +w: Nat, rest: List<&2, Wa.Ev>, +wake: Bool,
  ih: @d: Wa.D -> {Nat.is_le(WaitAny.wa_count(rest, wake, d), wa.left(d)) == True{} : Bool})
  -> {Nat.is_le(Nat.add(WaSpec.out_k(Wa.deliver(r, w)), WaitAny.wa_count(rest, wake, WaSpec.out_d(Wa.deliver(r, w)))), 1n) == True{} : Bool}:
  match r:
    case Wa.ToWaiter{}:
      ih(Wa.D{w, Wa.Kept{}})
    case Wa.ToNotice{}:
      ih(Wa.D{w, Wa.Sent{}})

# no events deliver more than what is left, counted on the laws' side
def wa.once_go(es: List<&2, Wa.Ev>, +wake: Bool, d: Wa.D) -> {Nat.is_le(WaitAny.wa_count(es, wake, d), wa.left(d)) == True{} : Bool}:
  match es:
    case Nil{}:
      wa.le_zero(wa.left(d))
    case Con{e, +rest}:
      match e:
        case Wa.Watch{}:
          match d:
            case Wa.D{+w, p}:
              match p:
                case Wa.Live{}:
                  wa.once_go(rest, wake, Wa.D{1n+w, Wa.Live{}})
                case Wa.Kept{}:
                  wa.once_go(rest, wake, Wa.D{1n+w, Wa.Kept{}})
                case Wa.Sent{}:
                  wa.once_go(rest, wake, Wa.D{1n+w, Wa.Sent{}})
        case Wa.Unwatch{}:
          match d:
            case Wa.D{+w, p}:
              match p:
                case Wa.Live{}:
                  wa.once_go(rest, wake, Wa.D{Wa.unwatch.left(w), Wa.Live{}})
                case Wa.Kept{}:
                  wa.after_route(Wa.route(Wa.watched(Wa.unwatch.left(w)), wake), Wa.unwatch.left(w), rest, wake, dd => wa.once_go(rest, wake, dd))
                case Wa.Sent{}:
                  wa.once_go(rest, wake, Wa.D{Wa.unwatch.left(w), Wa.Sent{}})
        case Wa.Settles{}:
          match d:
            case Wa.D{+w, p}:
              match p:
                case Wa.Live{}:
                  wa.after_route(Wa.route(Wa.watched(w), wake), w, rest, wake, dd => wa.once_go(rest, wake, dd))
                case Wa.Kept{}:
                  wa.once_go(rest, wake, Wa.D{w, Wa.Kept{}})
                case Wa.Sent{}:
                  wa.once_go(rest, wake, Wa.D{w, Wa.Sent{}})
        case Wa.Taken{}:
          match d:
            case Wa.D{+w, p}:
              match p:
                case Wa.Live{}:
                  wa.once_go(rest, wake, Wa.D{w, Wa.Live{}})
                case Wa.Kept{}:
                  wa.once_go(rest, wake, Wa.D{w, Wa.Sent{}})
                case Wa.Sent{}:
                  wa.once_go(rest, wake, Wa.D{w, Wa.Sent{}})

# Read back (R5): the entry's decoder reads a spelled request
# ------------------------------------------------------------

# the target codes read back as the targets
def wa.tgts_back(ts: List<&2, Wa.Tgt>) -> {FWa.tgts(SpW.c_tgts(ts)) == Some{ts} : Maybe<&2, List<&2, Wa.Tgt>>}:
  match ts:
    case Nil{}:
      {==}
    case Con{t, +rest}:
      match t:
        case Wa.Runs{}:
          %Equal.sym(Maybe<&2, List<&2, Wa.Tgt>>, FWa.tgts(SpW.c_tgts(rest)), Some{rest}, wa.tgts_back(rest)) : {FWa.tgts.cons(Some{Wa.Runs{}}, _) == Some{Wa.Runs{} <> rest} : Maybe<&2, List<&2, Wa.Tgt>>}
          {==}
        case Wa.Unread{}:
          %Equal.sym(Maybe<&2, List<&2, Wa.Tgt>>, FWa.tgts(SpW.c_tgts(rest)), Some{rest}, wa.tgts_back(rest)) : {FWa.tgts.cons(Some{Wa.Unread{}}, _) == Some{Wa.Unread{} <> rest} : Maybe<&2, List<&2, Wa.Tgt>>}
          {==}
        case Wa.Read{}:
          %Equal.sym(Maybe<&2, List<&2, Wa.Tgt>>, FWa.tgts(SpW.c_tgts(rest)), Some{rest}, wa.tgts_back(rest)) : {FWa.tgts.cons(Some{Wa.Read{}}, _) == Some{Wa.Read{} <> rest} : Maybe<&2, List<&2, Wa.Tgt>>}
          {==}

# a target's code fits the wire
def wa.tgt_fits(t: Wa.Tgt) -> {LawsBase.wire_fits(SpW.c_tgt(t)) == True{} : Bool}:
  match t:
    case Wa.Runs{}:
      {==}
    case Wa.Unread{}:
      {==}
    case Wa.Read{}:
      {==}

# every target code fits the wire
def wa.tgts_fit(ts: List<&2, Wa.Tgt>) -> {LawsBase.wire_nats_fit(SpW.c_tgts(ts)) == True{} : Bool}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, rest}:
      %Equal.sym(Bool, LawsBase.wire_fits(SpW.c_tgt(t)), True{}, wa.tgt_fits(t)) : {Bool.and(_, LawsBase.wire_nats_fit(SpW.c_tgts(rest))) == True{} : Bool}
      wa.tgts_fit(rest)

# there are as many codes as targets
def wa.tgts_len(ts: List<&2, Wa.Tgt>) -> {List.length(&2, Nat, SpW.c_tgts(ts)) == List.length(&2, Wa.Tgt, ts) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case Con{t, rest}:
      %wa.tgts_len(rest) : {1n+List.length(&2, Nat, SpW.c_tgts(rest)) == 1n+_ : Nat}
      {==}

# the codes of the targets of a request that fits fit the wire, their
# count too
def wa.list_fit(+ts: List<&2, Wa.Tgt>, h: {LawsBase.wire_fits(List.length(&2, Wa.Tgt, ts)) == True{} : Bool}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, SpW.c_tgts(ts))), LawsBase.wire_nats_fit(SpW.c_tgts(ts))) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Nat, SpW.c_tgts(ts)), List.length(&2, Wa.Tgt, ts), wa.tgts_len(ts)) : {Bool.and(LawsBase.wire_fits(_), LawsBase.wire_nats_fit(SpW.c_tgts(ts))) == True{} : Bool}
  %Equal.sym(Bool, LawsBase.wire_fits(List.length(&2, Wa.Tgt, ts)), True{}, h) : {Bool.and(_, LawsBase.wire_nats_fit(SpW.c_tgts(ts))) == True{} : Bool}
  wa.tgts_fit(ts)

# a phase's code fits the wire and reads back
def wa.phase_fits(p: Wa.Phase) -> {LawsBase.wire_fits(SpW.c_phase(p)) == True{} : Bool}:
  match p:
    case Wa.Live{}:
      {==}
    case Wa.Kept{}:
      {==}
    case Wa.Sent{}:
      {==}

def wa.phase_back(p: Wa.Phase) -> {FWa.phase_of(SpW.c_phase(p)) == Some{p} : Maybe<&2, Wa.Phase>}:
  match p:
    case Wa.Live{}:
      {==}
    case Wa.Kept{}:
      {==}
    case Wa.Sent{}:
      {==}

# an event's code fits the wire and reads back
def wa.ev_fits(e: Wa.Ev) -> {LawsBase.wire_fits(SpW.c_ev(e)) == True{} : Bool}:
  match e:
    case Wa.Watch{}:
      {==}
    case Wa.Unwatch{}:
      {==}
    case Wa.Settles{}:
      {==}
    case Wa.Taken{}:
      {==}

def wa.ev_back(e: Wa.Ev) -> {FWa.ev_of(SpW.c_ev(e)) == Some{e} : Maybe<&2, Wa.Ev>}:
  match e:
    case Wa.Watch{}:
      {==}
    case Wa.Unwatch{}:
      {==}
    case Wa.Settles{}:
      {==}
    case Wa.Taken{}:
      {==}

def wa.nat_rt(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

def wa.bool_rt(+b: Bool, +rest: String) -> {Wr.Got{b, rest} == Wr.get_bool(Wr.put_bool(b, rest)) : Wr.Dec<Bool>}:
  Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, rest)), Wr.Got{b, rest}, Wire.wire_bool_round_trip(b, rest))

# a poll request that fits reads back, and the rest is untouched
def wa.poll_rt(+n: Bool, +c: Bool, +l: Bool, +ts: List<&2, Wa.Tgt>, +rest: String, h: {LawsBase.wire_fits(List.length(&2, Wa.Tgt, ts)) == True{} : Bool}) -> {FWa.get_req(SpW.w_req(FWa.QPoll{n, c, l, ts}, rest)) == Wr.Got{FWa.QPoll{n, c, l, ts}, rest} : Wr.Dec<FWa.Req>}:
  +cs = SpW.c_tgts(ts)
  +r4 = Wr.put_list(~Nat, ~Wr.put_nat, cs, rest)
  +r3 = Wr.put_bool(l, r4)
  +r2 = Wr.put_bool(c, r3)
  +r1 = Wr.put_bool(n, r2)
  -g = {Wr.Got{FWa.QPoll{n, c, l, ts}, rest} : Wr.Dec<FWa.Req>}
  %wa.nat_rt(0n, r1, {==}) : {FWa.get_req.start(_) == g : Wr.Dec<FWa.Req>}
  %wa.bool_rt(n, r2) : {FWa.get_poll(_) == g : Wr.Dec<FWa.Req>}
  %wa.bool_rt(c, r3) : {FWa.get_poll.cancel(n, _) == g : Wr.Dec<FWa.Req>}
  %wa.bool_rt(l, r4) : {FWa.get_poll.late(n, c, _) == g : Wr.Dec<FWa.Req>}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, r4), Wr.Got{cs, rest}, Wire.wire_list_round_trip(cs, rest, wa.list_fit(ts, h))) : {FWa.get_poll.ts(n, c, l, _) == g : Wr.Dec<FWa.Req>}
  %Equal.sym(Maybe<&2, List<&2, Wa.Tgt>>, FWa.tgts(cs), Some{ts}, wa.tgts_back(ts)) : {FWa.get_poll.ok(n, c, l, _, rest) == g : Wr.Dec<FWa.Req>}
  {==}

# a step request that fits reads back, and the rest is untouched
def wa.step_rt(+k: Bool, +w: Nat, +p: Wa.Phase, +e: Wa.Ev, +rest: String, h: {LawsBase.wire_fits(w) == True{} : Bool}) -> {FWa.get_req(SpW.w_req(FWa.QStep{k, Wa.D{w, p}, e}, rest)) == Wr.Got{FWa.QStep{k, Wa.D{w, p}, e}, rest} : Wr.Dec<FWa.Req>}:
  +r4 = Wr.put_nat(SpW.c_ev(e), rest)
  +r3 = Wr.put_nat(SpW.c_phase(p), r4)
  +r2 = Wr.put_nat(w, r3)
  +r1 = Wr.put_bool(k, r2)
  -g = {Wr.Got{FWa.QStep{k, Wa.D{w, p}, e}, rest} : Wr.Dec<FWa.Req>}
  %wa.nat_rt(1n, r1, {==}) : {FWa.get_req.start(_) == g : Wr.Dec<FWa.Req>}
  %wa.bool_rt(k, r2) : {FWa.get_step(_) == g : Wr.Dec<FWa.Req>}
  %wa.nat_rt(w, r3, h) : {FWa.get_step.watchers(k, _) == g : Wr.Dec<FWa.Req>}
  %wa.nat_rt(SpW.c_phase(p), r4, wa.phase_fits(p)) : {FWa.get_step.phase(k, w, _) == g : Wr.Dec<FWa.Req>}
  %wa.nat_rt(SpW.c_ev(e), rest, wa.ev_fits(e)) : {FWa.get_step.ev(k, w, SpW.c_phase(p), _) == g : Wr.Dec<FWa.Req>}
  %Equal.sym(Maybe<&2, Wa.Phase>, FWa.phase_of(SpW.c_phase(p)), Some{p}, wa.phase_back(p)) : {FWa.get_step.ok(k, w, _, FWa.ev_of(SpW.c_ev(e)), rest) == g : Wr.Dec<FWa.Req>}
  %Equal.sym(Maybe<&2, Wa.Ev>, FWa.ev_of(SpW.c_ev(e)), Some{e}, wa.ev_back(e)) : {FWa.get_step.ok(k, w, Some{p}, _, rest) == g : Wr.Dec<FWa.Req>}
  {==}

# a timeout request that fits reads back, and the rest is untouched
def wa.timeout_rt(+a: Maybe<&2, Nat>, +rest: String, h: {SpW.fit_asked(a) == True{} : Bool}) -> {FWa.get_req(SpW.w_req(FWa.QTimeout{a}, rest)) == Wr.Got{FWa.QTimeout{a}, rest} : Wr.Dec<FWa.Req>}:
  match a:
    case None{}:
      +r1 = Wr.put_nat(0n, rest)
      %wa.nat_rt(2n, r1, {==}) : {FWa.get_req.start(_) == Wr.Got{FWa.QTimeout{None{}}, rest} : Wr.Dec<FWa.Req>}
      %wa.nat_rt(0n, rest, {==}) : {FWa.get_timeout(_) == Wr.Got{FWa.QTimeout{None{}}, rest} : Wr.Dec<FWa.Req>}
      {==}
    case Some{+t}:
      +r2 = Wr.put_nat(t, rest)
      +r1 = Wr.put_nat(1n, r2)
      %wa.nat_rt(2n, r1, {==}) : {FWa.get_req.start(_) == Wr.Got{FWa.QTimeout{Some{t}}, rest} : Wr.Dec<FWa.Req>}
      %wa.nat_rt(1n, r2, {==}) : {FWa.get_timeout(_) == Wr.Got{FWa.QTimeout{Some{t}}, rest} : Wr.Dec<FWa.Req>}
      %wa.nat_rt(t, rest, h) : {FWa.get_timeout.ms(_) == Wr.Got{FWa.QTimeout{Some{t}}, rest} : Wr.Dec<FWa.Req>}
      {==}

# a spelled request that fits reads back through the entry's decoder,
# and the rest is untouched
def wa.req_rt(+q: FWa.Req, +rest: String, h: {SpW.fit(q) == True{} : Bool}) -> {FWa.get_req(SpW.w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FWa.Req>}:
  match q:
    case FWa.QPoll{+n, +c, +l, +ts}:
      wa.poll_rt(n, c, l, ts, rest, h)
    case FWa.QStep{+k, d, +e}:
      match d:
        case Wa.D{+w, +p}:
          wa.step_rt(k, w, p, e, rest, h)
    case FWa.QTimeout{+a}:
      wa.timeout_rt(a, rest, h)
