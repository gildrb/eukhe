# eukhe: lemmas the proofs of area wait_any share: the poll and the cap;
# what is left to deliver; the entry's decoder is the laws' reader
# (spec/durable/wait_any_wire.bend), stage by stage; a spelled request
# that fits reads back whole

import Base
import ../../bend/wait_any.bend as Wa
import ../../bend/ffi_wait_any.bend as FWa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../spec/durable/wait_any.bend as WaSpec
import ../../spec/durable/wait_any_wire.bend as SpW
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

# S1: the first settled target
# ----------------------------

# m with every position moved i further
def wa.shift(+i: Nat, m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{j}:
      Some{Nat.add(i, j)}

def wa.shift_later(+i: Nat, m: Maybe<&2, Nat>) -> {wa.shift(1n+i, m) == wa.shift(i, WaSpec.later(m)) : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{j}:
      %wa.add_succ_r(i, j) : {Some{_} == Some{Nat.add(i, 1n+j)} : Maybe<&2, Nat>}
      {==}

def wa.shift_zero(m: Maybe<&2, Nat>) -> {wa.shift(0n, m) == m : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{j}:
      {==}

def wa.first_here(+i: Nat) -> {Some{i} == wa.shift(i, Some{0n}) : Maybe<&2, Nat>}:
  %wa.add_zero_r(i) : {Some{_} == Some{Nat.add(i, 0n)} : Maybe<&2, Nat>}
  {==}

def wa.first_on(+named: Bool, rest: List<&2, Wa.Tgt>, +i: Nat, ih: {Wa.first(rest, named, 1n+i) == wa.shift(1n+i, WaSpec.pos(rest, named)) : Maybe<&2, Nat>})
  -> {Wa.first(rest, named, 1n+i) == wa.shift(i, WaSpec.later(WaSpec.pos(rest, named))) : Maybe<&2, Nat>}:
  Equal.trans(Maybe<&2, Nat>, Wa.first(rest, named, 1n+i), wa.shift(1n+i, WaSpec.pos(rest, named)), wa.shift(i, WaSpec.later(WaSpec.pos(rest, named))), ih, wa.shift_later(i, WaSpec.pos(rest, named)))

# the code's first settled index from i is the spec's position, moved i
def wa.first_pos(ts: List<&2, Wa.Tgt>, +named: Bool, +i: Nat) -> {Wa.first(ts, named, i) == wa.shift(i, WaSpec.pos(ts, named)) : Maybe<&2, Nat>}:
  match ts:
    case Nil{}:
      {==}
    case Con{t, +rest}:
      match t:
        case Wa.Runs{}:
          wa.first_on(named, rest, i, wa.first_pos(rest, named, 1n+i))
        case Wa.Unread{}:
          wa.first_here(i)
        case Wa.Read{}:
          match named:
            case True{}:
              wa.first_here(i)
            case False{}:
              wa.first_on(False{}, rest, i, wa.first_pos(rest, False{}, 1n+i))

def wa.first0(+ts: List<&2, Wa.Tgt>, +named: Bool) -> {WaSpec.pos(ts, named) == Wa.first(ts, named, 0n) : Maybe<&2, Nat>}:
  Equal.sym(Maybe<&2, Nat>, Wa.first(ts, named, 0n), WaSpec.pos(ts, named),
    Equal.trans(Maybe<&2, Nat>, Wa.first(ts, named, 0n), wa.shift(0n, WaSpec.pos(ts, named)), WaSpec.pos(ts, named), wa.first_pos(ts, named, 0n), wa.shift_zero(WaSpec.pos(ts, named))))

# S2: some target runs exactly when the spec counts one
def wa.live_running(ts: List<&2, Wa.Tgt>) -> {Bool.not(Nat.is_eq(WaSpec.running(ts), 0n)) == Wa.live(ts) : Bool}:
  match ts:
    case Nil{}:
      {==}
    case Con{t, rest}:
      match t:
        case Wa.Runs{}:
          {==}
        case Wa.Unread{}:
          wa.live_running(rest)
        case Wa.Read{}:
          wa.live_running(rest)

# the code's last step of a poll is the spec's
def wa.poll_of(m: Maybe<&2, Nat>, z: Bool, c: Bool, l: Bool) -> {Wa.poll.found(m, Bool.not(z), c, l) == WaSpec.poll.of(m, z, c, l) : Wa.Pick}:
  match m:
    case Some{i}:
      {==}
    case None{}:
      match z:
        case True{}:
          {==}
        case False{}:
          match c:
            case True{}:
              {==}
            case False{}:
              match l:
                case True{}:
                  {==}
                case False{}:
                  {==}

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

# a delivery state of w watchers kept for a wait, as route sends it
def wa.after_route(r: Wa.Route, +w: Nat, rest: List<&2, Wa.Ev>, +wake: Bool,
  ih: @d: Wa.D -> {Nat.is_le(Wa.deliveries(rest, wake, d), wa.left(d)) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Wa.Out.k(Wa.deliver(r, w)), Wa.deliveries(rest, wake, Wa.Out.d(Wa.deliver(r, w)))), 1n) == True{} : Bool}:
  match r:
    case Wa.ToWaiter{}:
      ih(Wa.D{w, Wa.Kept{}})
    case Wa.ToNotice{}:
      ih(Wa.D{w, Wa.Sent{}})

# no events deliver more than what is left
def wa.once_go(es: List<&2, Wa.Ev>, +wake: Bool, d: Wa.D) -> {Nat.is_le(Wa.deliveries(es, wake, d), wa.left(d)) == True{} : Bool}:
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

# R4: the code's deliveries are the laws' count
# ---------------------------------------------

def wa.k_eq(o: Wa.Out) -> {Wa.Out.k(o) == WaSpec.out_k(o) : Nat}:
  match o:
    case Wa.Out{d, k}:
      {==}

# The reader (R5)
# ---------------

def wa.tgt_eq(n: Nat) -> {FWa.tgt_of(n) == SpW.r_tgt(n) : Maybe<&2, Wa.Tgt>}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+u:
      {==}

def wa.cons_eq(t: Maybe<&2, Wa.Tgt>, r: Maybe<&2, List<&2, Wa.Tgt>>) -> {FWa.tgts.cons(t, r) == SpW.r_tgts.cons(t, r) : Maybe<&2, List<&2, Wa.Tgt>>}:
  match t:
    case None{}:
      {==}
    case Some{x}:
      match r:
        case None{}:
          {==}
        case Some{xs}:
          {==}

def wa.tgts_eq(ns: List<&2, Nat>) -> {FWa.tgts(ns) == SpW.r_tgts(ns) : Maybe<&2, List<&2, Wa.Tgt>>}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, +rest}:
      %wa.tgt_eq(n) : {FWa.tgts.cons(FWa.tgt_of(n), FWa.tgts(rest)) == SpW.r_tgts.cons(_, SpW.r_tgts(rest)) : Maybe<&2, List<&2, Wa.Tgt>>}
      %wa.tgts_eq(rest) : {FWa.tgts.cons(FWa.tgt_of(n), FWa.tgts(rest)) == SpW.r_tgts.cons(FWa.tgt_of(n), _) : Maybe<&2, List<&2, Wa.Tgt>>}
      wa.cons_eq(FWa.tgt_of(n), FWa.tgts(rest))

def wa.poll_ok(n: Bool, c: Bool, l: Bool, ts: Maybe<&2, List<&2, Wa.Tgt>>, s: String) -> {FWa.get_poll.ok(n, c, l, ts, s) == SpW.r_poll.ok(n, c, l, ts, s) : Wr.Dec<FWa.Req>}:
  match ts:
    case Some{xs}:
      {==}
    case None{}:
      {==}

def wa.poll_ts(+n: Bool, +c: Bool, +l: Bool, x: Wr.Dec<List<&2, Nat>>) -> {FWa.get_poll.ts(n, c, l, x) == SpW.r_poll.ts(n, c, l, x) : Wr.Dec<FWa.Req>}:
  match x:
    case Wr.Got{+ns, +s}:
      %wa.tgts_eq(ns) : {FWa.get_poll.ok(n, c, l, FWa.tgts(ns), s) == SpW.r_poll.ok(n, c, l, _, s) : Wr.Dec<FWa.Req>}
      wa.poll_ok(n, c, l, FWa.tgts(ns), s)
    case Wr.Bad{}:
      {==}

def wa.poll_late(+n: Bool, +c: Bool, x: Wr.Dec<Bool>) -> {FWa.get_poll.late(n, c, x) == SpW.r_poll.late(n, c, x) : Wr.Dec<FWa.Req>}:
  match x:
    case Wr.Got{l, s}:
      wa.poll_ts(n, c, l, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      {==}

def wa.poll_cancel(+n: Bool, x: Wr.Dec<Bool>) -> {FWa.get_poll.cancel(n, x) == SpW.r_poll.cancel(n, x) : Wr.Dec<FWa.Req>}:
  match x:
    case Wr.Got{c, s}:
      wa.poll_late(n, c, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def wa.poll(x: Wr.Dec<Bool>) -> {FWa.get_poll(x) == SpW.r_poll(x) : Wr.Dec<FWa.Req>}:
  match x:
    case Wr.Got{n, s}:
      wa.poll_cancel(n, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def wa.phase_eq(n: Nat) -> {FWa.phase_of(n) == SpW.r_phase(n) : Maybe<&2, Wa.Phase>}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+u:
      {==}

def wa.ev_eq(n: Nat) -> {FWa.ev_of(n) == SpW.r_ev(n) : Maybe<&2, Wa.Ev>}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n+u:
      {==}

def wa.step_ok(k: Bool, w: Nat, p: Maybe<&2, Wa.Phase>, e: Maybe<&2, Wa.Ev>, s: String) -> {FWa.get_step.ok(k, w, p, e, s) == SpW.r_step.ok(k, w, p, e, s) : Wr.Dec<FWa.Req>}:
  match p:
    case Some{ph}:
      match e:
        case Some{ev}:
          {==}
        case None{}:
          {==}
    case None{}:
      {==}

def wa.step_ev(+k: Bool, +w: Nat, +p: Nat, x: Wr.Dec<Nat>) -> {FWa.get_step.ev(k, w, p, x) == SpW.r_step.ev(k, w, p, x) : Wr.Dec<FWa.Req>}:
  match x:
    case Wr.Got{+e, +s}:
      %wa.phase_eq(p) : {FWa.get_step.ok(k, w, FWa.phase_of(p), FWa.ev_of(e), s) == SpW.r_step.ok(k, w, _, SpW.r_ev(e), s) : Wr.Dec<FWa.Req>}
      %wa.ev_eq(e) : {FWa.get_step.ok(k, w, FWa.phase_of(p), FWa.ev_of(e), s) == SpW.r_step.ok(k, w, FWa.phase_of(p), _, s) : Wr.Dec<FWa.Req>}
      wa.step_ok(k, w, FWa.phase_of(p), FWa.ev_of(e), s)
    case Wr.Bad{}:
      {==}

def wa.step_phase(+k: Bool, +w: Nat, x: Wr.Dec<Nat>) -> {FWa.get_step.phase(k, w, x) == SpW.r_step.phase(k, w, x) : Wr.Dec<FWa.Req>}:
  match x:
    case Wr.Got{p, s}:
      wa.step_ev(k, w, p, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def wa.step_watchers(+k: Bool, x: Wr.Dec<Nat>) -> {FWa.get_step.watchers(k, x) == SpW.r_step.watchers(k, x) : Wr.Dec<FWa.Req>}:
  match x:
    case Wr.Got{w, s}:
      wa.step_phase(k, w, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def wa.step(x: Wr.Dec<Bool>) -> {FWa.get_step(x) == SpW.r_step(x) : Wr.Dec<FWa.Req>}:
  match x:
    case Wr.Got{k, s}:
      wa.step_watchers(k, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def wa.secs(x: Wr.Dec<Nat>) -> {FWa.get_timeout.ms(x) == SpW.r_timeout.secs(x) : Wr.Dec<FWa.Req>}:
  match x:
    case Wr.Got{t, s}:
      {==}
    case Wr.Bad{}:
      {==}

def wa.timeout(x: Wr.Dec<Nat>) -> {FWa.get_timeout(x) == SpW.r_timeout(x) : Wr.Dec<FWa.Req>}:
  match x:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          wa.secs(Wr.get_nat(s))
        case 2n+u:
          {==}
    case Wr.Bad{}:
      {==}

def wa.start(x: Wr.Dec<Nat>) -> {FWa.get_req.start(x) == SpW.r_req.tag(x) : Wr.Dec<FWa.Req>}:
  match x:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          wa.poll(Wr.get_bool(s))
        case 1n:
          wa.step(Wr.get_bool(s))
        case 2n:
          wa.timeout(Wr.get_nat(s))
        case 3n+u:
          {==}
    case Wr.Bad{}:
      {==}

# the entry reads every input as the laws' reader does
def wa.req(+s: String) -> {FWa.get_req(s) == SpW.r_req(s) : Wr.Dec<FWa.Req>}:
  wa.start(Wr.get_nat(s))

# Read back (R5)
# --------------

# the target codes read back as the targets
def wa.tgts_back(ts: List<&2, Wa.Tgt>) -> {SpW.r_tgts(SpW.c_tgts(ts)) == Some{ts} : Maybe<&2, List<&2, Wa.Tgt>>}:
  match ts:
    case Nil{}:
      {==}
    case Con{t, +rest}:
      match t:
        case Wa.Runs{}:
          %Equal.sym(Maybe<&2, List<&2, Wa.Tgt>>, SpW.r_tgts(SpW.c_tgts(rest)), Some{rest}, wa.tgts_back(rest)) : {SpW.r_tgts.cons(Some{Wa.Runs{}}, _) == Some{Wa.Runs{} <> rest} : Maybe<&2, List<&2, Wa.Tgt>>}
          {==}
        case Wa.Unread{}:
          %Equal.sym(Maybe<&2, List<&2, Wa.Tgt>>, SpW.r_tgts(SpW.c_tgts(rest)), Some{rest}, wa.tgts_back(rest)) : {SpW.r_tgts.cons(Some{Wa.Unread{}}, _) == Some{Wa.Unread{} <> rest} : Maybe<&2, List<&2, Wa.Tgt>>}
          {==}
        case Wa.Read{}:
          %Equal.sym(Maybe<&2, List<&2, Wa.Tgt>>, SpW.r_tgts(SpW.c_tgts(rest)), Some{rest}, wa.tgts_back(rest)) : {SpW.r_tgts.cons(Some{Wa.Read{}}, _) == Some{Wa.Read{} <> rest} : Maybe<&2, List<&2, Wa.Tgt>>}
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

def wa.phase_back(p: Wa.Phase) -> {SpW.r_phase(SpW.c_phase(p)) == Some{p} : Maybe<&2, Wa.Phase>}:
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

def wa.ev_back(e: Wa.Ev) -> {SpW.r_ev(SpW.c_ev(e)) == Some{e} : Maybe<&2, Wa.Ev>}:
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
def wa.poll_rt(+n: Bool, +c: Bool, +l: Bool, +ts: List<&2, Wa.Tgt>, +rest: String, h: {LawsBase.wire_fits(List.length(&2, Wa.Tgt, ts)) == True{} : Bool}) -> {SpW.r_req(SpW.w_req(FWa.QPoll{n, c, l, ts}, rest)) == Wr.Got{FWa.QPoll{n, c, l, ts}, rest} : Wr.Dec<FWa.Req>}:
  +cs = SpW.c_tgts(ts)
  +r4 = Wr.put_list(~Nat, ~Wr.put_nat, cs, rest)
  +r3 = Wr.put_bool(l, r4)
  +r2 = Wr.put_bool(c, r3)
  +r1 = Wr.put_bool(n, r2)
  -g = {Wr.Got{FWa.QPoll{n, c, l, ts}, rest} : Wr.Dec<FWa.Req>}
  %wa.nat_rt(0n, r1, {==}) : {SpW.r_req.tag(_) == g : Wr.Dec<FWa.Req>}
  %wa.bool_rt(n, r2) : {SpW.r_poll(_) == g : Wr.Dec<FWa.Req>}
  %wa.bool_rt(c, r3) : {SpW.r_poll.cancel(n, _) == g : Wr.Dec<FWa.Req>}
  %wa.bool_rt(l, r4) : {SpW.r_poll.late(n, c, _) == g : Wr.Dec<FWa.Req>}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, r4), Wr.Got{cs, rest}, Wire.wire_list_round_trip(cs, rest, wa.list_fit(ts, h))) : {SpW.r_poll.ts(n, c, l, _) == g : Wr.Dec<FWa.Req>}
  %Equal.sym(Maybe<&2, List<&2, Wa.Tgt>>, SpW.r_tgts(cs), Some{ts}, wa.tgts_back(ts)) : {SpW.r_poll.ok(n, c, l, _, rest) == g : Wr.Dec<FWa.Req>}
  {==}

# a step request that fits reads back, and the rest is untouched
def wa.step_rt(+k: Bool, +w: Nat, +p: Wa.Phase, +e: Wa.Ev, +rest: String, h: {LawsBase.wire_fits(w) == True{} : Bool}) -> {SpW.r_req(SpW.w_req(FWa.QStep{k, Wa.D{w, p}, e}, rest)) == Wr.Got{FWa.QStep{k, Wa.D{w, p}, e}, rest} : Wr.Dec<FWa.Req>}:
  +r4 = Wr.put_nat(SpW.c_ev(e), rest)
  +r3 = Wr.put_nat(SpW.c_phase(p), r4)
  +r2 = Wr.put_nat(w, r3)
  +r1 = Wr.put_bool(k, r2)
  -g = {Wr.Got{FWa.QStep{k, Wa.D{w, p}, e}, rest} : Wr.Dec<FWa.Req>}
  %wa.nat_rt(1n, r1, {==}) : {SpW.r_req.tag(_) == g : Wr.Dec<FWa.Req>}
  %wa.bool_rt(k, r2) : {SpW.r_step(_) == g : Wr.Dec<FWa.Req>}
  %wa.nat_rt(w, r3, h) : {SpW.r_step.watchers(k, _) == g : Wr.Dec<FWa.Req>}
  %wa.nat_rt(SpW.c_phase(p), r4, wa.phase_fits(p)) : {SpW.r_step.phase(k, w, _) == g : Wr.Dec<FWa.Req>}
  %wa.nat_rt(SpW.c_ev(e), rest, wa.ev_fits(e)) : {SpW.r_step.ev(k, w, SpW.c_phase(p), _) == g : Wr.Dec<FWa.Req>}
  %Equal.sym(Maybe<&2, Wa.Phase>, SpW.r_phase(SpW.c_phase(p)), Some{p}, wa.phase_back(p)) : {SpW.r_step.ok(k, w, _, SpW.r_ev(SpW.c_ev(e)), rest) == g : Wr.Dec<FWa.Req>}
  %Equal.sym(Maybe<&2, Wa.Ev>, SpW.r_ev(SpW.c_ev(e)), Some{e}, wa.ev_back(e)) : {SpW.r_step.ok(k, w, Some{p}, _, rest) == g : Wr.Dec<FWa.Req>}
  {==}

# a timeout request that fits reads back, and the rest is untouched
def wa.timeout_rt(+a: Maybe<&2, Nat>, +rest: String, h: {SpW.fit_asked(a) == True{} : Bool}) -> {SpW.r_req(SpW.w_req(FWa.QTimeout{a}, rest)) == Wr.Got{FWa.QTimeout{a}, rest} : Wr.Dec<FWa.Req>}:
  match a:
    case None{}:
      +r1 = Wr.put_nat(0n, rest)
      %wa.nat_rt(2n, r1, {==}) : {SpW.r_req.tag(_) == Wr.Got{FWa.QTimeout{None{}}, rest} : Wr.Dec<FWa.Req>}
      %wa.nat_rt(0n, rest, {==}) : {SpW.r_timeout(_) == Wr.Got{FWa.QTimeout{None{}}, rest} : Wr.Dec<FWa.Req>}
      {==}
    case Some{+t}:
      +r2 = Wr.put_nat(t, rest)
      +r1 = Wr.put_nat(1n, r2)
      %wa.nat_rt(2n, r1, {==}) : {SpW.r_req.tag(_) == Wr.Got{FWa.QTimeout{Some{t}}, rest} : Wr.Dec<FWa.Req>}
      %wa.nat_rt(1n, r2, {==}) : {SpW.r_timeout(_) == Wr.Got{FWa.QTimeout{Some{t}}, rest} : Wr.Dec<FWa.Req>}
      %wa.nat_rt(t, rest, h) : {SpW.r_timeout.secs(_) == Wr.Got{FWa.QTimeout{Some{t}}, rest} : Wr.Dec<FWa.Req>}
      {==}

# a spelled request that fits reads back (with the laws' reader), and the
# rest is untouched
def wa.req_rt(+q: FWa.Req, +rest: String, h: {SpW.fit(q) == True{} : Bool}) -> {SpW.r_req(SpW.w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FWa.Req>}:
  match q:
    case FWa.QPoll{+n, +c, +l, +ts}:
      wa.poll_rt(n, c, l, ts, rest, h)
    case FWa.QStep{+k, d, +e}:
      match d:
        case Wa.D{+w, +p}:
          wa.step_rt(k, w, p, e, rest, h)
    case FWa.QTimeout{+a}:
      wa.timeout_rt(a, rest, h)
