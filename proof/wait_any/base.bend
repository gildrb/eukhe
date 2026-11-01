# eukhe: lemmas the proofs of area wait_any share

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec

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
