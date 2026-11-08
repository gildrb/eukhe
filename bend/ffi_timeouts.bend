# ffi_timeouts: the compiled Bend core's entry for the supervisor's
# timeouts (bend/supervise.bend section Timeouts). Rust
# `eukhe_daemon::timeouts::derived` calls it once through
# `eukhe_bend::call` and keeps the answer for the process.
#
# Request (crates/eukhe-bend/WIRE.md): a record of the 19 base values, in
# the order of Su.Tm (Nats: ms, but k, the give-up count):
#   snap host kstep kterm kverify harness wterm wverify margin refresh
#   boot relaunch startup check slack k bmax loop qanswer
# Reply: a record of the 9 derived values (Nats, ms):
#   teardown stop_grace drain launcher_wait child_kill lost max_age
#   quiesce_hold window
# A derived value past the wire (15 digits or more) answers the error form
# "timeouts: a value past the wire": the entry never writes a number Rust
# cannot read. A malformed request or input left over answers the error
# form "timeouts: malformed request".

import Base
import ./wire.bend as W
import ./supervise.bend as Su

# Decoding
# --------

def get_tm.qanswer(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, startup: Nat, check: Nat, slack: Nat, k: Nat, bmax: Nat, loop: Nat, r: W.Dec<Nat>) -> W.Dec<Su.Tm>:
  match r:
    case W.Got{qanswer, rest}:
      W.Got{Su.Tm{snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, loop, qanswer}, rest}
    case W.Bad{}:
      W.Bad{}

def get_tm.loop(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, startup: Nat, check: Nat, slack: Nat, k: Nat, bmax: Nat, r: W.Dec<Nat>) -> W.Dec<Su.Tm>:
  match r:
    case W.Got{loop, rest}:
      get_tm.qanswer(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, loop, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_tm.bmax(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, startup: Nat, check: Nat, slack: Nat, k: Nat, r: W.Dec<Nat>) -> W.Dec<Su.Tm>:
  match r:
    case W.Got{bmax, rest}:
      get_tm.loop(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_tm.k(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, startup: Nat, check: Nat, slack: Nat, r: W.Dec<Nat>) -> W.Dec<Su.Tm>:
  match r:
    case W.Got{k, rest}:
      get_tm.bmax(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_tm.slack(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, startup: Nat, check: Nat, r: W.Dec<Nat>) -> W.Dec<Su.Tm>:
  match r:
    case W.Got{slack, rest}:
      get_tm.k(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_tm.check(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, startup: Nat, r: W.Dec<Nat>) -> W.Dec<Su.Tm>:
  match r:
    case W.Got{check, rest}:
      get_tm.slack(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_tm.startup(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, r: W.Dec<Nat>) -> W.Dec<Su.Tm>:
  match r:
    case W.Got{startup, rest}:
      get_tm.check(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_tm.relaunch(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, r: W.Dec<Nat>) -> W.Dec<Su.Tm>:
  match r:
    case W.Got{relaunch, rest}:
      get_tm.startup(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_tm.boot(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, r: W.Dec<Nat>) -> W.Dec<Su.Tm>:
  match r:
    case W.Got{boot, rest}:
      get_tm.relaunch(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_tm.refresh(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, r: W.Dec<Nat>) -> W.Dec<Su.Tm>:
  match r:
    case W.Got{refresh, rest}:
      get_tm.boot(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_tm.margin(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, r: W.Dec<Nat>) -> W.Dec<Su.Tm>:
  match r:
    case W.Got{margin, rest}:
      get_tm.refresh(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_tm.wverify(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, r: W.Dec<Nat>) -> W.Dec<Su.Tm>:
  match r:
    case W.Got{wverify, rest}:
      get_tm.margin(snap, host, kstep, kterm, kverify, harness, wterm, wverify, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_tm.wterm(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, r: W.Dec<Nat>) -> W.Dec<Su.Tm>:
  match r:
    case W.Got{wterm, rest}:
      get_tm.wverify(snap, host, kstep, kterm, kverify, harness, wterm, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_tm.harness(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, r: W.Dec<Nat>) -> W.Dec<Su.Tm>:
  match r:
    case W.Got{harness, rest}:
      get_tm.wterm(snap, host, kstep, kterm, kverify, harness, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_tm.kverify(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, r: W.Dec<Nat>) -> W.Dec<Su.Tm>:
  match r:
    case W.Got{kverify, rest}:
      get_tm.harness(snap, host, kstep, kterm, kverify, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_tm.kterm(snap: Nat, host: Nat, kstep: Nat, r: W.Dec<Nat>) -> W.Dec<Su.Tm>:
  match r:
    case W.Got{kterm, rest}:
      get_tm.kverify(snap, host, kstep, kterm, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_tm.kstep(snap: Nat, host: Nat, r: W.Dec<Nat>) -> W.Dec<Su.Tm>:
  match r:
    case W.Got{kstep, rest}:
      get_tm.kterm(snap, host, kstep, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_tm.host(snap: Nat, r: W.Dec<Nat>) -> W.Dec<Su.Tm>:
  match r:
    case W.Got{host, rest}:
      get_tm.kstep(snap, host, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_tm.snap(r: W.Dec<Nat>) -> W.Dec<Su.Tm>:
  match r:
    case W.Got{snap, rest}:
      get_tm.host(snap, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

# the base values at the start of s
def get_tm(s: String) -> W.Dec<Su.Tm>:
  get_tm.snap(W.get_nat(s))

# Encoding
# --------

# 1 + how many more decimal digits follow the lowest one of a value whose
# higher part is q (the fuel f >= q is enough)
def digits.go(f: Nat, q: Nat) -> Nat:
  match f:
    case 0n:
      0n
    case 1n+g:
      match q:
        case 0n:
          0n
        case 1n+p:
          +m = {1n+p : Nat}
          1n+digits.go(g, Nat.div(m, 10n))

# how many decimal digits n has (0 has one)
def digits(n: Nat) -> Nat:
  +m = n
  1n+digits.go(m, Nat.div(m, 10n))

# a number Rust reads back: at most 14 digits (below 10^14)
def fits(n: Nat) -> Bool:
  Nat.is_le(digits(n), 14n)

# A derived value is computed as a Maybe: the value when Rust can read it
# back, None once it is past the wire. Every sum adds two values that fit
# (each below 10^14, the sum below 2^48 - 1), and the product doubles or
# adds a value that fits, so no step passes the runtime's Nat range,
# whatever the base values (the laws' derivation, Su.Tm, sums them whole).

def fit.put(ok: Bool, n: Nat) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{n}
    case False{}:
      None{}

# n, when Rust reads it back; else None
def fit(+n: Nat) -> Maybe<&2, Nat>:
  fit.put(fits(n), n)

def plus.some(x: Nat, b: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case None{}:
      None{}
    case Some{y}:
      fit(Nat.add(x, y))

# a + b, None when either or the sum is past the wire
def plus(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match a:
    case None{}:
      None{}
    case Some{x}:
      plus.some(x, b)

# twice h, plus y when the bit r is 1
def times.bit(r: Nat, +h: Maybe<&2, Nat>, y: Nat) -> Maybe<&2, Nat>:
  match r:
    case 0n:
      plus(h, h)
    case 1n+q:
      plus(plus(h, h), Some{y})

# x * y for a y that fits, None when past the wire: the product of half x
# (rounded down), doubled, plus y when x is odd (the fuel f >= x)
def times.go(f: Nat, x: Nat, +y: Nat) -> Maybe<&2, Nat>:
  match f:
    case 0n:
      Some{0n}
    case 1n+g:
      match x:
        case 0n:
          Some{0n}
        case 1n+p:
          +x1 = {1n+p : Nat}
          times.bit(Nat.mod(x1, 2n), times.go(g, Nat.div(x1, 2n), y), y)

# x * b, None when b or the product is past the wire (x is at least 1)
def times(+x: Nat, b: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case None{}:
      None{}
    case Some{y}:
      times.go(x, x, y)

# the derived values, in reply order (the order of Su.Tm's derivation)
def derived(t: Su.Tm) -> List<&2, Maybe<&2, Nat>>:
  match t:
    case Su.Tm{snap, host, +kstep, kterm, kverify, harness, wterm, wverify, +margin, refresh, boot, relaunch, startup, check, slack, k, bmax, loop, qanswer}:
      +ks = fit(kstep)
      +td = plus(plus(plus(plus(fit(snap), fit(host)), plus(ks, plus(ks, plus(ks, fit(0n))))), fit(kterm)), fit(kverify))
      +sg = plus(td, fit(harness))
      +dr = plus(plus(sg, fit(wterm)), fit(wverify))
      [td, sg, dr, plus(dr, fit(margin)), plus(plus(sg, dr), fit(margin)), plus(plus(plus(fit(relaunch), fit(startup)), fit(check)), fit(slack)), plus(fit(refresh), fit(boot)), plus(fit(qanswer), sg), times(1n+k, plus(fit(bmax), fit(loop)))]

def every.cons(x: Nat, m: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  match m:
    case None{}:
      None{}
    case Some{xs}:
      Some{x <> xs}

# every value, when none is past the wire
def every(ms: List<&2, Maybe<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  match ms:
    case Nil{}:
      Some{Nil{}}
    case m <> t:
      match m:
        case None{}:
          None{}
        case Some{x}:
          every.cons(x, every(t))

# the values of xs, one after the other, then rest
def put_nats(xs: List<&2, Nat>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      W.put_nat(x, put_nats(t, rest))

def answer.of(m: Maybe<&2, List<&2, Nat>>) -> String:
  match m:
    case Some{xs}:
      put_nats(xs, "")
    case None{}:
      W.err("timeouts: a value past the wire")

# the reply to the base values t
def answer(t: Su.Tm) -> String:
  answer.of(every(derived(t)))

# The entry
# ---------

def ffi.fin(done: Bool, t: Su.Tm) -> String:
  match done:
    case True{}:
      answer(t)
    case False{}:
      W.err("timeouts: malformed request")

def ffi.go(r: W.Dec<Su.Tm>) -> String:
  match r:
    case W.Got{t, rest}:
      ffi.fin(W.end(rest), t)
    case W.Bad{}:
      W.err("timeouts: malformed request")

def ffi(input: String) -> String:
  ffi.go(get_tm(input))
