# eukhe: the laws of area timeouts

import Base
import ../bend/ffi_timeouts.bend as FT
import ../bend/supervise.bend as Su
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (D1) The timeouts' entry of the compiled core
# ---------------------------------------------
# docs/daemon.md D1: every timeout of the supervisor, its workers and its
# clients derives from the timeouts it must exceed (law timeouts_ordered,
# laws/supervise.bend, on the model bend/supervise.bend section Timeouts).
# Rust `eukhe_daemon::timeouts::derived` writes the 19 base values and
# reads the 9 derived values from the entry (bend/ffi_timeouts.bend): no
# Rust copy of the derivation. Every input is free: any base values.
#
# The spec below spells the request and the reply with the wire
# primitives (bend/wire.bend), never with the entry's own codec, and
# derives each value from the base values as docs/daemon.md states it.

# Spec
# ----

# the request Rust writes for the base values t, in the order of Su.Tm
def tw_spell(t: Su.Tm) -> String:
  match t:
    case Su.Tm{snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, loop, qanswer}:
      Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, Wr.put_nat(refresh, Wr.put_nat(boot, Wr.put_nat(relaunch, Wr.put_nat(startup, Wr.put_nat(check, Wr.put_nat(slack, Wr.put_nat(k, Wr.put_nat(bmax, Wr.put_nat(loop, Wr.put_nat(qanswer, "")))))))))))))))))))

# every base value of t fits the wire
def tw_fits(t: Su.Tm) -> Bool:
  match t:
    case Su.Tm{snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, loop, qanswer}:
      Bool.and(LawsBase.wire_fits(snap), Bool.and(LawsBase.wire_fits(host), Bool.and(LawsBase.wire_fits(kstep), Bool.and(LawsBase.wire_fits(kterm), Bool.and(LawsBase.wire_fits(kverify), Bool.and(LawsBase.wire_fits(harness), Bool.and(LawsBase.wire_fits(wterm), Bool.and(LawsBase.wire_fits(wverify), Bool.and(LawsBase.wire_fits(margin), Bool.and(LawsBase.wire_fits(refresh), Bool.and(LawsBase.wire_fits(boot), Bool.and(LawsBase.wire_fits(relaunch), Bool.and(LawsBase.wire_fits(startup), Bool.and(LawsBase.wire_fits(check), Bool.and(LawsBase.wire_fits(slack), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(bmax), Bool.and(LawsBase.wire_fits(loop), LawsBase.wire_fits(qanswer)))))))))))))))))))

# the derived values, in reply order: the kernel teardown (the snapshot
# flush, the host-request drain, three shutdown steps, SIGTERM, SIGKILL),
# the stop grace (the teardown, then the Harness close), the supervisor's
# drain (the grace, a worker's SIGTERM, its SIGKILL), the launcher's wait
# (the drain, then its margin), a parent's kill of a child (the kill
# route's grace, the child's drain, the margin), the lost-exit window (the
# client relaunch, the supervisor start, the worker's check, the slack),
# the max age of busy evidence (a refresh, then the boot window), the
# quiesce hold (the answer window, then the stop grace) and the restart
# window (one more than the give-up count of the longest pause plus the
# crash-loop period)
def tw_values(t: Su.Tm) -> List<&2, Nat>:
  match t:
    case Su.Tm{snap, host, kstep, kterm, kverify, harness, wterm, wverify, +margin, refresh, boot, relaunch, startup, check, slack, k, bmax, loop, qanswer}:
      +td = Nat.add(Nat.add(Nat.add(Nat.add(snap, host), Nat.mul(3n, kstep)), kterm), kverify)
      +sg = Nat.add(td, harness)
      +dr = Nat.add(Nat.add(sg, wterm), wverify)
      [td, sg, dr, Nat.add(dr, margin), Nat.add(Nat.add(sg, dr), margin), Nat.add(Nat.add(Nat.add(relaunch, startup), check), slack), Nat.add(refresh, boot), Nat.add(qanswer, sg), Nat.mul(1n+k, Nat.add(bmax, loop))]

# a value Rust reads back: it fits the wire (at most 14 decimal digits,
# i.e. below 10^14)
def tw_below(n: Nat) -> Bool:
  LawsBase.wire_fits(n)

def tw_all_below(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> r:
      Bool.and(tw_below(x), tw_all_below(r))

def tw_spell_values(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> r:
      Wr.put_nat(x, tw_spell_values(r))

def tw_reply.put(ok: Bool, xs: List<&2, Nat>) -> String:
  match ok:
    case True{}:
      tw_spell_values(xs)
    case False{}:
      Wr.err("timeouts: a value past the wire")

# the reply to the base values t: the derived values, or the error form
# when one of them is past the wire
def tw_reply(+t: Su.Tm) -> String:
  +xs = tw_values(t)
  tw_reply.put(tw_all_below(xs), xs)

# Reader: the requests the entry accepts, read with the wire primitives

def tw_read.qanswer(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, startup: Nat, check: Nat, slack: Nat, k: Nat, bmax: Nat, loop: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Su.Tm>:
  match r:
    case Wr.Got{qanswer, s}:
      Wr.Got{Su.Tm{snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, loop, qanswer}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def tw_read.loop(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, startup: Nat, check: Nat, slack: Nat, k: Nat, bmax: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Su.Tm>:
  match r:
    case Wr.Got{loop, s}:
      tw_read.qanswer(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, loop, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tw_read.bmax(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, startup: Nat, check: Nat, slack: Nat, k: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Su.Tm>:
  match r:
    case Wr.Got{bmax, s}:
      tw_read.loop(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tw_read.k(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, startup: Nat, check: Nat, slack: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Su.Tm>:
  match r:
    case Wr.Got{k, s}:
      tw_read.bmax(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tw_read.slack(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, startup: Nat, check: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Su.Tm>:
  match r:
    case Wr.Got{slack, s}:
      tw_read.k(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tw_read.check(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, startup: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Su.Tm>:
  match r:
    case Wr.Got{check, s}:
      tw_read.slack(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tw_read.startup(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Su.Tm>:
  match r:
    case Wr.Got{startup, s}:
      tw_read.check(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tw_read.relaunch(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Su.Tm>:
  match r:
    case Wr.Got{relaunch, s}:
      tw_read.startup(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tw_read.boot(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Su.Tm>:
  match r:
    case Wr.Got{boot, s}:
      tw_read.relaunch(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tw_read.refresh(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Su.Tm>:
  match r:
    case Wr.Got{refresh, s}:
      tw_read.boot(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tw_read.margin(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Su.Tm>:
  match r:
    case Wr.Got{margin, s}:
      tw_read.refresh(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tw_read.wverify(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Su.Tm>:
  match r:
    case Wr.Got{wverify, s}:
      tw_read.margin(snap, host, kstep, kterm, kverify, harness, wterm, wverify, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tw_read.wterm(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Su.Tm>:
  match r:
    case Wr.Got{wterm, s}:
      tw_read.wverify(snap, host, kstep, kterm, kverify, harness, wterm, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tw_read.harness(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Su.Tm>:
  match r:
    case Wr.Got{harness, s}:
      tw_read.wterm(snap, host, kstep, kterm, kverify, harness, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tw_read.kverify(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Su.Tm>:
  match r:
    case Wr.Got{kverify, s}:
      tw_read.harness(snap, host, kstep, kterm, kverify, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tw_read.kterm(snap: Nat, host: Nat, kstep: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Su.Tm>:
  match r:
    case Wr.Got{kterm, s}:
      tw_read.kverify(snap, host, kstep, kterm, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tw_read.kstep(snap: Nat, host: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Su.Tm>:
  match r:
    case Wr.Got{kstep, s}:
      tw_read.kterm(snap, host, kstep, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tw_read.host(snap: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Su.Tm>:
  match r:
    case Wr.Got{host, s}:
      tw_read.kstep(snap, host, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tw_read.snap(r: Wr.Dec<Nat>) -> Wr.Dec<Su.Tm>:
  match r:
    case Wr.Got{snap, s}:
      tw_read.host(snap, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tw_read.end(whole: Bool, t: Su.Tm) -> Maybe<&2, Su.Tm>:
  match whole:
    case True{}:
      Some{t}
    case False{}:
      None{}

def tw_read.whole(r: Wr.Dec<Su.Tm>) -> Maybe<&2, Su.Tm>:
  match r:
    case Wr.Got{t, s}:
      tw_read.end(Wr.end(s), t)
    case Wr.Bad{}:
      None{}

# the base values s is, when s is exactly one request
def tw_read(s: String) -> Maybe<&2, Su.Tm>:
  tw_read.whole(tw_read.snap(Wr.get_nat(s)))

# Laws
# ----

# LAW timeouts_ffi_answers: on every request Rust writes (any base values that fit the wire),
# the entry answers the 9 derived values, each derived from the base values
# it must exceed, in reply order; or exactly the error form "timeouts: a
# value past the wire" when one of them is 10^14 or more
# EXCLUDES: a misread or swapped base value, a derived value that drops,
#   adds or doubles a term, a reply in another order, a number Rust cannot
#   read (past the wire)
law timeouts_ffi_answers:
  for +t: Su.Tm
  for fits: {tw_fits(t) == True{} : Bool}
  {FT.ffi(tw_spell(t)) == tw_reply(t) : String}

# LAW timeouts_ffi_reads: every input that is exactly one request (as the wire primitives read
# it) gets the reply to its base values
# EXCLUDES: a reply on another reading of the input
law timeouts_ffi_reads:
  for +s: String
  for +t: Su.Tm
  for got: {tw_read(s) == Some{t} : Maybe<&2, Su.Tm>}
  {FT.ffi(s) == tw_reply(t) : String}

# LAW timeouts_ffi_malformed_exact: every input that is not exactly one request (a malformed
# value, a number past the wire, input left over) gets exactly the error
# form 'E ', then "timeouts: malformed request"
# EXCLUDES: a default derivation on garbage, a request with input after it
#   answered
law timeouts_ffi_malformed_exact:
  for +s: String
  for no: {tw_read(s) == None{} : Maybe<&2, Su.Tm>}
  {FT.ffi(s) == SCon{'E', SCon{' ', "timeouts: malformed request"}} : String}

# LAW timeouts_ffi_example: anchor: the base values eukhe ships in seconds (in ms they are
# 1000 times these, but k = 5; crates/eukhe-daemon src/timeouts.rs,
# eukhe-types daemon/timing.rs, eukhe-core kernel/shared.rs: the checker
# expands large literals) and the derived values Rust reads: a teardown
# of 28, a stop grace of 30, a drain of 33, a launcher wait of 35, a child
# kill of 65, a lost-exit window of 300, a max age of 1800, a quiesce hold
# of 35 and a restart window of 900; input left over is refused
# EXCLUDES: a field order other than Rust's
law timeouts_ffi_example:
  {FT.ffi("5,5,5,2,1,2,2,1,2,300,1500,60,30,5,205,5,30,120,5,") == "28,30,33,35,65,300,1800,35,900," : String} &
  {FT.ffi("5,5,5,2,1,2,2,1,2,300,1500,60,30,5,205,5,30,120,5,x") == Wr.err("timeouts: malformed request") : String}
