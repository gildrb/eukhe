# eukhe: the laws of area timeouts
#
# The timeouts' entry of the compiled core (bend/ffi_timeouts.bend): Rust
# `eukhe_daemon::timeouts::derived` writes the 19 base values once and
# reads the 9 derived values; the derivation of each is the doc of its
# field of Rust's `timeouts::Derived` (crates/eukhe-daemon/src/timeouts.rs).
# (A5-A7 continue the numbering of laws/supervise.bend, which holds A1-A4.)
# A5  Every request Rust writes (any base values that fit the wire) gets
#     the 9 derived values in reply order, each the sum of the base values
#     its Rust doc names (the restart window: k + 1 times the longest pause
#     plus the loop period); or exactly the error "timeouts: a value past
#     the wire" when one of them has 15 digits or more. Each derived value
#     is a sum that contains the timeouts it must exceed (the stop grace
#     the teardown, the launcher's wait the drain, ...), so A5 is also their
#     order (a separate `x <= x + y` law would hold for any values). Law:
#     timeouts_ffi_answers.
# A6  Any input that is not exactly such a request (a malformed value, a
#     number past the wire, input left over) gets exactly the error
#     "timeouts: malformed request". Law:
#     timeouts_ffi_malformed_unless_request.
# A7  A worker that crashes in a loop is given up within the restart
#     window (timeouts.rs): with the budget Rust configures (give up after
#     k, the derived window, the longest pause as the cap), a failure
#     followed by k more, each at most the longest pause plus the loop
#     period after the one before it, gives the worker up. Law:
#     timeouts_crash_loop_given_up.

import Base
import ../bend/ffi_timeouts.bend as FT
import ../bend/supervise.bend as Su
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (D1) The timeouts' entry of the compiled core
# ---------------------------------------------
# Every timeout of the supervisor, its workers and its clients derives
# from the timeouts it must exceed (A5). Rust writes the base values and
# reads the derived values from the entry: no Rust copy of the derivation.
# Every input is free: any base values.
#
# The spec below spells the request and the reply with the wire
# primitives (bend/wire.bend), never with the entry's own codec, and
# derives each value from the base values as the Rust docs state it.

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

# Laws
# ----

# LAW timeouts_ffi_answers: on every request Rust writes (any base values that fit the wire),
# the entry answers the 9 derived values in reply order, each the sum of
# the base values its Rust doc names (tw_values); or exactly the error form
# "timeouts: a value past the wire" when one of them is 10^14 or more
# EXCLUDES: a misread or swapped base value, a derived value that drops,
#   adds or doubles a term, a reply in another order, a number Rust cannot
#   read (past the wire)
law timeouts_ffi_answers:
  for +t: Su.Tm
  for fits: {tw_fits(t) == True{} : Bool}
  {FT.ffi(tw_spell(t)) == tw_reply(t) : String}

# LAW timeouts_ffi_malformed_unless_request: every answer but the error form "timeouts:
# malformed request" comes from an input that is exactly a request Rust
# writes (base values that fit the wire, spelled from the wire primitives,
# nothing after them); with timeouts_ffi_answers this fixes the answer to
# every input
# EXCLUDES: a decoder that accepts a missing, extra or reordered value, a
#   number past the wire, or input left over, and answers it (a default
#   derivation instead of the malformed error)
law timeouts_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FT.ffi(s), Wr.err("timeouts: malformed request")) == False{} : Bool}
  exs t: Su.Tm
  {(s, tw_fits(t)) == (tw_spell(t), True{}) : String & Bool}

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

# The crash loop (A7)
# -------------------

# the restart budget Rust configures (restart_budget::restart_cfg): give
# up after k, the window the entry derives (tw_values' last value: k + 1
# times the longest pause plus the loop period), the base pause b, the
# longest pause bmax as the cap
def tw_restart_cfg(+k: Nat, +bmax: Nat, +loop: Nat, b: Nat) -> Su.Cfg:
  Su.Cfg{k, Nat.mul(1n+k, Nat.add(bmax, loop)), b, bmax}

# every gap of gs is at most m
def tw_all_le(gs: List<&2, Nat>, +m: Nat) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case g <> rest:
      Bool.and(Nat.is_le(g, m), tw_all_le(rest, m))

# LAW timeouts_crash_loop_given_up: with the budget Rust configures from the base values,
# a crash loop is given up: after any earlier failures, a failure followed
# by k more, each at most the longest pause plus the loop period after the
# one before it (that sum not 0), gives the worker up
# EXCLUDES: a restart window too short for k crash-loop steps (a loop that
#   is never given up), a window derived from another count or period
law timeouts_crash_loop_given_up:
  for +k: Nat
  for +bmax: Nat
  for +loop: Nat
  for +b: Nat
  for +pre: List<&2, Nat>
  for +g: Nat
  for +gs: List<&2, Nat>
  for live: {Nat.is_lt(0n, Nat.add(bmax, loop)) == True{} : Bool}
  for many: {List.length(&2, Nat, gs) == k : Nat}
  for loops: {tw_all_le(gs, Nat.add(bmax, loop)) == True{} : Bool}
  {Su.gives_up(Su.verdict(tw_restart_cfg(k, bmax, loop, b), Su.failures(tw_restart_cfg(k, bmax, loop, b), List.append(&2, Nat, pre, g <> gs)))) == True{} : Bool}
