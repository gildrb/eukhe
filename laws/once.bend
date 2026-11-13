# eukhe: the laws of area once

import Base
import ../bend/once.bend as O
import ../bend/ffi_once.bend as FO
import ../bend/wire.bend as Wr
import ../bend/tool_call.bend as Tc
import ../spec/once/life.bend as S
import ./base.bend as LawsBase

# (O1-O8) Exactly-once effects
# ----------------------------
# spec/README.md O1-O8. bend/once.bend: the life of one effect across
# restarts and what a restart does with it. An effect is anything the
# harness does to the world for a run (a tool call, a subagent spawn, a
# background job, a cron fire, a heartbeat, the delivery of a queued or
# steering message, a provider request, a file write). Rust journals it
# durably (intended, started at each launch, then one end: finished,
# unknown, unstarted) and, at every restart of its run, opens the stepper
# bend/ffi_once.bend (eukhe-bend rules/once.rs), sends it the records of
# the effect's journal in order, asks what the restart does, and does it.
# The call of the same entry answers an effect's idempotency key.
# spec/once/life.bend restates the rule (O1-O8) and the world of one
# effect. Every law holds for every input: any list of records (also one
# no run writes), any order of events, any policy, any cap.
#
# Not pinned here: that Rust writes each record where the spec says
# (before the launch, after the end) and reads the world truthfully; that
# a receiver drops a repeated key. The Rust tests kill the process at
# each point of each effect kind (crates/eukhe-daemon/tests/
# exactly_once_e2e).

# Spellers: the bytes Rust sends and reads, from the wire's primitives
# --------------------------------------------------------------------

# a record: 0 intended, 1 started, 2 finished, 3 unknown, 4 unstarted
def on_spell_rec(r: O.Rec, rest: String) -> String:
  match r:
    case O.Intended{}:
      Wr.put_nat(0n, rest)
    case O.Started{}:
      Wr.put_nat(1n, rest)
    case O.Finished{}:
      Wr.put_nat(2n, rest)
    case O.Unknown{}:
      Wr.put_nat(3n, rest)
    case O.Unstarted{}:
      Wr.put_nat(4n, rest)

# a mode: 0 resume, 1 stop
def on_spell_mode(m: O.Mode, rest: String) -> String:
  match m:
    case O.Resume{}:
      Wr.put_nat(0n, rest)
    case O.Stop{}:
      Wr.put_nat(1n, rest)

# a policy: 0 never, 1 safe, 2 keyed and its cap
def on_spell_policy(p: O.Policy, rest: String) -> String:
  match p:
    case O.Never{}:
      Wr.put_nat(0n, rest)
    case O.Safe{}:
      Wr.put_nat(1n, rest)
    case O.Keyed{cap}:
      Wr.put_nat(2n, Wr.put_nat(cap, rest))

# what the world shows: 0 dark, 1 landed, 2 clean
def on_spell_seen(s: O.Seen, rest: String) -> String:
  match s:
    case O.Dark{}:
      Wr.put_nat(0n, rest)
    case O.Landed{}:
      Wr.put_nat(1n, rest)
    case O.Clean{}:
      Wr.put_nat(2n, rest)

# an event as Rust writes it: 0 and a record; 1 and the restart's
# question (mode, policy, what the world shows)
def on_spell(e: FO.Ev) -> String:
  match e:
    case FO.Note{r}:
      Wr.put_nat(0n, on_spell_rec(r, ""))
    case FO.Ask{m, p, s}:
      Wr.put_nat(1n, on_spell_mode(m, on_spell_policy(p, on_spell_seen(s, ""))))

# a life as Rust reads it: 0 absent, 1 pending, 2 running and the
# launches after the first, 3 ran, 4 lost, 5 void
def on_spell_life(l: O.Life) -> String:
  match l:
    case O.Absent{}:
      "0,"
    case O.Pending{}:
      "1,"
    case O.Running{again}:
      SCon{'2', SCon{',', Wr.put_nat(again, "")}}
    case O.Ran{}:
      "3,"
    case O.Unsure{}:
      "4,"
    case O.Void{}:
      "5,"

# a verdict as Rust reads it: 0 skip, 1 launch, 2 adopt, 3 interrupt,
# 4 abandon, 5 settled
def on_spell_verdict(v: O.Verdict) -> String:
  match v:
    case O.Skip{}:
      "0,"
    case O.Launch{}:
      "1,"
    case O.Adopt{}:
      "2,"
    case O.Interrupt{}:
      "3,"
    case O.Abandon{}:
      "4,"
    case O.Settled{}:
      "5,"

# a key request as Rust writes it: the scope, then the id
def on_spell_key(scope: String, id: String) -> String:
  Wr.put_str(scope, Wr.put_str(id, ""))

def on_state(r: FO.St & String) -> FO.St:
  (s, x) = r
  s

def on_reply(r: FO.St & String) -> String:
  (s, x) = r
  x

# the stepper as opened
def on_opened() -> FO.St:
  on_state(FO.open(""))

# the replies of the stepper st to the events es, spelled, in order
def on_replies(es: List<&2, FO.Ev>, +st: FO.St) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> rest:
      on_reply(FO.step(st, on_spell(e))) <> on_replies(rest, on_state(FO.step(st, on_spell(e))))

# What O1-O8 ask of the stepper, written from the spec
# ----------------------------------------------------

# the reply O1-O8 ask for each event, spelled; j: the records sent before
# it, in order. A record answers the life of the records read so far; a
# question answers the restart's verdict for them and leaves them as they
# are.
def on_spec(es: List<&2, FO.Ev>, +j: List<&2, O.Rec>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case FO.Note{+r}:
          on_spell_life(S.life_spec(List.append(&2, O.Rec, j, [r]))) <> on_spec(rest, List.append(&2, O.Rec, j, [r]))
        case FO.Ask{m, p, s}:
          on_spell_verdict(S.verdict_spec(S.life_spec(j), s, m, p)) <> on_spec(rest, j)

def on_fit.policy(p: O.Policy) -> Bool:
  match p:
    case O.Never{}:
      True{}
    case O.Safe{}:
      True{}
    case O.Keyed{cap}:
      LawsBase.wire_fits(cap)

def on_fit.ev(e: FO.Ev) -> Bool:
  match e:
    case FO.Note{r}:
      True{}
    case FO.Ask{m, p, s}:
      on_fit.policy(p)

# every cap of es fits the wire (at most 14 digits)
def on_fit(es: List<&2, FO.Ev>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> rest:
      Bool.and(on_fit.ev(e), on_fit(rest))

# The world of one effect, run with the shipped rules (spec: The world)
# ---------------------------------------------------------------------

# the world after the restart's verdict v for an effect of life l, no
# launch in flight (n launches, k lands, e ends, x late launches)
def wd_answer(v: O.Verdict, +l: O.Life, n: Nat, k: Nat, e: Nat, x: Nat) -> S.World:
  match v:
    case O.Skip{}:
      S.Wd{l, False{}, False{}, n, k, e, x}
    case O.Launch{}:
      S.Wd{O.life.step(l, O.Started{}), True{}, False{}, 1n+n, k, e, S.late_add(S.settled(l), x)}
    case O.Adopt{}:
      S.Wd{O.life.step(l, O.Finished{}), False{}, False{}, n, k, 1n+e, x}
    case O.Interrupt{}:
      S.Wd{O.life.step(l, O.Unknown{}), False{}, False{}, n, k, 1n+e, x}
    case O.Abandon{}:
      S.Wd{O.life.step(l, O.Unstarted{}), False{}, False{}, n, k, 1n+e, x}
    case O.Settled{}:
      S.Wd{l, False{}, False{}, n, k, e, x}

# the runtime comes to the effect: never while a launch is in flight
def wd_tick(live: Bool, +l: O.Life, hit: Bool, n: Nat, +k: Nat, e: Nat, x: Nat, m: O.Mode, look: Bool, p: O.Policy) -> S.World:
  match live:
    case True{}:
      S.Wd{l, True{}, hit, n, k, e, x}
    case False{}:
      wd_answer(O.recover(l, S.seen(look, k), m, p), l, n, k, e, x)

# the launch in flight takes hold: once
def wd_land(live: Bool, hit: Bool, l: O.Life, n: Nat, k: Nat, e: Nat, x: Nat) -> S.World:
  match live hit:
    case True{} False{}:
      S.Wd{l, True{}, True{}, n, 1n+k, e, x}
    case True{} True{}:
      S.Wd{l, True{}, True{}, n, k, e, x}
    case False{} h:
      S.Wd{l, False{}, h, n, k, e, x}

# a launch that returns took hold, if not before
def wd_end.lands(hit: Bool, k: Nat) -> Nat:
  match hit:
    case True{}:
      k
    case False{}:
      1n+k

# the launch in flight returns: finished is journaled
def wd_end(live: Bool, l: O.Life, hit: Bool, n: Nat, k: Nat, e: Nat, x: Nat) -> S.World:
  match live:
    case True{}:
      S.Wd{O.life.step(l, O.Finished{}), False{}, False{}, n, wd_end.lands(hit, k), 1n+e, x}
    case False{}:
      S.Wd{l, False{}, hit, n, k, e, x}

# the world after one event, the effect of policy p
def wd_step(w: S.World, e: S.Ev, p: O.Policy) -> S.World:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      match e:
        case S.Mean{}:
          S.Wd{O.life.step(l, O.Intended{}), live, hit, n, k, d, x}
        case S.Tick{m, look}:
          wd_tick(live, l, hit, n, k, d, x, m, look, p)
        case S.Land{}:
          wd_land(live, hit, l, n, k, d, x)
        case S.End{}:
          wd_end(live, l, hit, n, k, d, x)
        case S.Crash{}:
          S.Wd{l, False{}, False{}, n, k, d, x}

# the world after the events es, in order, from w
def wd_run(es: List<&2, S.Ev>, w: S.World, +p: O.Policy) -> S.World:
  match es:
    case Nil{}:
      w
    case e <> rest:
      wd_run(rest, wd_step(w, e, p), p)

# the effect waits: intended, never launched, nothing in flight
def wd_waits(w: S.World) -> Bool:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      match l:
        case O.Absent{}:
          False{}
        case O.Pending{}:
          Bool.not(live)
        case O.Running{again}:
          False{}
        case O.Ran{}:
          False{}
        case O.Unsure{}:
          False{}
        case O.Void{}:
          False{}

# the effect was cut: started, no end on record, nothing in flight
def wd_cut(w: S.World) -> Bool:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      match l:
        case O.Absent{}:
          False{}
        case O.Pending{}:
          False{}
        case O.Running{again}:
          Bool.not(live)
        case O.Ran{}:
          False{}
        case O.Unsure{}:
          False{}
        case O.Void{}:
          False{}

# a launch is in flight
def wd_live(w: S.World) -> Bool:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      live

# the effect is reported interrupted
def wd_lost(w: S.World) -> Bool:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      match l:
        case O.Absent{}:
          False{}
        case O.Pending{}:
          False{}
        case O.Running{again}:
          False{}
        case O.Ran{}:
          False{}
        case O.Unsure{}:
          True{}
        case O.Void{}:
          False{}

# the effect has no record, or an end on record (finished, unknown,
# unstarted)
def wd_closed(w: S.World) -> Bool:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      match l:
        case O.Absent{}:
          True{}
        case O.Pending{}:
          False{}
        case O.Running{again}:
          False{}
        case O.Ran{}:
          True{}
        case O.Unsure{}:
          True{}
        case O.Void{}:
          True{}

# Tools: the once rule beside the tool gate
# -----------------------------------------

# the once policy of a tool's replay policy
def on_policy(r: Tc.Replay) -> O.Policy:
  match r:
    case Tc.Safe{}:
      O.Safe{}
    case Tc.Unsafe{}:
      O.Never{}

# the once policy of a call whose intent recorded the policy a and whose
# tool is offered now with b: safe only when both are
def on_both(a: Tc.Replay, b: Tc.Replay) -> O.Policy:
  match a:
    case Tc.Safe{}:
      on_policy(b)
    case Tc.Unsafe{}:
      O.Never{}

# a launch as the tool gate words it: a rerun of a begun call, else a run
def on_go.launch(begun: Bool) -> Tc.Go:
  match begun:
    case True{}:
      Tc.Rerun{}
    case False{}:
      Tc.Run{}

# a restart's verdict as the tool gate words it (begun: the call's intent
# was recorded): a launch is a run, or a rerun of a begun call; an
# interrupt is `interrupted`; an abandon is `abandoned`; the gate has no
# word for the others (`missing` is none of its answers for a found call)
def on_go(begun: Bool, v: O.Verdict) -> Tc.Go:
  match v:
    case O.Skip{}:
      Tc.Missing{}
    case O.Launch{}:
      on_go.launch(begun)
    case O.Adopt{}:
      Tc.Missing{}
    case O.Interrupt{}:
      Tc.Interrupted{}
    case O.Abandon{}:
      Tc.Abandoned{}
    case O.Settled{}:
      Tc.Missing{}

# The entry: the laws' reader, from the wire's primitives
# -------------------------------------------------------

def on_read_rec.tag(n: Nat, s: String) -> Wr.Dec<O.Rec>:
  match n:
    case 0n:
      Wr.Got{O.Intended{}, s}
    case 1n:
      Wr.Got{O.Started{}, s}
    case 2n:
      Wr.Got{O.Finished{}, s}
    case 3n:
      Wr.Got{O.Unknown{}, s}
    case 4n:
      Wr.Got{O.Unstarted{}, s}
    case 5n+p:
      Wr.Bad{}

def on_read_rec(r: Wr.Dec<Nat>) -> Wr.Dec<O.Rec>:
  match r:
    case Wr.Got{n, s}:
      on_read_rec.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def on_read_mode.tag(n: Nat, s: String) -> Wr.Dec<O.Mode>:
  match n:
    case 0n:
      Wr.Got{O.Resume{}, s}
    case 1n:
      Wr.Got{O.Stop{}, s}
    case 2n+p:
      Wr.Bad{}

def on_read_mode(r: Wr.Dec<Nat>) -> Wr.Dec<O.Mode>:
  match r:
    case Wr.Got{n, s}:
      on_read_mode.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def on_read_policy.cap(r: Wr.Dec<Nat>) -> Wr.Dec<O.Policy>:
  match r:
    case Wr.Got{cap, s}:
      Wr.Got{O.Keyed{cap}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def on_read_policy.tag(n: Nat, s: String) -> Wr.Dec<O.Policy>:
  match n:
    case 0n:
      Wr.Got{O.Never{}, s}
    case 1n:
      Wr.Got{O.Safe{}, s}
    case 2n:
      on_read_policy.cap(Wr.get_nat(s))
    case 3n+p:
      Wr.Bad{}

def on_read_policy(r: Wr.Dec<Nat>) -> Wr.Dec<O.Policy>:
  match r:
    case Wr.Got{n, s}:
      on_read_policy.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def on_read_seen.tag(n: Nat, s: String) -> Wr.Dec<O.Seen>:
  match n:
    case 0n:
      Wr.Got{O.Dark{}, s}
    case 1n:
      Wr.Got{O.Landed{}, s}
    case 2n:
      Wr.Got{O.Clean{}, s}
    case 3n+p:
      Wr.Bad{}

def on_read_seen(r: Wr.Dec<Nat>) -> Wr.Dec<O.Seen>:
  match r:
    case Wr.Got{n, s}:
      on_read_seen.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def on_read.note(r: Wr.Dec<O.Rec>) -> Wr.Dec<FO.Ev>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{FO.Note{x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def on_read.seen(m: O.Mode, p: O.Policy, r: Wr.Dec<O.Seen>) -> Wr.Dec<FO.Ev>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{FO.Ask{m, p, x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def on_read.policy(m: O.Mode, r: Wr.Dec<O.Policy>) -> Wr.Dec<FO.Ev>:
  match r:
    case Wr.Got{p, s}:
      on_read.seen(m, p, on_read_seen(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def on_read.mode(r: Wr.Dec<O.Mode>) -> Wr.Dec<FO.Ev>:
  match r:
    case Wr.Got{m, s}:
      on_read.policy(m, on_read_policy(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def on_read.tag(n: Nat, s: String) -> Wr.Dec<FO.Ev>:
  match n:
    case 0n:
      on_read.note(on_read_rec(Wr.get_nat(s)))
    case 1n:
      on_read.mode(on_read_mode(Wr.get_nat(s)))
    case 2n+p:
      Wr.Bad{}

def on_read.go(r: Wr.Dec<Nat>) -> Wr.Dec<FO.Ev>:
  match r:
    case Wr.Got{n, s}:
      on_read.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def on_read.end(whole: Bool, e: FO.Ev) -> Maybe<&2, FO.Ev>:
  match whole:
    case True{}:
      Some{e}
    case False{}:
      None{}

def on_read.whole(d: Wr.Dec<FO.Ev>) -> Maybe<&2, FO.Ev>:
  match d:
    case Wr.Got{e, s}:
      on_read.end(Wr.end(s), e)
    case Wr.Bad{}:
      None{}

# the event s is, when s is exactly one event
def on_read(s: String) -> Maybe<&2, FO.Ev>:
  on_read.whole(on_read.go(Wr.get_nat(s)))

# A key request: the scope, then the id
type OnKey is Data:
  OnKey{scope: String, id: String}

def on_read_key.end(whole: Bool, a: String, b: String) -> Maybe<&2, OnKey>:
  match whole:
    case True{}:
      Some{OnKey{a, b}}
    case False{}:
      None{}

def on_read_key.id(a: String, d: Wr.Dec<String>) -> Maybe<&2, OnKey>:
  match d:
    case Wr.Got{b, s}:
      on_read_key.end(Wr.end(s), a, b)
    case Wr.Bad{}:
      None{}

def on_read_key.scope(d: Wr.Dec<String>) -> Maybe<&2, OnKey>:
  match d:
    case Wr.Got{a, s}:
      on_read_key.id(a, Wr.get_str(s))
    case Wr.Bad{}:
      None{}

# the key request s is, when s is exactly two strings
def on_read_key(s: String) -> Maybe<&2, OnKey>:
  on_read_key.scope(Wr.get_str(s))

# Laws: the life and the restart (O1-O8)
# --------------------------------------

# LAW once_life_is_spec (O1, O6, O8): for every list of records, the life
# the model tells is the spec's: the first end on record decides it for
# good; with no end, an effect with a launch on record is running, with
# its launches counted; with no launch, one with a record is pending;
# with no record it is absent
# EXCLUDES: a life read off the last record (a finished effect running
# again after a stray start), a second end that replaces the first, a
# launch not counted or counted twice, an intended effect read as absent
# or as started, a prefix of a journal read as its whole
law once_life_is_spec:
  for +j: List<&2, O.Rec>
  {O.life(j) == S.life_spec(j) : O.Life}

# LAW once_recover_is_spec (O1-O7): for every life, every answer of the
# world, both modes and every policy, the model's verdict is the spec's
# EXCLUDES: a started `never` effect launched again when the world says
# nothing, a launch of an ended effect, a `done` for an effect the world
# does not show, an abandon of an effect that may have run, a pending
# effect interrupted or skipped, a safe effect not run again, a keyed
# effect sent past its cap or refused under it, a stopped run that
# launches
law once_recover_is_spec:
  for l: O.Life
  for s: O.Seen
  for m: O.Mode
  for p: O.Policy
  {O.recover(l, s, m, p) == S.verdict_spec(l, s, m, p) : O.Verdict}

# LAW once_ended_stays (O6, O8): once the records read tell an end,
# whatever records follow tell the same life
# EXCLUDES: an end overwritten by a later record (a finished effect read
# as interrupted after a stray `unknown`, an interrupted one read as
# finished), an ended effect started again by a later `started`
law once_ended_stays:
  for +j: List<&2, O.Rec>
  for +rest: List<&2, O.Rec>
  for ended: {S.settled(O.life(j)) == True{} : Bool}
  {O.life(List.append(&2, O.Rec, j, rest)) == O.life(j) : O.Life}

# LAW once_step_is_spec (O1-O8): the stepper, opened and sent any records
# and any questions in any order (every cap fitting the wire), answers
# each as the spec asks for the records sent before it: a record with the
# life of the records read so far, a question with the restart's verdict
# for them, which changes nothing
# EXCLUDES: a decision that differs after some prefix of a journal (a
# crash point the rule forgot), a question that moves the life, a record
# lost, doubled or read as another, a field misread, a reply spelled
# otherwise, a stepper whose state drifts after some order of events
law once_step_is_spec:
  for +es: List<&2, FO.Ev>
  for fits: {on_fit(es) == True{} : Bool}
  {on_replies(es, on_opened()) == on_spec(es, Nil{}) : List<&2, String>}

# Laws: the world of one effect (O2-O7)
# -------------------------------------

# LAW once_never_takes_hold_twice (O2): in every history of a `never`
# effect (any order of intents, runs, resumes, stops, looks at the world,
# lands, ends and crashes), it takes hold in the world at most once
# EXCLUDES: a bash command, an edit or a spawn done a second time after a
# crash mid-run, after its end, after a look that showed it landed, or
# beside a launch still in flight
law once_never_takes_hold_twice:
  for +es: List<&2, S.Ev>
  {Nat.is_le(S.lands(wd_run(es, S.w0(), O.Never{})), 1n) == True{} : Bool}

# LAW once_never_launches_twice (O2): in every history in which the world
# is never asked, a `never` effect is launched at most once
# EXCLUDES: a second launch of an effect that may have partially run (a
# rerun after a crash before its end was journaled, after a stop, after
# its end)
law once_never_launches_twice:
  for +es: List<&2, S.Ev>
  {Nat.is_le(S.launches(wd_run(S.dim(es), S.w0(), O.Never{})), 1n) == True{} : Bool}

# LAW once_keyed_sends_capped (O7): in every history in which the world
# is never asked, a keyed effect of any cap is sent at most 1 + cap times
# EXCLUDES: a crash loop that sends (and bills) one request without
# bound, a cap off by one, a count that restarts after a crash
law once_keyed_sends_capped:
  for +cap: Nat
  for +es: List<&2, S.Ev>
  {Nat.is_le(S.launches(wd_run(S.dim(es), S.w0(), O.Keyed{cap})), 1n+cap) == True{} : Bool}

# LAW once_done_ran (O3): in every history of an effect of any policy,
# when its journal says finished it took hold in the world
# EXCLUDES: an effect reported done that never ran (a result claimed for
# a call cut before its launch, an adopt without the world showing it)
law once_done_ran:
  for +p: O.Policy
  for +es: List<&2, S.Ev>
  {Bool.or(Bool.not(S.is_ran(S.life(wd_run(es, S.w0(), p)))), Nat.is_le(1n, S.lands(wd_run(es, S.w0(), p)))) == True{} : Bool}

# LAW once_unstarted_never_ran (O3): in every history of an effect of any
# policy, when its journal says unstarted it never took hold in the world
# EXCLUDES: "it was not started" said of an effect that ran or partially
# ran (an abandon of a started effect the world was not asked about, or
# that the world shows landed)
law once_unstarted_never_ran:
  for +p: O.Policy
  for +es: List<&2, S.Ev>
  {Bool.or(Bool.not(S.is_void(S.life(wd_run(es, S.w0(), p)))), Nat.is_eq(S.lands(wd_run(es, S.w0(), p)), 0n)) == True{} : Bool}

# LAW once_ends_once (O6): in every history of an effect of any policy,
# at most one end is journaled
# EXCLUDES: a second result for one effect (an interrupted answer after a
# finished one, an adopt after an interrupt, an end journaled by a
# restart for an effect that already ended)
law once_ends_once:
  for +p: O.Policy
  for +es: List<&2, S.Ev>
  {Nat.is_le(S.ends(wd_run(es, S.w0(), p)), 1n) == True{} : Bool}

# LAW once_ended_never_launches (O6): in every history of an effect of
# any policy, no launch is made once its end is journaled
# EXCLUDES: a safe or keyed effect run again after it finished, an
# interrupted effect run again by a later restart, a launch of an effect
# reported not started
law once_ended_never_launches:
  for +p: O.Policy
  for +es: List<&2, S.Ev>
  {S.late(wd_run(es, S.w0(), p)) == 0n : Nat}

# LAW once_unrun_resumes (O5): after every history of an effect of any
# policy, an effect that waits (intended, never launched, nothing in
# flight) is launched by the next resume of its run, whatever the world
# shows
# EXCLUDES: an intended effect dropped by a crash before its start (a
# tool call, a queued message or a fire that never runs and is never
# reported), one reported interrupted though it never started
law once_unrun_resumes:
  for +p: O.Policy
  for +es: List<&2, S.Ev>
  for look: Bool
  {Bool.or(Bool.not(wd_waits(wd_run(es, S.w0(), p))), wd_live(wd_step(wd_run(es, S.w0(), p), S.Tick{O.Resume{}, look}, p))) == True{} : Bool}

# LAW once_unknown_is_said (O4): after every history of a `never` effect,
# an effect that was cut (started, no end on record, nothing in flight)
# is journaled unknown by the next run of either mode that cannot ask the
# world, and no launch is made
# EXCLUDES: a cut effect left running for ever (never reported), launched
# again, or reported finished
law once_unknown_is_said:
  for +es: List<&2, S.Ev>
  for m: O.Mode
  {Bool.or(Bool.not(wd_cut(wd_run(es, S.w0(), O.Never{}))), Bool.and(wd_lost(wd_step(wd_run(es, S.w0(), O.Never{}), S.Tick{m, False{}}, O.Never{})), Bool.not(wd_live(wd_step(wd_run(es, S.w0(), O.Never{}), S.Tick{m, False{}}, O.Never{}))))) == True{} : Bool}

# LAW once_stop_settles (O4, O5): after every history of an effect of
# any policy, a stop of its run that comes to it with nothing in flight,
# the world asked or not, leaves it with no record or with an end on
# record (finished, unknown or unstarted), nothing in flight, and the
# launches made unchanged
# EXCLUDES: a stop that leaves a started effect with no end (skipped, or
#   called settled), a stop that launches a pending effect, or sends a
#   keyed one again or runs a safe one again, a pending effect a stop
#   leaves waiting
law once_stop_settles:
  for +p: O.Policy
  for +es: List<&2, S.Ev>
  for look: Bool
  {Bool.or(wd_live(wd_run(es, S.w0(), p)), Bool.and(wd_closed(wd_step(wd_run(es, S.w0(), p), S.Tick{O.Stop{}, look}, p)), Bool.and(Bool.not(wd_live(wd_step(wd_run(es, S.w0(), p), S.Tick{O.Stop{}, look}, p))), Nat.is_eq(S.launches(wd_step(wd_run(es, S.w0(), p), S.Tick{O.Stop{}, look}, p)), S.launches(wd_run(es, S.w0(), p)))))) == True{} : Bool}

# Laws: tools (H1 beside O2-O5)
# -----------------------------

# LAW once_tool_gate_agrees (O2, O4, O5): for a call a committed entry
# holds, the once rule and the tool gate (bend/tool_call.bend, H1) say the
# same: after a restart found the intent, a rerun exactly when the stored
# and the current policy are both safe, else interrupted (a tool no
# longer offered never reruns); a stopped run's call interrupted when its
# intent was recorded, abandoned when it was not; a first run runs
# EXCLUDES: the two rules of one tool call drifting apart (a call the
# gate interrupts and the once rule launches, or the reverse)
law once_tool_gate_agrees:
  for stored: Tc.Replay
  for now: Tc.Replay
  for s: O.Seen
  for p: O.Policy
  for again: Nat
  {on_go(True{}, O.recover(O.Running{again}, O.Dark{}, O.Resume{}, on_both(stored, now))) == Tc.gate(Tc.Recover{True{}, stored, Tc.Offered{now}}) : Tc.Go} &
  {on_go(True{}, O.recover(O.Running{again}, O.Dark{}, O.Resume{}, O.Never{})) == Tc.gate(Tc.Recover{True{}, stored, Tc.Gone{}}) : Tc.Go} &
  {on_go(True{}, O.recover(O.Running{again}, O.Dark{}, O.Stop{}, p)) == Tc.gate(Tc.Stop{True{}, True{}, True{}}) : Tc.Go} &
  {on_go(False{}, O.recover(O.Pending{}, s, O.Stop{}, p)) == Tc.gate(Tc.Stop{True{}, True{}, False{}}) : Tc.Go} &
  {on_go(False{}, O.recover(O.Pending{}, s, O.Resume{}, p)) == Tc.gate(Tc.Enter{True{}, Tc.Offered{now}}) : Tc.Go}

# Laws: the idempotency key (O7)
# ------------------------------

# LAW once_key_distinct (O7): two key requests (strings whose lengths fit
# the wire) that the entry answers with the same key name the same scope
# and the same id
# EXCLUDES: two effects sharing a key (a scope and an id glued with no
# length: "ab" + "c" and "a" + "bc"; a key that drops the scope or the
# id; a constant key), so a receiver that drops a repeat never drops
# another effect
law once_key_distinct:
  for +a: String
  for +b: String
  for +c: String
  for +d: String
  for fa: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}
  for fb: {LawsBase.wire_fits(String.length(b)) == True{} : Bool}
  for fc: {LawsBase.wire_fits(String.length(c)) == True{} : Bool}
  for fd: {LawsBase.wire_fits(String.length(d)) == True{} : Bool}
  for same: {FO.ffi(on_spell_key(a, b)) == FO.ffi(on_spell_key(c, d)) : String}
  {a == c : String} & {b == d : String}

# LAW once_key_never_err (O7): every key request (two strings whose
# lengths fit the wire) is answered with a key, never with the error form
# (a reply that opens with 'E', which Rust reads as an error)
# EXCLUDES: a key answered as an error for a long id, for an empty scope
#   or for any request but the example's, however distinct the keys stay
#   (the effect then fails, or goes out with no key)
law once_key_never_err:
  for +a: String
  for +b: String
  for fa: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}
  for fb: {LawsBase.wire_fits(String.length(b)) == True{} : Bool}
  {LawsBase.wire_opens_err(FO.ffi(on_spell_key(a, b))) == False{} : Bool}

# LAW once_key_reads (O7): a call input the laws' reader reads as exactly
# two strings is answered as those strings spelled
# EXCLUDES: an input read otherwise by the entry than by the wire's
# grammar
law once_key_reads:
  for +i: String
  for +a: String
  for +b: String
  for got: {on_read_key(i) == Some{OnKey{a, b}} : Maybe<&2, OnKey>}
  {FO.ffi(i) == FO.ffi(on_spell_key(a, b)) : String}

# LAW once_key_malformed_exact (O7): a call input the laws' reader does
# not read as exactly two strings (a short or bad string, input left
# over) answers exactly the error form 'E ' + "once: malformed key"
# EXCLUDES: a key guessed for garbage, another error text
law once_key_malformed_exact:
  for +i: String
  for no: {on_read_key(i) == None{} : Maybe<&2, OnKey>}
  {FO.ffi(i) == SCon{'E', SCon{' ', "once: malformed key"}} : String}

# Laws: the entry
# ---------------

# LAW once_entry_reads: in every state, an input the laws' reader reads
# as exactly one event is answered as that event spelled
# EXCLUDES: an input read otherwise by the entry than by the wire's
# grammar
law once_entry_reads:
  for +l: O.Life
  for +i: String
  for +e: FO.Ev
  for got: {on_read(i) == Some{e} : Maybe<&2, FO.Ev>}
  {FO.step(FO.Eff{l}, i) == FO.step(FO.Eff{l}, on_spell(e)) : FO.St & String}

# LAW once_entry_malformed_exact: in every state, an input the laws'
# reader does not read as exactly one event (a bad tag, a short or bad
# field, input left over) keeps the life and answers exactly the error
# form 'E ' + "once: malformed event"
# EXCLUDES: a guessed event (garbage that journals a record or answers a
# launch), a life moved by garbage, another error text
law once_entry_malformed_exact:
  for +l: O.Life
  for +i: String
  for no: {on_read(i) == None{} : Maybe<&2, FO.Ev>}
  {FO.step(FO.Eff{l}, i) == (FO.Eff{l}, SCon{'E', SCon{' ', "once: malformed event"}}) : FO.St & String}

# LAW once_entry_open_exact: an open with no input opens an effect with no
# record and answers its life; an open with any input opens the refused
# state and answers exactly the error form 'E ' + "once: malformed open"
# EXCLUDES: an effect that opens with a record (pending or started before
# any record was sent), a default for garbage
law once_entry_open_exact:
  for +c: Char
  for +i: String
  {FO.open("") == (FO.Eff{O.Absent{}}, "0,") : FO.St & String} &
  {FO.open(SCon{c, i}) == (FO.Refused{}, SCon{'E', SCon{' ', "once: malformed open"}}) : FO.St & String}

# LAW once_entry_shut: a refused open answers every step with exactly the
# error form 'E ' + "once: the open was refused"
# EXCLUDES: a refused stepper that reads a record or answers a verdict
law once_entry_shut:
  for +i: String
  {FO.step(FO.Refused{}, i) == (FO.Refused{}, SCon{'E', SCon{' ', "once: the open was refused"}}) : FO.St & String}

# LAW once_entry_example: anchor: the bytes Rust sends and the replies: a
# tool call cut mid-run (intended, started, then the restart: a `never`
# call interrupted, a safe one launched, a stopped run's interrupted); a
# call cut before its start (launched by a resume, abandoned by a stop);
# a file write the world shows landed (adopted) or clean (launched); a
# provider request sent twice asked again under cap 1 and cap 2; an ended
# effect; a record after an end; garbage: a bad tag, a short question,
# input left over; the key of scope "s1" and id "t:9", and a key request
# with input left over
# EXCLUDES: an entry that answers other bytes than the grammar's
law once_entry_example:
  {on_replies([FO.Note{O.Intended{}}, FO.Note{O.Started{}}, FO.Ask{O.Resume{}, O.Never{}, O.Dark{}}, FO.Ask{O.Resume{}, O.Safe{}, O.Dark{}}, FO.Ask{O.Stop{}, O.Safe{}, O.Dark{}}, FO.Ask{O.Resume{}, O.Never{}, O.Landed{}}, FO.Ask{O.Resume{}, O.Never{}, O.Clean{}}, FO.Note{O.Started{}}, FO.Ask{O.Resume{}, O.Keyed{1n}, O.Dark{}}, FO.Ask{O.Resume{}, O.Keyed{2n}, O.Dark{}}, FO.Note{O.Unknown{}}, FO.Note{O.Finished{}}, FO.Ask{O.Resume{}, O.Safe{}, O.Landed{}}], on_opened()) == ["1,", "2,0,", "3,", "1,", "3,", "2,", "1,", "2,1,", "3,", "1,", "4,", "4,", "5,"] : List<&2, String>} &
  {on_replies([FO.Note{O.Intended{}}, FO.Ask{O.Resume{}, O.Never{}, O.Dark{}}, FO.Ask{O.Stop{}, O.Never{}, O.Dark{}}], on_opened()) == ["1,", "1,", "4,"] : List<&2, String>} &
  {[on_reply(FO.step(on_opened(), "0,1,")), on_reply(FO.step(on_opened(), "1,0,2,3,0,")), on_reply(FO.step(on_opened(), "2,")), on_reply(FO.step(on_opened(), "1,0,")), on_reply(FO.step(on_opened(), "0,1,x")), on_reply(FO.step(on_opened(), "0,5,"))] == ["2,0,", "0,", SCon{'E', SCon{' ', "once: malformed event"}}, SCon{'E', SCon{' ', "once: malformed event"}}, SCon{'E', SCon{' ', "once: malformed event"}}, SCon{'E', SCon{' ', "once: malformed event"}}] : List<&2, String>} &
  {[FO.ffi("2,s13,t:9"), FO.ffi("2,s13,t:9x"), FO.ffi("2,s1")] == ["2,s13,t:9", SCon{'E', SCon{' ', "once: malformed key"}}, SCon{'E', SCon{' ', "once: malformed key"}}] : List<&2, String>}
