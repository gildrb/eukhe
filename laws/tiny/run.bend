# eukhe: the laws of area tiny, section run: the run of one process's
# election and of a started worker's seat (bend/tiny.bend section 4), R7
# and R5 of laws/tiny/elect.bend, and its stepper entry
# (bend/ffi_tiny_run.bend)

import Base
import ../../bend/ffi_tiny_run.bend as FTr
import ../../bend/tiny.bend as Tn
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase
import ./elect.bend as TinyElect

# The spelling of an outcome, an open and a reply, from the wire
# primitives (R5): a probe is its tag (Pong: then its tag text); an
# outcome or a reply is its tag, then its fields.

def sp_w_probe(p: Tn.Probe, rest: String) -> String:
  match p:
    case Tn.Missing{}:
      Wr.put_nat(0n, rest)
    case Tn.Unreachable{}:
      Wr.put_nat(1n, rest)
    case Tn.Pong{t}:
      Wr.put_nat(2n, Wr.put_str(t, rest))
    case Tn.Odd{}:
      Wr.put_nat(3n, rest)
    case Tn.Garbled{}:
      Wr.put_nat(4n, rest)
    case Tn.Hung{}:
      Wr.put_nat(5n, rest)

def sp_w_heard(h: Tn.Heard) -> Nat:
  match h:
    case Tn.Bye{}:
      0n
    case Tn.Other{}:
      1n
    case Tn.Eof{}:
      2n
    case Tn.Lost{}:
      3n

def sp_w_got(g: Tn.Got) -> Nat:
  match g:
    case Tn.Started{}:
      0n
    case Tn.Joined{}:
      1n
    case Tn.Replaced{}:
      2n

def sp_w_why(w: Tn.Why) -> Nat:
  match w:
    case Tn.WhyIo{}:
      0n
    case Tn.WhyProtocol{}:
      1n
    case Tn.WhyMistagged{}:
      2n
    case Tn.WhyVacant{}:
      3n
    case Tn.WhySpawn{}:
      4n

def sp_w_launch(l: Tn.Launch) -> Nat:
  match l:
    case Tn.Bound{}:
      0n
    case Tn.Adopted{}:
      1n

def sp_w_seen(s: Tn.Seen, rest: String) -> String:
  match s:
    case Tn.Pinged{p}:
      Wr.put_nat(0n, sp_w_probe(p, rest))
    case Tn.ShutHeard{h}:
      Wr.put_nat(1n, Wr.put_nat(sp_w_heard(h), rest))
    case Tn.Came{l}:
      Wr.put_nat(2n, Wr.put_nat(sp_w_launch(l), rest))
    case Tn.NoSpawn{}:
      Wr.put_nat(3n, rest)
    case Tn.Locked{}:
      Wr.put_nat(4n, rest)

def sp_w_open(o: FTr.Open, rest: String) -> String:
  match o:
    case FTr.ONeed{m}:
      Wr.put_nat(0n, Wr.put_str(m, rest))
    case FTr.OSeat{}:
      Wr.put_nat(1n, rest)

# the reply Rust reads
def sp_w_do(d: Tn.Do) -> String:
  match d:
    case Tn.DoPing{}:
      Wr.put_nat(0n, "")
    case Tn.DoShutdown{}:
      Wr.put_nat(1n, "")
    case Tn.DoLaunch{}:
      Wr.put_nat(2n, "")
    case Tn.DoUse{g}:
      Wr.put_nat(3n, Wr.put_nat(sp_w_got(g), ""))
    case Tn.DoFail{w}:
      Wr.put_nat(4n, Wr.put_nat(sp_w_why(w), ""))
    case Tn.DoLock{}:
      Wr.put_nat(5n, "")
    case Tn.DoAdopt{}:
      Wr.put_nat(6n, "")
    case Tn.DoTake{}:
      Wr.put_nat(7n, "")
    case Tn.DoFault{}:
      Wr.put_nat(8n, "")
    case Tn.DoNothing{}:
      Wr.put_nat(9n, "")

def sp_w_dos(ds: List<&2, Tn.Do>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> t:
      sp_w_do(d) <> sp_w_dos(t)

def sp_fit_probe(p: Tn.Probe) -> Bool:
  match p:
    case Tn.Missing{}:
      True{}
    case Tn.Unreachable{}:
      True{}
    case Tn.Pong{t}:
      LawsBase.wire_fits(String.length(t))
    case Tn.Odd{}:
      True{}
    case Tn.Garbled{}:
      True{}
    case Tn.Hung{}:
      True{}

def sp_fit_seen(s: Tn.Seen) -> Bool:
  match s:
    case Tn.Pinged{p}:
      sp_fit_probe(p)
    case Tn.ShutHeard{h}:
      True{}
    case Tn.Came{l}:
      True{}
    case Tn.NoSpawn{}:
      True{}
    case Tn.Locked{}:
      True{}

def sp_all_fit(ss: List<&2, Tn.Seen>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case s <> t:
      Bool.and(sp_fit_seen(s), sp_all_fit(t))

def sp_fit_open(o: FTr.Open) -> Bool:
  match o:
    case FTr.ONeed{m}:
      LawsBase.wire_fits(String.length(m))
    case FTr.OSeat{}:
      True{}

# The run (R7)
# ------------

def sp_r(+m: String, ph: Tn.Phase, d: Tn.Do) -> Tn.Run & Tn.Do:
  (Tn.Run{m, ph}, d)

# what an open starts: a need pings, a seat takes the lock
def sp_open(o: FTr.Open) -> Tn.Run & Tn.Do:
  match o:
    case FTr.ONeed{m}:
      (Tn.Run{m, Tn.Probing{}}, Tn.DoPing{})
    case FTr.OSeat{}:
      (Tn.Run{"", Tn.Locking{}}, Tn.DoLock{})

def sp_by_elect(+m: String, a: Tn.Act) -> Tn.Run & Tn.Do:
  match a:
    case Tn.Join{}:
      sp_r(m, Tn.Over{}, Tn.DoUse{Tn.Joined{}})
    case Tn.Replace{}:
      sp_r(m, Tn.Shutting{}, Tn.DoShutdown{})
    case Tn.Start{}:
      sp_r(m, Tn.Launching{Tn.First{}}, Tn.DoLaunch{})
    case Tn.Broken{}:
      sp_r(m, Tn.Over{}, Tn.DoFail{Tn.WhyIo{}})

def sp_by_shut(+m: String, x: Tn.Shut) -> Tn.Run & Tn.Do:
  match x:
    case Tn.Down{}:
      sp_r(m, Tn.Launching{Tn.Again{}}, Tn.DoLaunch{})
    case Tn.Spoke{}:
      sp_r(m, Tn.Over{}, Tn.DoFail{Tn.WhyProtocol{}})
    case Tn.Cut{}:
      sp_r(m, Tn.Over{}, Tn.DoFail{Tn.WhyIo{}})

def sp_by_check(+m: String, g: Tn.Got, c: Tn.Check) -> Tn.Run & Tn.Do:
  match c:
    case Tn.Serving{}:
      sp_r(m, Tn.Over{}, Tn.DoUse{g})
    case Tn.Mistagged{}:
      sp_r(m, Tn.Over{}, Tn.DoFail{Tn.WhyMistagged{}})
    case Tn.Vacant{}:
      sp_r(m, Tn.Over{}, Tn.DoFail{Tn.WhyVacant{}})
    case Tn.Faulty{}:
      sp_r(m, Tn.Over{}, Tn.DoFail{Tn.WhyIo{}})

def sp_by_seat(+m: String, x: Tn.Seat) -> Tn.Run & Tn.Do:
  match x:
    case Tn.Adopt{}:
      sp_r(m, Tn.Over{}, Tn.DoAdopt{})
    case Tn.Take{}:
      sp_r(m, Tn.Over{}, Tn.DoTake{})
    case Tn.Fault{}:
      sp_r(m, Tn.Over{}, Tn.DoFault{})

# what a run of tag m in phase ph makes of outcome s: the outcome the
# phase waits for decides by R1-R4, R6; any other does nothing
def sp_step(+m: String, ph: Tn.Phase, s: Tn.Seen) -> Tn.Run & Tn.Do:
  match ph:
    case Tn.Probing{}:
      match s:
        case Tn.Pinged{p}:
          sp_by_elect(m, TinyElect.sp_elect(p, m))
        case Tn.ShutHeard{h}:
          sp_r(m, Tn.Probing{}, Tn.DoNothing{})
        case Tn.Came{l}:
          sp_r(m, Tn.Probing{}, Tn.DoNothing{})
        case Tn.NoSpawn{}:
          sp_r(m, Tn.Probing{}, Tn.DoNothing{})
        case Tn.Locked{}:
          sp_r(m, Tn.Probing{}, Tn.DoNothing{})
    case Tn.Shutting{}:
      match s:
        case Tn.Pinged{p}:
          sp_r(m, Tn.Shutting{}, Tn.DoNothing{})
        case Tn.ShutHeard{h}:
          sp_by_shut(m, TinyElect.sp_shut(h))
        case Tn.Came{l}:
          sp_r(m, Tn.Shutting{}, Tn.DoNothing{})
        case Tn.NoSpawn{}:
          sp_r(m, Tn.Shutting{}, Tn.DoNothing{})
        case Tn.Locked{}:
          sp_r(m, Tn.Shutting{}, Tn.DoNothing{})
    case Tn.Launching{f}:
      match s:
        case Tn.Pinged{p}:
          sp_r(m, Tn.Launching{f}, Tn.DoNothing{})
        case Tn.ShutHeard{h}:
          sp_r(m, Tn.Launching{f}, Tn.DoNothing{})
        case Tn.Came{l}:
          sp_r(m, Tn.Checking{TinyElect.sp_launched(l, f)}, Tn.DoPing{})
        case Tn.NoSpawn{}:
          sp_r(m, Tn.Over{}, Tn.DoFail{Tn.WhySpawn{}})
        case Tn.Locked{}:
          sp_r(m, Tn.Launching{f}, Tn.DoNothing{})
    case Tn.Checking{g}:
      match s:
        case Tn.Pinged{p}:
          sp_by_check(m, g, TinyElect.sp_confirm(p, m))
        case Tn.ShutHeard{h}:
          sp_r(m, Tn.Checking{g}, Tn.DoNothing{})
        case Tn.Came{l}:
          sp_r(m, Tn.Checking{g}, Tn.DoNothing{})
        case Tn.NoSpawn{}:
          sp_r(m, Tn.Checking{g}, Tn.DoNothing{})
        case Tn.Locked{}:
          sp_r(m, Tn.Checking{g}, Tn.DoNothing{})
    case Tn.Locking{}:
      match s:
        case Tn.Pinged{p}:
          sp_r(m, Tn.Locking{}, Tn.DoNothing{})
        case Tn.ShutHeard{h}:
          sp_r(m, Tn.Locking{}, Tn.DoNothing{})
        case Tn.Came{l}:
          sp_r(m, Tn.Locking{}, Tn.DoNothing{})
        case Tn.NoSpawn{}:
          sp_r(m, Tn.Locking{}, Tn.DoNothing{})
        case Tn.Locked{}:
          sp_r(m, Tn.Seating{}, Tn.DoPing{})
    case Tn.Seating{}:
      match s:
        case Tn.Pinged{p}:
          sp_by_seat(m, TinyElect.sp_bind(p))
        case Tn.ShutHeard{h}:
          sp_r(m, Tn.Seating{}, Tn.DoNothing{})
        case Tn.Came{l}:
          sp_r(m, Tn.Seating{}, Tn.DoNothing{})
        case Tn.NoSpawn{}:
          sp_r(m, Tn.Seating{}, Tn.DoNothing{})
        case Tn.Locked{}:
          sp_r(m, Tn.Seating{}, Tn.DoNothing{})
    case Tn.Over{}:
      sp_r(m, Tn.Over{}, Tn.DoNothing{})

def sp_step_r(x: Tn.Run, s: Tn.Seen) -> Tn.Run & Tn.Do:
  match x:
    case Tn.Run{m, ph}:
      sp_step(m, ph, s)

# the entry's state and reply for a run and what Rust does next
def sp_reply(r: Tn.Run & Tn.Do) -> FTr.St & String:
  (x, d) = r
  (FTr.Live{x}, sp_w_do(d))

def tr_snd(r: FTr.St & String) -> String:
  (st, out) = r
  out

# the reply of r, then the replies of the model's run to ss from its run
def tr_replies(ss: List<&2, Tn.Seen>, r: Tn.Run & Tn.Do) -> List<&2, Tn.Do>:
  match ss:
    case Nil{}:
      (x, d) = r
      [d]
    case s <> t:
      (x, d) = r
      d <> tr_replies(t, Tn.step_run(x, s))

# the reply of r, then the shipped stepper's replies to ss spelled on the
# wire, from the state of r
def tr_feed(ss: List<&2, Tn.Seen>, r: FTr.St & String) -> List<&2, String>:
  match ss:
    case Nil{}:
      (st, out) = r
      [out]
    case s <> t:
      (st, out) = r
      out <> tr_feed(t, FTr.step(st, sp_w_seen(s, "")))

# the replies of the shipped stepper to raw inputs, from the state of r
def tr_raw(ins: List<&2, String>, r: FTr.St & String) -> List<&2, String>:
  match ins:
    case Nil{}:
      (st, out) = r
      [out]
    case i <> t:
      (st, out) = r
      out <> tr_raw(t, FTr.step(st, i))

# what the uses of ds got, in order
def tr_used(ds: List<&2, Tn.Do>) -> List<&2, Tn.Got>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> t:
      match d:
        case Tn.DoUse{g}:
          g <> tr_used(t)
        case Tn.DoPing{}:
          tr_used(t)
        case Tn.DoShutdown{}:
          tr_used(t)
        case Tn.DoLaunch{}:
          tr_used(t)
        case Tn.DoFail{w}:
          tr_used(t)
        case Tn.DoLock{}:
          tr_used(t)
        case Tn.DoAdopt{}:
          tr_used(t)
        case Tn.DoTake{}:
          tr_used(t)
        case Tn.DoFault{}:
          tr_used(t)
        case Tn.DoNothing{}:
          tr_used(t)

# s is a ping a worker answered with a tag that is m (want) or is not
def tr_pong(+m: String, want: Bool, s: Tn.Seen) -> Bool:
  match s:
    case Tn.Pinged{p}:
      match p:
        case Tn.Pong{t}:
          Bool.not(Bool.xor(LawsBase.text_same(t, m), want))
        case Tn.Missing{}:
          False{}
        case Tn.Unreachable{}:
          False{}
        case Tn.Odd{}:
          False{}
        case Tn.Garbled{}:
          False{}
        case Tn.Hung{}:
          False{}
    case Tn.ShutHeard{h}:
      False{}
    case Tn.Came{l}:
      False{}
    case Tn.NoSpawn{}:
      False{}
    case Tn.Locked{}:
      False{}

# s shows no live worker on the socket: no socket, a hang-up, or a
# shutdown the worker answered with bye or its own exit
def tr_vacant(s: Tn.Seen) -> Bool:
  match s:
    case Tn.Pinged{p}:
      match p:
        case Tn.Missing{}:
          True{}
        case Tn.Hung{}:
          True{}
        case Tn.Pong{t}:
          False{}
        case Tn.Unreachable{}:
          False{}
        case Tn.Odd{}:
          False{}
        case Tn.Garbled{}:
          False{}
    case Tn.ShutHeard{h}:
      match h:
        case Tn.Bye{}:
          True{}
        case Tn.Eof{}:
          True{}
        case Tn.Other{}:
          False{}
        case Tn.Lost{}:
          False{}
    case Tn.Came{l}:
      False{}
    case Tn.NoSpawn{}:
      False{}
    case Tn.Locked{}:
      False{}

# a reply d to outcome s in a run of tag m that R7 allows: a use only
# after a ping its own tag answered, a shutdown only after a ping another
# tag answered, a launch only after the socket showed no live worker
def tr_allowed(+m: String, +s: Tn.Seen, d: Tn.Do) -> Bool:
  match d:
    case Tn.DoUse{g}:
      tr_pong(m, True{}, s)
    case Tn.DoShutdown{}:
      tr_pong(m, False{}, s)
    case Tn.DoLaunch{}:
      tr_vacant(s)
    case Tn.DoPing{}:
      True{}
    case Tn.DoFail{w}:
      True{}
    case Tn.DoLock{}:
      True{}
    case Tn.DoAdopt{}:
      True{}
    case Tn.DoTake{}:
      True{}
    case Tn.DoFault{}:
      True{}
    case Tn.DoNothing{}:
      True{}

def tr_mine(x: Tn.Run) -> String:
  match x:
    case Tn.Run{m, ph}:
      m

def tr_run(r: Tn.Run & Tn.Do) -> Tn.Run:
  (x, d) = r
  x

def tr_do(r: Tn.Run & Tn.Do) -> Tn.Do:
  (x, d) = r
  d

# every reply of the run x to ss is allowed
def tr_safe(ss: List<&2, Tn.Seen>, +x: Tn.Run) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case +s <> t:
      Bool.and(tr_allowed(tr_mine(x), s, tr_do(Tn.step_run(x, s))), tr_safe(t, tr_run(Tn.step_run(x, s))))

# 1 when d is a launch (k = 0), a shutdown (1) or a ping (2)
def tr_is(d: Tn.Do, k: Nat) -> Nat:
  match d:
    case Tn.DoLaunch{}:
      match k:
        case 0n:
          1n
        case 1n+j:
          0n
    case Tn.DoShutdown{}:
      match k:
        case 0n:
          0n
        case 1n+j:
          match j:
            case 0n:
              1n
            case 1n+i:
              0n
    case Tn.DoPing{}:
      match k:
        case 0n:
          0n
        case 1n+j:
          match j:
            case 0n:
              0n
            case 1n+i:
              1n
    case Tn.DoUse{g}:
      0n
    case Tn.DoFail{w}:
      0n
    case Tn.DoLock{}:
      0n
    case Tn.DoAdopt{}:
      0n
    case Tn.DoTake{}:
      0n
    case Tn.DoFault{}:
      0n
    case Tn.DoNothing{}:
      0n

# how many replies of the run x to ss are of kind k
def tr_count(+k: Nat, ss: List<&2, Tn.Seen>, +x: Tn.Run) -> Nat:
  match ss:
    case Nil{}:
      0n
    case +s <> t:
      Nat.add(tr_is(tr_do(Tn.step_run(x, s)), k), tr_count(k, t, tr_run(Tn.step_run(x, s))))

# d ends a run
def tr_ends(d: Tn.Do) -> Bool:
  match d:
    case Tn.DoUse{g}:
      True{}
    case Tn.DoFail{w}:
      True{}
    case Tn.DoAdopt{}:
      True{}
    case Tn.DoTake{}:
      True{}
    case Tn.DoFault{}:
      True{}
    case Tn.DoPing{}:
      False{}
    case Tn.DoShutdown{}:
      False{}
    case Tn.DoLaunch{}:
      False{}
    case Tn.DoLock{}:
      False{}
    case Tn.DoNothing{}:
      False{}

def tr_nothing(d: Tn.Do) -> Bool:
  match d:
    case Tn.DoNothing{}:
      True{}
    case Tn.DoPing{}:
      False{}
    case Tn.DoShutdown{}:
      False{}
    case Tn.DoLaunch{}:
      False{}
    case Tn.DoUse{g}:
      False{}
    case Tn.DoFail{w}:
      False{}
    case Tn.DoLock{}:
      False{}
    case Tn.DoAdopt{}:
      False{}
    case Tn.DoTake{}:
      False{}
    case Tn.DoFault{}:
      False{}

def tr_once.at(ended: Bool, +d: Tn.Do) -> Bool:
  match ended:
    case True{}:
      tr_nothing(d)
    case False{}:
      True{}

# once a reply of the run x to ss ended it (ended: one before did), every
# later reply is nothing
def tr_once(ss: List<&2, Tn.Seen>, +x: Tn.Run, +ended: Bool) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case +s <> t:
      Bool.and(tr_once.at(ended, tr_do(Tn.step_run(x, s))), tr_once(t, tr_run(Tn.step_run(x, s)), Bool.or(ended, tr_ends(tr_do(Tn.step_run(x, s))))))

def tr_is_lock(s: Tn.Seen) -> Bool:
  match s:
    case Tn.Locked{}:
      True{}
    case Tn.Pinged{p}:
      False{}
    case Tn.ShutHeard{h}:
      False{}
    case Tn.Came{l}:
      False{}
    case Tn.NoSpawn{}:
      False{}

def tr_is_ping(s: Tn.Seen) -> Bool:
  match s:
    case Tn.Pinged{p}:
      True{}
    case Tn.Locked{}:
      False{}
    case Tn.ShutHeard{h}:
      False{}
    case Tn.Came{l}:
      False{}
    case Tn.NoSpawn{}:
      False{}

# a reply d to outcome s of a seat run that R7 allows (held: the run got
# the lock before s): a ping only when the lock is got, a seat only on a
# ping under the lock, nothing of a need
def tr_seat_ok(held: Bool, +s: Tn.Seen, d: Tn.Do) -> Bool:
  match d:
    case Tn.DoPing{}:
      tr_is_lock(s)
    case Tn.DoAdopt{}:
      Bool.and(held, tr_is_ping(s))
    case Tn.DoTake{}:
      Bool.and(held, tr_is_ping(s))
    case Tn.DoFault{}:
      Bool.and(held, tr_is_ping(s))
    case Tn.DoNothing{}:
      True{}
    case Tn.DoShutdown{}:
      False{}
    case Tn.DoLaunch{}:
      False{}
    case Tn.DoUse{g}:
      False{}
    case Tn.DoFail{w}:
      False{}
    case Tn.DoLock{}:
      False{}

# every reply of the seat run x to ss is allowed
def tr_seat(ss: List<&2, Tn.Seen>, +x: Tn.Run, +held: Bool) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case +s <> t:
      Bool.and(tr_seat_ok(held, s, tr_do(Tn.step_run(x, s))), tr_seat(t, tr_run(Tn.step_run(x, s)), Bool.or(held, tr_is_lock(s))))

# Laws: the run (R7)
# ------------------

# LAW tiny_run_step_is_model (R7): in every phase, each outcome makes the
# run's next phase and what Rust does next exactly as the spec's table
# EXCLUDES: an outcome the phase does not wait for acted on (a ping
#   answered twice, a late shutdown answer that launches again); a run
#   that forgets its tag or what its start got; a launch after a failed
#   one; a seat that pings before the lock
law tiny_run_step_is_model:
  for +m: String
  for +ph: Tn.Phase
  for +s: Tn.Seen
  {Tn.step_run(Tn.Run{m, ph}, s) == sp_step(m, ph, s) : Tn.Run & Tn.Do}

# LAW tiny_run_opens (R7): a need's run pings first with its tag kept; a
# seat run takes the bind lock first
# EXCLUDES: a need that launches unasked, a seat that pings or binds
#   before it holds the lock
law tiny_run_opens:
  for +m: String
  {Tn.need(m) == sp_open(FTr.ONeed{m}) : Tn.Run & Tn.Do} & {Tn.seat() == sp_open(FTr.OSeat{}) : Tn.Run & Tn.Do}

# LAW tiny_run_safe (R7): from any state, whatever outcomes come in any
# order, a run uses only a connection its own tag answered, shuts down
# only a worker that answered with another tag, and launches only when
# the socket showed no live worker
# EXCLUDES: a stale worker of another tag served; a worker of the
#   process's own tag shut down; a second worker started on top of a
#   live one (two workers on one socket)
law tiny_run_safe:
  for +x: Tn.Run
  for +ss: List<&2, Tn.Seen>
  {tr_safe(ss, x) == True{} : Bool}

# LAW tiny_run_at_most_once (R7): from any state, whatever outcomes come,
# a run launches at most once, shuts down at most once and pings at most
# once more
# EXCLUDES: a double start (two launches of one need), a double kill of
#   the old worker, a ping loop
law tiny_run_at_most_once:
  for +x: Tn.Run
  for +ss: List<&2, Tn.Seen>
  {[Nat.is_le(tr_count(0n, ss, x), 1n), Nat.is_le(tr_count(1n, ss, x), 1n), Nat.is_le(tr_count(2n, ss, x), 1n)] == [True{}, True{}, True{}] : List<&2, Bool>}

# LAW tiny_run_ends_once (R7): from any state, once a run ended (a use, a
# failure, a seat) every later outcome does nothing
# EXCLUDES: a need answered twice, a use after a failure, a launch after
#   the need was served
law tiny_run_ends_once:
  for +x: Tn.Run
  for +ss: List<&2, Tn.Seen>
  {tr_once(ss, x, False{}) == True{} : Bool}

# LAW tiny_run_ended_does_nothing (R7): an ended run does nothing,
# whatever comes
# EXCLUDES: a run revived by a late outcome
law tiny_run_ended_does_nothing:
  for +m: String
  for +s: Tn.Seen
  {Tn.step_run(Tn.Run{m, Tn.Over{}}, s) == (Tn.Run{m, Tn.Over{}}, Tn.DoNothing{}) : Tn.Run & Tn.Do}

# LAW tiny_seat_under_lock (R6, R7): a seat run, whatever outcomes come
# in any order, pings only once it got the bind lock, seats only on a
# ping under the lock, and does nothing a need does
# EXCLUDES: a check and a bind outside the lock (two workers bound on one
#   socket); a seat that launches, shuts down or serves
law tiny_seat_under_lock:
  for +ss: List<&2, Tn.Seen>
  {tr_seat(ss, Tn.Run{"", Tn.Locking{}}, False{}) == True{} : Bool}

# LAW tiny_run_is_model (R7, S9): the run of a need of tag m (text b)
# against the worker model, as its outcomes show it: with a worker of tag
# t (text a: the same text exactly when t = m) the ping meets it, a
# shutdown is answered bye, the launch binds, and the check meets the
# need's own tag; with no worker the ping meets no socket. The run uses
# exactly what the worker model's need gets
# EXCLUDES: an election whose run drifts from the worker model of
#   tiny_same_tag_joins and tiny_worker_current (the transcript the
#   Rust bridge compared, restated over the stepper)
law tiny_run_is_model:
  for +o: Nat
  for +t: Nat
  for +q: Nat
  for +m: Nat
  for +a: String
  for +b: String
  for named: {LawsBase.text_same(a, b) == Nat.is_eq(t, m) : Bool}
  {tr_used(tr_replies([Tn.Pinged{Tn.Pong{a}}, Tn.ShutHeard{Tn.Bye{}}, Tn.Came{Tn.Bound{}}, Tn.Pinged{Tn.Pong{b}}], Tn.need(b))) == Tn.got(Tn.Worker{o, t}, Tn.Need{q, m}) : List<&2, Tn.Got>} & {tr_used(tr_replies([Tn.Pinged{Tn.Missing{}}, Tn.Came{Tn.Bound{}}, Tn.Pinged{Tn.Pong{b}}], Tn.need(b))) == Tn.got(Tn.NoWorker{}, Tn.Need{q, m}) : List<&2, Tn.Got>}

# LAW tiny_run_example (R7): anchor: a replacement start to end, a start
# another worker beat (adopted: joined), a launch that fails, a seat that
# takes a free socket
# EXCLUDES: a table read in another order
law tiny_run_example:
  {[tr_replies([Tn.Pinged{Tn.Pong{"b"}}, Tn.ShutHeard{Tn.Eof{}}, Tn.Came{Tn.Bound{}}, Tn.Pinged{Tn.Pong{"a"}}, Tn.Locked{}], Tn.need("a")), tr_replies([Tn.Pinged{Tn.Hung{}}, Tn.Came{Tn.Adopted{}}, Tn.Pinged{Tn.Pong{"b"}}], Tn.need("a")), tr_replies([Tn.Pinged{Tn.Missing{}}, Tn.NoSpawn{}, Tn.Came{Tn.Bound{}}], Tn.need("a")), tr_replies([Tn.Pinged{Tn.Missing{}}, Tn.Locked{}, Tn.Pinged{Tn.Missing{}}], Tn.seat())] == [[Tn.DoPing{}, Tn.DoShutdown{}, Tn.DoLaunch{}, Tn.DoPing{}, Tn.DoUse{Tn.Replaced{}}, Tn.DoNothing{}], [Tn.DoPing{}, Tn.DoLaunch{}, Tn.DoPing{}, Tn.DoFail{Tn.WhyMistagged{}}], [Tn.DoPing{}, Tn.DoLaunch{}, Tn.DoFail{Tn.WhySpawn{}}, Tn.DoNothing{}], [Tn.DoLock{}, Tn.DoNothing{}, Tn.DoPing{}, Tn.DoTake{}]] : List<&2, List<&2, Tn.Do>>}

# Laws: the entry (R5)
# --------------------

# LAW tiny_run_entry_open (R5): an open Rust spells (its tag within the
# wire) starts the spec's run and answers what Rust does first
# EXCLUDES: a tag misread, an open read as the other kind, a reply
#   spelled otherwise
law tiny_run_entry_open:
  for +o: FTr.Open
  for h: {sp_fit_open(o) == True{} : Bool}
  {FTr.open(sp_w_open(o, "")) == sp_reply(sp_open(o)) : FTr.St & String}

# LAW tiny_run_entry_open_exact (R5): every open the entry does not
# refuse is a spelled open that fits the wire
# EXCLUDES: a run opened on input that is no open (an unknown tag, a
#   malformed tag text, input left over)
law tiny_run_entry_open_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(tr_snd(FTr.open(s))) == False{} : Bool}
  exs o: FTr.Open
  {s == sp_w_open(o, "") : String} & {sp_fit_open(o) == True{} : Bool}

# LAW tiny_run_entry_open_refuses (R5): every open the entry refuses opens
# the refused state with exactly `E tiny_run: malformed open`
# EXCLUDES: a default run for a malformed open, another error text
law tiny_run_entry_open_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(tr_snd(FTr.open(s))) == True{} : Bool}
  {FTr.open(s) == (FTr.Refused{}, Wr.err("tiny_run: malformed open")) : FTr.St & String}

# LAW tiny_run_entry_shut (R5): a refused open answers every step with
# exactly `E tiny_run: the open was refused`
# EXCLUDES: a refused stepper that launches or serves
law tiny_run_entry_shut:
  for +s: String
  {FTr.step(FTr.Refused{}, s) == (FTr.Refused{}, Wr.err("tiny_run: the open was refused")) : FTr.St & String}

# LAW tiny_run_entry_answers (R5, R7): in any state, every outcome Rust
# spells (its tag text within the wire) moves the run as the spec's
# table and answers the spelled reply
# EXCLUDES: a field misread, swapped or dropped; a state other than the
#   spec's; a reply in another spelling
law tiny_run_entry_answers:
  for +x: Tn.Run
  for +e: Tn.Seen
  for h: {sp_fit_seen(e) == True{} : Bool}
  {FTr.step(FTr.Live{x}, sp_w_seen(e, "")) == sp_reply(sp_step_r(x, e)) : FTr.St & String}

# LAW tiny_run_entry_exact (R5): in any state, every input the entry does
# not answer with the error form is a spelled outcome that fits the wire
# EXCLUDES: a step taken on input that is no outcome (an unknown tag, a
#   malformed field, input left over)
law tiny_run_entry_exact:
  for +x: Tn.Run
  for +s: String
  for ok: {LawsBase.wire_opens_err(tr_snd(FTr.step(FTr.Live{x}, s))) == False{} : Bool}
  exs e: Tn.Seen
  {s == sp_w_seen(e, "") : String} & {sp_fit_seen(e) == True{} : Bool}

# LAW tiny_run_entry_refuses (R5): in any state, every error the entry
# answers is exactly `E tiny_run: malformed event`, and the run stays
# EXCLUDES: a run changed by a malformed outcome, another error text
law tiny_run_entry_refuses:
  for +x: Tn.Run
  for +s: String
  for bad: {LawsBase.wire_opens_err(tr_snd(FTr.step(FTr.Live{x}, s))) == True{} : Bool}
  {FTr.step(FTr.Live{x}, s) == (FTr.Live{x}, Wr.err("tiny_run: malformed event")) : FTr.St & String}

# LAW tiny_run_entry_history (R5, R7): the shipped stepper, opened as
# Rust opens it and fed any outcomes Rust spells, answers each what the
# model's run decides after the outcomes before it: every run law above
# holds for the run Rust drives
# EXCLUDES: a stepper that forgets, reorders or replays an outcome, or
#   whose state drifts from the model's
law tiny_run_entry_history:
  for +o: FTr.Open
  for +ss: List<&2, Tn.Seen>
  for fo: {sp_fit_open(o) == True{} : Bool}
  for fs: {sp_all_fit(ss) == True{} : Bool}
  {tr_feed(ss, FTr.open(sp_w_open(o, ""))) == sp_w_dos(tr_replies(ss, sp_open(o))) : List<&2, String>}

# LAW tiny_run_entry_example (R5): anchor: the wire strings Rust sends and
# the replies it reads: a replacement, a seat, an unknown tag, input left
# over, a refused open
# EXCLUDES: tags in another order, a field order other than Rust's
law tiny_run_entry_example:
  {[tr_raw(["0,2,1,b", "1,0,", "2,0,", "0,2,1,a", "7,", "0,0,x"], FTr.open("0,1,a")), tr_raw(["4,", "0,0,"], FTr.open("1,")), tr_raw(["4,"], FTr.open("2,"))] == [["0,", "1,", "2,", "0,", "3,2,", Wr.err("tiny_run: malformed event"), Wr.err("tiny_run: malformed event")], ["5,", "0,", "7,"], [Wr.err("tiny_run: malformed open"), Wr.err("tiny_run: the open was refused")]] : List<&2, List<&2, String>>}

# LAW tiny_run_fits_example (R5): witness: opens and outcomes of each
# kind Rust sends fit the wire (the entry laws are not vacuous)
law tiny_run_fits_example:
  {[sp_fit_open(FTr.ONeed{"a"}), sp_fit_open(FTr.OSeat{}), sp_all_fit([Tn.Pinged{Tn.Pong{"ab"}}, Tn.ShutHeard{Tn.Bye{}}, Tn.Came{Tn.Adopted{}}, Tn.NoSpawn{}, Tn.Locked{}])] == [True{}, True{}, True{}] : List<&2, Bool>}
