# run: the recoveries of a stuck reply (H4.8): rows of repeated calls, RCfg, Rk, Out, Rec, Act, Dec and their step and caps

import Base
import ./state.bend as RnState
import ../stop.bend as Stop

# rounds in a row with hash h after a round: one more when the last
# round had it, else 1 (the recoveries count their rows with it)
def again.eq(eq: Bool, k: Nat) -> Nat:
  match eq:
    case True{}:
      2n+k
    case False{}:
      1n

def again(same: Nat, +last: Nat, +h: Nat) -> Nat:
  match same:
    case 0n:
      1n
    case 1n+k:
      again.eq(Nat.is_eq(last, h), k)

# Recoveries
# ----------
# LAWS.bend H4.8. The replies a weaker model gives when it is stuck get
# a recovery, each with a cap: a length stop (its text, if any, cut),
# tool calls that it wrote as text (markup in the answer), the same tool
# calls (names and arguments) round after round, and, from the Directors
# at a candidate stop (bend/stop.bend), a reply with no text and an
# answer that announces a next step it did not take. A recovery turns the
# reply into one that the steps above already read (Act.reply): a noted
# error, whose retry ends its request with a note of the recovery (H4.7),
# calls that run, or an answer. Thus every law above holds for a run with
# the recoveries too: those laws hold for every reply. The Rust side is
# decide.rs `recover`.

# long: LENGTH_NOTES (3), leak: LEAK_NOTES (2), redirect:
# REDIRECT_NOTES (2), repeat: REPEAT_CALLS (5)
type RCfg is Data:
  RCfg{long: Nat, leak: Nat, redirect: Nat, repeat: Nat}

def RCfg.long(c: RCfg) -> Nat:
  match c:
    case RCfg{long, leak, redirect, repeat}:
      long

def RCfg.leak(c: RCfg) -> Nat:
  match c:
    case RCfg{long, leak, redirect, repeat}:
      leak

def RCfg.redirect(c: RCfg) -> Nat:
  match c:
    case RCfg{long, leak, redirect, repeat}:
      redirect

def RCfg.repeat(c: RCfg) -> Nat:
  match c:
    case RCfg{long, leak, redirect, repeat}:
      repeat

# a < b
def below(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      False{}
    case 0n 1n+q:
      True{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      below(p, q)

# the recovery that the note of the next request counts: none (no note,
# or the note after a stream cut as repeating), a length stop, a leaked
# call, a repeated call, a reply with no text, an announced step not taken
type Rk is Data:
  Free{}
  Longs{}
  Leaks{}
  Loops{}
  Empties{}
  Promises{}

# what a reply holds, as the recoveries read it. Long: a length stop with
# no tool call (text or not; the stop walk's LengthStop). Leak: tool-call
# markup in its text and no tool call; rebuilt: every leaked call parsed
# and names a tool that the request offered, so the calls are rebuilt, as
# Ran (not rebuilt: the stop walk's MarkupStop). Ran: tool calls (any stop
# reason), h the hash of their names and arguments; kept: when they run,
# their results are the results of the last round (a result that changes
# is progress, as a job that a call polls, so it is no repeat). Noted:
# another noted reply (a stream cut as repeating). Said: a user message
# joins the context (a steer, the user's next turn): the user changed the
# context, so no call repeats across it. Answer: an answer with no tool
# call. Other: any other reply (an error that is not noted, deferred, an
# overflow). Empty: no text and no tool call (the stop walk's EmptyStop).
# Promise: an answer whose end announces a next step it did not take,
# asking the user nothing, with no work running (the stop walk's
# UnexpectedStop)
type Out is Data:
  Long{}
  Leak{rebuilt: Bool, h: Nat, kept: Bool}
  Ran{h: Nat, kept: Bool}
  Noted{}
  Said{}
  Answer{}
  Other{}
  Empty{}
  Promise{}

# k and row: the recovery that the note of the next request counts and
# the notes of it in a row; same: the rounds in a row that the run ran
# with the calls of hash last and the same results (0: none)
type Rec is Data:
  Rec{k: Rk, row: Nat, same: Nat, last: Nat}

# the rounds in a row after a round that would make m: m when its
# results are those of the last round, else it starts a new row
def ran.same(kept: Bool, m: Nat) -> Nat:
  match kept:
    case True{}:
      m
    case False{}:
      1n

def Rec.same(r: Rec) -> Nat:
  match r:
    case Rec{k, row, same, last}:
      same

# what a recovery does with a reply. Pass: no recovery; the reply goes on
# as it is. Exec: its calls run. Redo: a noted error, so a retry whose
# note names the recovery. Stand: the reply answers as text. Quit: the
# cap is reached; the run fails on the model. Remind: the reply stays in
# the transcript, and the run asks again with a note that names the
# recovery: a noted retry for the steps above
type Act is Data:
  Pass{}
  Exec{}
  Redo{}
  Stand{}
  Quit{}
  Remind{}

# the reply that the steps above read; pass: the reply as Ended.reply
# made it
def Act.reply(a: Act, pass: RnState.Reply) -> RnState.Reply:
  match a:
    case Pass{}:
      pass
    case Exec{}:
      RnState.Calls{}
    case Redo{}:
      RnState.Error{False{}, True{}}
    case Stand{}:
      RnState.Plain{}
    case Quit{}:
      RnState.Error{False{}, False{}}
    case Remind{}:
      RnState.Error{False{}, True{}}

# an act and the recoveries after it
type Dec is Data:
  Dec{act: Act, r: Rec}

def Dec.act(d: Dec) -> Act:
  match d:
    case Dec{act, r}:
      act

def Dec.r(d: Dec) -> Rec:
  match d:
    case Dec{act, r}:
      r

# the notes of each recovery in a row that the next request's note makes:
# its row when it counts that recovery, else 0
def Rk.longs(k: Rk, row: Nat) -> Nat:
  match k:
    case Free{}:
      0n
    case Longs{}:
      row
    case Leaks{}:
      0n
    case Loops{}:
      0n
    case Empties{}:
      0n
    case Promises{}:
      0n

def Rk.leaks(k: Rk, row: Nat) -> Nat:
  match k:
    case Free{}:
      0n
    case Longs{}:
      0n
    case Leaks{}:
      row
    case Loops{}:
      0n
    case Empties{}:
      0n
    case Promises{}:
      0n

def Rk.loops(k: Rk, row: Nat) -> Nat:
  match k:
    case Free{}:
      0n
    case Longs{}:
      0n
    case Leaks{}:
      0n
    case Loops{}:
      row
    case Empties{}:
      0n
    case Promises{}:
      0n

def Rk.empties(k: Rk, row: Nat) -> Nat:
  match k:
    case Free{}:
      0n
    case Longs{}:
      0n
    case Leaks{}:
      0n
    case Loops{}:
      0n
    case Empties{}:
      row
    case Promises{}:
      0n

def Rk.promises(k: Rk, row: Nat) -> Nat:
  match k:
    case Free{}:
      0n
    case Longs{}:
      0n
    case Leaks{}:
      0n
    case Loops{}:
      0n
    case Empties{}:
      0n
    case Promises{}:
      row

# a length stop: under the cap (n notes in a row) a retry with the next
# length note; at the cap the run fails
def rec.long(under: Bool, +n: Nat, +same: Nat, +last: Nat, r: Rec) -> Dec:
  match under:
    case True{}:
      Dec{Redo{}, Rec{Longs{}, 1n+n, same, last}}
    case False{}:
      Dec{Quit{}, r}

# leaked calls that were not rebuilt: under the cap a retry with the next
# leak note; at the cap the run fails: markup is never an answer
def rec.leak(under: Bool, +n: Nat, +same: Nat, +last: Nat, r: Rec) -> Dec:
  match under:
    case True{}:
      Dec{Redo{}, Rec{Leaks{}, 1n+n, same, last}}
    case False{}:
      Dec{Quit{}, r}

# no text and no tool call: under the cap (Stop.empty_cap) a retry with
# the next empty note; at the cap the run fails
def rec.empty(under: Bool, +n: Nat, +same: Nat, +last: Nat, r: Rec) -> Dec:
  match under:
    case True{}:
      Dec{Redo{}, Rec{Empties{}, 1n+n, same, last}}
    case False{}:
      Dec{Quit{}, r}

# an announced step not taken: under the cap (Stop.promise_cap) the
# answer stays and the run asks again with the next stop note; at the cap
# the answer stands
def rec.promise(under: Bool, +n: Nat, +same: Nat, +last: Nat, r: Rec) -> Dec:
  match under:
    case True{}:
      Dec{Remind{}, Rec{Promises{}, 1n+n, same, last}}
    case False{}:
      Dec{Stand{}, r}

# tool calls that would make m rounds in a row: below the repeat cap they
# run (kept: their results are the last round's), and the next generation
# starts with no note; else they do not run: under the cap a retry with
# the next redirect note, at it the run fails
def rec.ran(fresh: Bool, under: Bool, kept: Bool, +m: Nat, +h: Nat, +n: Nat, +same: Nat, +last: Nat, r: Rec) -> Dec:
  match fresh under:
    case True{} under:
      Dec{Exec{}, Rec{Free{}, 0n, ran.same(kept, m), h}}
    case False{} True{}:
      Dec{Redo{}, Rec{Loops{}, 1n+n, same, last}}
    case False{} False{}:
      Dec{Quit{}, r}

def rec.go(+rc: RCfg, o: Out, +k: Rk, +row: Nat, +same: Nat, +last: Nat) -> Dec:
  match o:
    case Long{}:
      rec.long(below(Rk.longs(k, row), RCfg.long(rc)), Rk.longs(k, row), same, last, Rec{k, row, same, last})
    case Leak{rebuilt, +h, kept}:
      match rebuilt:
        case True{}:
          rec.ran(below(again(same, last, h), RCfg.repeat(rc)), below(Rk.loops(k, row), RCfg.redirect(rc)), kept, again(same, last, h), h, Rk.loops(k, row), same, last, Rec{k, row, same, last})
        case False{}:
          rec.leak(below(Rk.leaks(k, row), RCfg.leak(rc)), Rk.leaks(k, row), same, last, Rec{k, row, same, last})
    case Ran{+h, kept}:
      rec.ran(below(again(same, last, h), RCfg.repeat(rc)), below(Rk.loops(k, row), RCfg.redirect(rc)), kept, again(same, last, h), h, Rk.loops(k, row), same, last, Rec{k, row, same, last})
    case Noted{}:
      Dec{Pass{}, Rec{Free{}, 0n, same, last}}
    case Said{}:
      Dec{Pass{}, Rec{k, row, 0n, last}}
    case Answer{}:
      Dec{Pass{}, Rec{Free{}, 0n, 0n, last}}
    case Other{}:
      Dec{Pass{}, Rec{k, row, same, last}}
    case Empty{}:
      rec.empty(below(Rk.empties(k, row), Stop.empty_cap()), Rk.empties(k, row), same, last, Rec{k, row, same, last})
    case Promise{}:
      rec.promise(below(Rk.promises(k, row), Stop.promise_cap()), Rk.promises(k, row), same, last, Rec{k, row, same, last})

# the recovery of one reply (decide.rs `recover`; a Noted, Said, Answer
# or Other reply is `retry_note` and the context alone)
def Rec.step(+rc: RCfg, o: Out, r: Rec) -> Dec:
  match r:
    case Rec{k, row, same, last}:
      rec.go(rc, o, k, row, same, last)

# a run starts with no note and no round
def Rec.init() -> Rec:
  Rec{Free{}, 0n, 0n, 0n}

def Rec.go(os: List<&2, Out>, +rc: RCfg, r: Rec) -> Rec:
  match os:
    case Nil{}:
      r
    case o <> rest:
      Rec.go(rest, rc, Dec.r(Rec.step(rc, o, r)))

# the recoveries after the replies os
def Rec.run(+rc: RCfg, os: List<&2, Out>) -> Rec:
  Rec.go(os, rc, Rec.init())

# the row of the next note is at most the cap of its recovery
def Rk.capped(+rc: RCfg, k: Rk, row: Nat) -> Bool:
  match k:
    case Free{}:
      True{}
    case Longs{}:
      below(row, 1n+RCfg.long(rc))
    case Leaks{}:
      below(row, 1n+RCfg.leak(rc))
    case Loops{}:
      below(row, 1n+RCfg.redirect(rc))
    case Empties{}:
      below(row, 1n+Stop.empty_cap())
    case Promises{}:
      below(row, 1n+Stop.promise_cap())

def Rec.capped(+rc: RCfg, r: Rec) -> Bool:
  match r:
    case Rec{k, row, same, last}:
      Rk.capped(rc, k, row)

# the act runs tool calls
def Act.runs(a: Act) -> Bool:
  match a:
    case Pass{}:
      False{}
    case Exec{}:
      True{}
    case Redo{}:
      False{}
    case Stand{}:
      False{}
    case Quit{}:
      False{}
    case Remind{}:
      False{}

# the reply is stuck: a length stop, leaked tool calls, tool calls (which
# may repeat), no text, an announced step not taken
def Out.stuck(o: Out) -> Bool:
  match o:
    case Long{}:
      True{}
    case Leak{rebuilt, h, kept}:
      True{}
    case Ran{h, kept}:
      True{}
    case Noted{}:
      False{}
    case Said{}:
      False{}
    case Answer{}:
      False{}
    case Other{}:
      False{}
    case Empty{}:
      True{}
    case Promise{}:
      True{}

# the act does something about the reply: it runs calls that are no
# repeat, retries with a note (a new request, H4.7), answers, or ends the
# run; only Pass leaves the reply as it is
def Act.helps(a: Act) -> Bool:
  match a:
    case Pass{}:
      False{}
    case Exec{}:
      True{}
    case Redo{}:
      True{}
    case Stand{}:
      True{}
    case Quit{}:
      True{}
    case Remind{}:
      True{}
