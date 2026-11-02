# worker: the two pure decisions of the "main + worker" session shape. It
# runs as the compiled Bend core (entry bend/ffi_worker.bend, a plain call:
# Rust keeps the pause state in a durable doc and sends it with each event).
#
# 1. The pause of the worker tree. The run asks before each boundary (a
#    model request, a tool call, a child spawn): while paused it holds there
#    (the boundary is parked) until a Resume or a waking message. A pause
#    cancels nothing: a tool call that started runs to its end. Messages that
#    arrive while paused and do not wake the tree are kept, and released in
#    arrival order when it runs again.
# 2. The forward pick: main hands the worker the user's words, verbatim: the
#    messages past the cursor, their texts joined by a blank line, then main's
#    note.

import Base

# Pause
# -----

type Mode is Data:
  Run{}
  Paused{}

# the mode; the id of the boundary held while paused (None: none); the ids
# of the messages kept while paused, in arrival order; the tool calls that
# started and did not end
type St is Data:
  St{mode: Mode, parked: Maybe<&2, Nat>, kept: List<&2, Nat>, inflight: Nat}

# Gate kind: 0 a model request, 1 a tool call, 2 a child spawn; id names the
# boundary. ToolDone: a tool call that started ended. Msg: a message reached
# the session; wakes: a user message or a forward from main (it wakes a
# paused tree), else a report or a note (it waits). End: the run ended.
type Ev is Data:
  Pause{}
  Resume{}
  Gate{kind: Nat, id: Nat}
  ToolDone{}
  Msg{id: Nat, wakes: Bool}
  End{}

# Go: start the boundary. Hold: wait at it. Release: these kept messages go
# to the run now, in order. Kept: the message waits. Pass: the message goes
# as it would without the pause. Ack: noted.
type Verdict is Data:
  Go{}
  Hold{}
  Release{ids: List<&2, Nat>}
  Kept{}
  Pass{}
  Ack{}

# one more tool call in flight when the boundary is a tool call (kind 1)
def started(kind: Nat, n: Nat) -> Nat:
  match kind:
    case 0n:
      n
    case 1n:
      1n+n
    case 2n+k:
      n

# one tool call fewer in flight, never below none
def settled(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# k, then the id x
def snoc(k: List<&2, Nat>, x: Nat) -> List<&2, Nat>:
  List.append(&2, Nat, k, [x])

def resume(m: Mode, p: Maybe<&2, Nat>, k: List<&2, Nat>, n: Nat) -> St & Verdict:
  match m:
    case Run{}:
      (St{Run{}, p, k, n}, Release{Nil{}})
    case Paused{}:
      (St{Run{}, p, Nil{}, n}, Release{k})

def gate(m: Mode, p: Maybe<&2, Nat>, k: List<&2, Nat>, n: Nat, kind: Nat, id: Nat) -> St & Verdict:
  match m:
    case Run{}:
      (St{Run{}, None{}, k, started(kind, n)}, Go{})
    case Paused{}:
      (St{Paused{}, Some{id}, k, n}, Hold{})

def msg.paused(p: Maybe<&2, Nat>, k: List<&2, Nat>, n: Nat, id: Nat, wakes: Bool) -> St & Verdict:
  match wakes:
    case True{}:
      (St{Run{}, p, Nil{}, n}, Release{snoc(k, id)})
    case False{}:
      (St{Paused{}, p, snoc(k, id), n}, Kept{})

def msg(m: Mode, p: Maybe<&2, Nat>, k: List<&2, Nat>, n: Nat, id: Nat, wakes: Bool) -> St & Verdict:
  match m:
    case Run{}:
      (St{Run{}, p, k, n}, Pass{})
    case Paused{}:
      msg.paused(p, k, n, id, wakes)

def step.on(m: Mode, p: Maybe<&2, Nat>, k: List<&2, Nat>, n: Nat, e: Ev) -> St & Verdict:
  match e:
    case Pause{}:
      (St{Paused{}, p, k, n}, Ack{})
    case Resume{}:
      resume(m, p, k, n)
    case Gate{kind, id}:
      gate(m, p, k, n, kind, id)
    case ToolDone{}:
      (St{m, p, k, settled(n)}, Ack{})
    case Msg{id, wakes}:
      msg(m, p, k, n, id, wakes)
    case End{}:
      (St{m, None{}, k, 0n}, Ack{})

# the state after event e, and the answer to it
def step(s: St, e: Ev) -> St & Verdict:
  match s:
    case St{m, p, k, n}:
      step.on(m, p, k, n, e)

# Forward
# -------

# one of main's user messages, in transcript order
type UMsg is Data:
  UMsg{seq: Nat, text: String}

# the new cursor, the seqs handed on, and the text handed on
type Pick is Data:
  Pick{cursor: Nat, picked: List<&2, Nat>, body: String}

# what goes between two texts
def gap() -> String:
  "\n\n"

# what opens main's note
def note_head() -> String:
  "[note from main] "

def after.put(keep: Bool, m: UMsg, r: List<&2, UMsg>) -> List<&2, UMsg>:
  match keep:
    case True{}:
      m <> r
    case False{}:
      r

# the messages past the cursor c, in list order
def after(+c: Nat, ms: List<&2, UMsg>) -> List<&2, UMsg>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{UMsg{+q, t}, r}:
      after.put(Nat.is_lt(c, q), UMsg{q, t}, after(c, r))

def seqs(ms: List<&2, UMsg>) -> List<&2, Nat>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{UMsg{q, t}, r}:
      q <> seqs(r)

def higher(lt: Bool, a: Nat, b: Nat) -> Nat:
  match lt:
    case True{}:
      b
    case False{}:
      a

# the largest of c and the seqs of ms
def top(ms: List<&2, UMsg>, +c: Nat) -> Nat:
  match ms:
    case Nil{}:
      c
    case Con{UMsg{+q, t}, r}:
      top(r, higher(Nat.is_lt(c, q), c, q))

# the note after a text
def note.after(note: Maybe<&2, String>) -> String:
  match note:
    case None{}:
      ""
    case Some{n}:
      String.append(gap(), String.append(note_head(), n))

# the note alone
def note.alone(note: Maybe<&2, String>) -> String:
  match note:
    case None{}:
      ""
    case Some{n}:
      String.append(note_head(), n)

# the texts of ms after a first one, each after a gap, then the note
def body.more(ms: List<&2, UMsg>, note: Maybe<&2, String>) -> String:
  match ms:
    case Nil{}:
      note.after(note)
    case Con{UMsg{q, t}, r}:
      String.append(gap(), String.append(t, body.more(r, note)))

# the texts of ms joined by gaps, then the note
def body(ms: List<&2, UMsg>, note: Maybe<&2, String>) -> String:
  match ms:
    case Nil{}:
      note.alone(note)
    case Con{UMsg{q, t}, r}:
      String.append(t, body.more(r, note))

# main's user messages ms past the cursor c, handed on with main's note
def pick(+c: Nat, ms: List<&2, UMsg>, note: Maybe<&2, String>) -> Pick:
  +sel = after(c, ms)
  Pick{top(sel, c), seqs(sel), body(sel, note)}
