# dash: the model of the dashboard's pairing gate (laws/dash.bend,
# "Pairing"). crates/eukhe-dashboard/src/pairing.rs,
# http.rs and bridge.rs implement it; its bridge test
# (pairing::tests::the_gate_pairs_as_its_model, with
# bridge/bridge_dash.bend) runs both on the same events.
#
# 1. Tokens. A token is named by the order in which it was made: the
#    first is 0, and each rotation makes the next one current. So the
#    tokens made so far are 0 .. cur, and cur is the current one.
# 2. Opening. A connection's first frame presents a token, or none. The
#    gate admits it only when it is the current token: the connection is
#    then open and holds that token. Otherwise the connection is rejected
#    (and closed).
# 3. Frames. A frame of an open connection runs (a daemon command) only
#    when the token the connection holds is the current one. Otherwise
#    the frame is refused and the connection closes. A frame of a closed
#    (or rejected) connection reaches nothing.
#
# Every event answers one outcome, which the bridge prints.

import Base

# 1. Connections and events
# -------------------------

# an open connection: its id and the token it presented
type Conn is Data:
  Conn{id: Nat, tok: Nat}

# the current token, and the open connections, newest first
type St is Data:
  St{cur: Nat, conns: List<&2, Conn>}

type Ev is Data:
  Rotate{}
  Open{c: Nat, shown: Maybe<&2, Nat>}
  Frame{c: Nat}

type Out is Data:
  Rotated{}
  Paired{c: Nat}
  Rejected{c: Nat}
  Ran{c: Nat}
  Refused{c: Nat}
  Closed{c: Nat}

# before any event: token 0 is current, and no connection is open
def init() -> St:
  St{0n, Nil{}}

def St.cur(s: St) -> Nat:
  match s:
    case St{cur, cs}:
      cur

def St.conns(s: St) -> List<&2, Conn>:
  match s:
    case St{cur, cs}:
      cs

# 2. The connection table
# -----------------------

def held.put(t: Nat, r: Maybe<&2, Nat>, hit: Bool) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{t}
    case False{}:
      r

# the token connection c holds, while it is open
def held(+c: Nat, cs: List<&2, Conn>) -> Maybe<&2, Nat>:
  match cs:
    case Nil{}:
      None{}
    case Conn{i, t} <> rest:
      held.put(t, held(c, rest), Nat.is_eq(i, c))

def drop.put(h: Conn, r: List<&2, Conn>, hit: Bool) -> List<&2, Conn>:
  match hit:
    case True{}:
      r
    case False{}:
      h <> r

# the table without connection c
def drop(+c: Nat, cs: List<&2, Conn>) -> List<&2, Conn>:
  match cs:
    case Nil{}:
      Nil{}
    case Conn{+i, t} <> rest:
      drop.put(Conn{i, t}, drop(c, rest), Nat.is_eq(i, c))

# 3. The gate
# -----------

# whether a presented token (or none) is the current one
def admit(+cur: Nat, shown: Maybe<&2, Nat>) -> Bool:
  match shown:
    case None{}:
      False{}
    case Some{t}:
      Nat.is_eq(t, cur)

def open.out(c: Nat, ok: Bool) -> Out:
  match ok:
    case True{}:
      Paired{c}
    case False{}:
      Rejected{c}

def frame.ran(c: Nat, ok: Bool) -> Out:
  match ok:
    case True{}:
      Ran{c}
    case False{}:
      Refused{c}

def frame.out(c: Nat, m: Maybe<&2, Nat>, +cur: Nat) -> Out:
  match m:
    case None{}:
      Closed{c}
    case Some{t}:
      frame.ran(c, Nat.is_eq(t, cur))

# what one event does
def out(+s: St, e: Ev) -> Out:
  match e:
    case Rotate{}:
      Rotated{}
    case Open{+c, shown}:
      open.out(c, admit(St.cur(s), shown))
    case Frame{+c}:
      frame.out(c, held(c, St.conns(s)), St.cur(s))

def open.keep(c: Nat, t: Nat, ok: Bool, cs: List<&2, Conn>) -> List<&2, Conn>:
  match ok:
    case True{}:
      Conn{c, t} <> cs
    case False{}:
      cs

# the table after an open of c; cs is already without c
def open.next(c: Nat, shown: Maybe<&2, Nat>, +cur: Nat, cs: List<&2, Conn>) -> List<&2, Conn>:
  match shown:
    case None{}:
      cs
    case Some{+t}:
      open.keep(c, t, Nat.is_eq(t, cur), cs)

# the table after a frame of c: a frame that does not run closes c
def frame.next(+c: Nat, ok: Bool, cs: List<&2, Conn>) -> List<&2, Conn>:
  match ok:
    case True{}:
      cs
    case False{}:
      drop(c, cs)

# the state after one event
def next(s: St, e: Ev) -> St:
  match s:
    case St{+cur, +cs}:
      match e:
        case Rotate{}:
          St{1n+cur, cs}
        case Open{+c, shown}:
          St{cur, open.next(c, shown, cur, drop(c, cs))}
        case Frame{+c}:
          St{cur, frame.next(c, admit(cur, held(c, cs)), cs)}

# 4. Runs
# -------

# the outcomes of the events, in order, from state s
def run(evs: List<&2, Ev>, +s: St) -> List<&2, Out>:
  match evs:
    case Nil{}:
      Nil{}
    case +e <> rest:
      out(s, e) <> run(rest, next(s, e))

# the state after the events, from state s
def state(evs: List<&2, Ev>, s: St) -> St:
  match evs:
    case Nil{}:
      s
    case +e <> rest:
      state(rest, next(s, e))

# 5. Questions about runs
# -----------------------

def is_paired(o: Out) -> Bool:
  match o:
    case Paired{c}:
      True{}
    case Rotated{}:
      False{}
    case Rejected{c}:
      False{}
    case Ran{c}:
      False{}
    case Refused{c}:
      False{}
    case Closed{c}:
      False{}

# whether the outcome ran a frame of connection c
def ran(+c: Nat, o: Out) -> Bool:
  match o:
    case Ran{x}:
      Nat.is_eq(x, c)
    case Rotated{}:
      False{}
    case Paired{x}:
      False{}
    case Rejected{x}:
      False{}
    case Refused{x}:
      False{}
    case Closed{x}:
      False{}

# whether any outcome ran a frame of connection c
def any_ran(+c: Nat, os: List<&2, Out>) -> Bool:
  match os:
    case Nil{}:
      False{}
    case o <> rest:
      Bool.or(ran(c, o), any_ran(c, rest))

# whether an event opens connection c
def opens(+c: Nat, e: Ev) -> Bool:
  match e:
    case Open{x, shown}:
      Nat.is_eq(x, c)
    case Rotate{}:
      False{}
    case Frame{x}:
      False{}

# whether any event opens connection c
def any_opens(+c: Nat, evs: List<&2, Ev>) -> Bool:
  match evs:
    case Nil{}:
      False{}
    case e <> rest:
      Bool.or(opens(c, e), any_opens(c, rest))
