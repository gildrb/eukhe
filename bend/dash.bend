# dash: the model of the dashboard's pairing gate (laws/dash.bend,
# docs/dashboard.md "Pairing"). crates/eukhe-dashboard/src/pairing.rs,
# http.rs and bridge.rs implement it: every choice of section 6 runs as
# the compiled core (bend/ffi_dash.bend); the bridge test
# (pairing::tests::the_gate_pairs_as_its_model, with
# bridge/bridge_dash.bend) runs the real server and the run model of
# sections 1-5 on the same events (rotations by another process between
# the frames of open sockets: the interleaving).
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

# 6. The host's choices
# ---------------------
# What the server decides from what it met (crates/eukhe-dashboard
# pairing.rs, http.rs, bridge.rs). A token is 32 bytes, written as 64 hex
# digits (either case); the file holds it, trimmed of whitespace. Rust
# reads frames and the file and compares two decoded tokens in constant
# time (`same`: both decode and are equal); every choice is here.

# what reading the token file met
type Disk is Data:
  NoFile{}         # the file does not exist
  Unread{}         # it could not be read (or is not UTF-8)
  Holds{s: String}  # its text
  Huge{}           # its text is longer than the wire carries

# a text a tab presented
type Said is Data:
  Spoken{s: String}  # this text
  Overlong{}         # a text longer than the wire carries

# the first frame of a socket
type First is Data:
  NoText{}           # a binary frame, none in time, or the tab left
  NotPairing{}       # a text frame that is not a pairing
  Pair{token: Said}  # a pairing that presents this text

# what a presented text is
type Shown is Data:
  Hex{bytes: List<&2, Nat>}  # a token: its 32 bytes
  Blank{}                    # empty: no token presented
  Junk{}                     # not a token

# the gate's answer: pass, or refuse with the text the tab shows
type Pass is Data:
  Admit{}
  Refuse{text: String}

# what `eukhe dashboard` does with the stored token at its start
type Rotation is Data:
  KeepToken{}
  RotateToken{}

type Keep is Data:
  Mint{}        # store a new token
  Reuse{}       # use the stored token
  Restrict{}    # use it, and narrow the file's mode to 0600
  Unreadable{}  # fail: the file cannot be read
  Tokenless{}   # fail: the file holds no token (rotate to replace it)

def find.hit(b: Bool, n: Nat, r: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{n}
    case False{}:
      r

# the place of c in ds, counted from n
def find(+c: Char, ds: String, +n: Nat) -> Maybe<&2, Nat>:
  match ds:
    case SNil{}:
      None{}
    case SCon{d, rest}:
      find.hit(Char.is_eq(c, d), n, find(c, rest, 1n+n))

def digit.upper(+c: Char, m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      find(c, "ABCDEF", 10n)
    case Some{v}:
      Some{v}

# the value of a hex digit (either case)
def digit(+c: Char) -> Maybe<&2, Nat>:
  digit.upper(c, find(c, "0123456789abcdef", 0n))

def byte(x: Maybe<&2, Nat>, y: Maybe<&2, Nat>, r: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  match x:
    case None{}:
      None{}
    case Some{h}:
      match y:
        case None{}:
          None{}
        case Some{l}:
          match r:
            case None{}:
              None{}
            case Some{bs}:
              Some{Nat.add(Nat.mul(h, 16n), l) <> bs}

# the k bytes that s spells in exactly 2k hex digits
def bytes(k: Nat, s: String) -> Maybe<&2, List<&2, Nat>>:
  match k:
    case 0n:
      match s:
        case SNil{}:
          Some{Nil{}}
        case SCon{c, t}:
          None{}
    case 1n+j:
      match s:
        case SNil{}:
          None{}
        case SCon{a, t}:
          match t:
            case SNil{}:
              None{}
            case SCon{b, u}:
              byte(digit(a), digit(b), bytes(j, u))

# the token a text spells: exactly 64 hex digits
def parse(s: String) -> Maybe<&2, List<&2, Nat>>:
  bytes(32n, s)

def shown.of(m: Maybe<&2, List<&2, Nat>>, e: Bool) -> Shown:
  match m:
    case Some{bs}:
      Hex{bs}
    case None{}:
      match e:
        case True{}:
          Blank{}
        case False{}:
          Junk{}

# what a presented text is
def shown(x: Said) -> Shown:
  match x:
    case Spoken{+s}:
      shown.of(parse(s), String.is_empty(s))
    case Overlong{}:
      Junk{}

# Rust's whitespace (`char::is_whitespace`: the White_Space property), by
# code point
def spaces() -> List<&2, U32>:
  [9, 10, 11, 12, 13, 32, 133, 160, 5760, 8192, 8193, 8194, 8195, 8196, 8197, 8198, 8199, 8200, 8201, 8202, 8232, 8233, 8239, 8287, 12288]

def space.in(+x: U32, xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(U32.is_eq(x, y), space.in(x, rest))

def space(c: Char) -> Bool:
  space.in(Char.to_u32(c), spaces())

def trim_start.if(b: Bool, c: Char, t: String, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, t}

# s without its leading whitespace (r: the rest without its own)
def trim_start(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      trim_start.if(space(c), c, t, trim_start(t))

# s without its leading and trailing whitespace
def trim(s: String) -> String:
  String.reverse(trim_start(String.reverse(trim_start(s))))

# the token the file holds, if any
def stored(f: Disk) -> Maybe<&2, List<&2, Nat>>:
  match f:
    case NoFile{}:
      None{}
    case Unread{}:
      None{}
    case Holds{s}:
      parse(trim(s))
    case Huge{}:
      None{}

def missing() -> String:
  "pairing needed: open the link that `eukhe dashboard` prints"

def wrong() -> String:
  "this pairing link is not valid any more: open the link that `eukhe dashboard` prints"

def unset() -> String:
  "the dashboard has no pairing token: restart `eukhe dashboard`"

def pass.same(same: Bool) -> Pass:
  match same:
    case True{}:
      Admit{}
    case False{}:
      Refuse{wrong()}

# a presented token against the file: same says that Rust found both
# tokens equal
def check(m: Maybe<&2, List<&2, Nat>>, same: Bool) -> Pass:
  match m:
    case None{}:
      Refuse{unset()}
    case Some{bs}:
      pass.same(same)

def gate.shown(s: Shown, f: Disk, same: Bool) -> Pass:
  match s:
    case Hex{bs}:
      check(stored(f), same)
    case Blank{}:
      Refuse{missing()}
    case Junk{}:
      Refuse{wrong()}

# the first frame of a socket: open it or refuse it
def gate(x: First, f: Disk, same: Bool) -> Pass:
  match x:
    case NoText{}:
      Refuse{missing()}
    case NotPairing{}:
      Refuse{missing()}
    case Pair{t}:
      gate.shown(shown(t), f, same)

# a later frame of an open socket: run it, or refuse it and close
def frame(f: Disk, same: Bool) -> Pass:
  check(stored(f), same)

# a 0600 file: no bit for the group or others
def keep.private(b: Bool) -> Keep:
  match b:
    case True{}:
      Reuse{}
    case False{}:
      Restrict{}

def keep.mode(mode: Nat) -> Keep:
  keep.private(Nat.is_eq(Nat.mod(mode, 64n), 0n))

def keep.held(m: Maybe<&2, List<&2, Nat>>, mode: Nat) -> Keep:
  match m:
    case None{}:
      Tokenless{}
    case Some{bs}:
      keep.mode(mode)

# what `eukhe dashboard` does with the token file at its start
def keep(r: Rotation, f: Disk, mode: Nat) -> Keep:
  match r:
    case RotateToken{}:
      Mint{}
    case KeepToken{}:
      match f:
        case NoFile{}:
          Mint{}
        case Unread{}:
          Unreadable{}
        case Holds{s}:
          keep.held(parse(trim(s)), mode)
        case Huge{}:
          Tokenless{}
