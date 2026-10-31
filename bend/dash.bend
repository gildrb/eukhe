# dash: the dashboard's pairing gate (laws/dash.bend, laws/dash_conn.bend),
# run as the compiled core
# (bend/ffi_dash.bend). crates/eukhe-dashboard/src/pairing.rs, http.rs and
# bridge.rs are its host: an event loop that reads frames and the token
# file, compares two decoded tokens in constant time, and does what the
# core answers.
#
# 1. The host's choices: what a presented text and the token file hold,
#    whether a socket opens on its first frame, whether a later frame runs,
#    what `eukhe dashboard` does with the file at its start.
# 2. One socket: the stepper each socket runs, waiting for its pairing,
#    paired, or closed. Each frame comes with the token file as read at
#    that moment and with whether Rust found the socket's token equal to
#    the file's (`matches`: Rust's constant-time comparison, a primitive
#    like a hash); the stepper decides what that means, so a rotation by
#    any `eukhe dashboard` process ends every socket at its next frame.

import Base

# 1. The host's choices
# -----------------------
# What the server decides from what it met (crates/eukhe-dashboard
# pairing.rs, http.rs, bridge.rs). A token is 32 bytes, written as 64 hex
# digits (either case); the file holds it, trimmed of whitespace.
# `matches` says that Rust found the presented and the stored token both
# decoded and equal, in constant time.

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

def pass.matches(matches: Bool) -> Pass:
  match matches:
    case True{}:
      Admit{}
    case False{}:
      Refuse{wrong()}

# a presented token against the file: matches says that Rust found both
# tokens equal
def check(m: Maybe<&2, List<&2, Nat>>, matches: Bool) -> Pass:
  match m:
    case None{}:
      Refuse{unset()}
    case Some{bs}:
      pass.matches(matches)

def gate.shown(s: Shown, f: Disk, matches: Bool) -> Pass:
  match s:
    case Hex{bs}:
      check(stored(f), matches)
    case Blank{}:
      Refuse{missing()}
    case Junk{}:
      Refuse{wrong()}

# the first frame of a socket: open it or refuse it
def gate(x: First, f: Disk, matches: Bool) -> Pass:
  match x:
    case NoText{}:
      Refuse{missing()}
    case NotPairing{}:
      Refuse{missing()}
    case Pair{t}:
      gate.shown(shown(t), f, matches)

# a later frame of an open socket: run it, or refuse it and close
def frame(f: Disk, matches: Bool) -> Pass:
  check(stored(f), matches)

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

# 2. One socket
# -------------

# where a socket stands (Rust keeps the token it paired with)
type Conn is Data:
  Waiting{}  # no frame yet: it waits for its pairing
  Paired{}   # it paired: its frames may run
  Closed{}   # refused: nothing more runs

# what a socket met, with the token file as read at that moment and
# whether Rust found the socket's token (the one this frame presents, or
# the one it paired with) equal to the file's
type CEv is Data:
  CFirst{first: First, file: Disk, matches: Bool}  # its first frame (or none in time)
  CFrame{file: Disk, matches: Bool}                # a later text frame (a daemon command)

# what the host does
type Verdict is Data:
  VPaired{}             # the socket opens: greet the tab
  VRun{}                # the frame runs
  VRefuse{text: String} # tell the tab the text, and close the socket
  VClosed{}             # the socket is closed: nothing runs

def first.pass(p: Pass) -> Conn & Verdict:
  match p:
    case Admit{}:
      (Paired{}, VPaired{})
    case Refuse{t}:
      (Closed{}, VRefuse{t})

def frame.pass(p: Pass) -> Conn & Verdict:
  match p:
    case Admit{}:
      (Paired{}, VRun{})
    case Refuse{t}:
      (Closed{}, VRefuse{t})

# one event: where the socket stands after it, and what the host does
def cstep(c: Conn, e: CEv) -> Conn & Verdict:
  match c:
    case Waiting{}:
      match e:
        case CFirst{x, f, m}:
          first.pass(gate(x, f, m))
        case CFrame{f, m}:
          (Closed{}, VRefuse{missing()})
    case Paired{}:
      match e:
        case CFirst{x, f, m}:
          (Closed{}, VRefuse{missing()})
        case CFrame{f, m}:
          frame.pass(frame(f, m))
    case Closed{}:
      (Closed{}, VClosed{})
