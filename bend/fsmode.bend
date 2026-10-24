# fsmode: who reaches eukhe's own state (docs/runtime.md "Local access").
# Four small decisions, each as one function, run as this code (entry
# bend/ffi_fsmode.bend):
#
# - socket_dir: the check of the dir that holds the daemon sockets
#   (crates/eukhe-daemon/src/platform/paths.rs `prepare_socket_dir`).
# - peer: the peer rule of every socket listener
#   (crates/eukhe-types/src/platform/transport.rs, the rule it is given).
# - made: the mode of each file and dir eukhe creates under its home
#   (eukhe_types::platform::access PRIVATE_FILE_MODE / PRIVATE_DIR_MODE,
#   used by the daemon's `ensure_dir`, the socket dir, the auth store and
#   the private storage env of eukhe-durable).
# - open: the working dir of a session create
#   (crates/eukhe-daemon/src/session_cwd.rs `session_cwd`).
#
# A mode is its three octal digits (user, group, other). Paths and uids
# are numbers.

import Base

# Modes
# -----

type Mode is Data:
  Mode{user: Nat, group: Nat, other: Nat}

# 0700
def dir_mode() -> Mode:
  Mode{7n, 0n, 0n}

# 0600
def file_mode() -> Mode:
  Mode{6n, 0n, 0n}

# a digit with any bit set
def digit.set(d: Nat) -> Bool:
  match d:
    case 0n:
      False{}
    case 1n+p:
      True{}

# the mode has a group or other bit
def Mode.loose(m: Mode) -> Bool:
  match m:
    case Mode{u, g, o}:
      Bool.or(digit.set(g), digit.set(o))

# The socket dir
# --------------

# what symlink_metadata finds at the path
type Node is Data:
  Missing{}
  Dir{}
  Link{}
  Other{}

# the node, whether this uid owns it, whether a group or other user may
# write in it (the read and search bits are harmless: the socket is 0600
# and the peer rule drops other uids)
type Seen is Data:
  Seen{node: Node, mine: Bool, loose: Bool}

type Verdict is Data:
  Create{mode: Mode}
  Use{}
  Refuse{}

def Node.is_dir(k: Node) -> Bool:
  match k:
    case Missing{}:
      False{}
    case Dir{}:
      True{}
    case Link{}:
      False{}
    case Other{}:
      False{}

# a dir the daemon may bind in: a real dir, this uid's, that no group or
# other user may write in
def Seen.safe(d: Seen) -> Bool:
  match d:
    case Seen{k, mine, loose}:
      Bool.and(Node.is_dir(k), Bool.and(mine, Bool.not(loose)))

def socket_dir.dir(mine: Bool, loose: Bool) -> Verdict:
  match mine loose:
    case True{} False{}:
      Use{}
    case True{} True{}:
      Refuse{}
    case False{} _:
      Refuse{}

def socket_dir(d: Seen) -> Verdict:
  match d:
    case Seen{k, mine, loose}:
      match k:
        case Missing{}:
          Create{dir_mode()}
        case Dir{}:
          socket_dir.dir(mine, loose)
        case Link{}:
          Refuse{}
        case Other{}:
          Refuse{}

# what the daemon finds after it creates a dir with mode m
def made(m: Mode) -> Seen:
  Seen{Dir{}, True{}, Mode.loose(m)}

# Socket peers
# ------------

type Peer is Data:
  Accept{}
  Drop{}

def peer.at(same: Bool) -> Peer:
  match same:
    case True{}:
      Accept{}
    case False{}:
      Drop{}

def peer(+p: Nat, +own: Nat) -> Peer:
  peer.at(Nat.is_eq(p, own))

# What eukhe creates
# ------------------

type Made is Data:
  DirMade{}
  FileMade{}

def made_mode(k: Made) -> Mode:
  match k:
    case DirMade{}:
      dir_mode()
    case FileMade{}:
      file_mode()

# The working dir of a session
# ----------------------------

# what the create names: no dir, a path where nothing is, a path to a
# file, a path to a dir
type Cwd is Data:
  NoCwd{}
  GoneCwd{p: Nat}
  FileCwd{p: Nat}
  DirCwd{p: Nat}

type Open is Data:
  Opened{p: Nat}
  NeedsCwd{}
  Gone{p: Nat}
  NotDir{p: Nat}

def open(c: Cwd) -> Open:
  match c:
    case NoCwd{}:
      NeedsCwd{}
    case GoneCwd{p}:
      Gone{p}
    case FileCwd{p}:
      NotDir{p}
    case DirCwd{p}:
      Opened{p}

# What Rust reads
# ---------------

# the bit of weight w (a power of two) is set in the permission bits m
def bit(+m: Nat, w: Nat) -> Bool:
  Nat.is_eq(Nat.mod(Nat.div(m, w), 2n), 1n)

# the socket dir as Rust finds it: what symlink_metadata found, the uid
# that owns it, this process's uid and its permission bits (mode & 0o7777;
# for a missing dir the numbers are 0): a group or other user may write in
# it when the group-write (0o020) or other-write (0o002) bit is set
def look(k: Node, +uid: Nat, +own: Nat, +m: Nat) -> Seen:
  Seen{k, Nat.is_eq(uid, own), Bool.or(bit(m, 16n), bit(m, 2n))}

# why the check refuses a socket dir
type Why is Data:
  WhyLink{}
  WhyNotDir{}
  WhyOwner{}
  WhyMode{}

def why.dir(mine: Bool) -> Why:
  match mine:
    case True{}:
      WhyMode{}
    case False{}:
      WhyOwner{}

# the reason of a refused dir (the first check it fails: a link, not a
# dir, another owner, a loose mode)
def why(d: Seen) -> Why:
  match d:
    case Seen{k, mine, loose}:
      match k:
        case Missing{}:
          WhyNotDir{}
        case Dir{}:
          why.dir(mine)
        case Link{}:
          WhyLink{}
        case Other{}:
          WhyNotDir{}

# what metadata finds at a named working dir
type Stat is Data:
  Absent{}
  AFile{}
  ADir{}

def cwd.named(empty: Bool, s: Stat) -> Cwd:
  match empty:
    case True{}:
      NoCwd{}
    case False{}:
      match s:
        case Absent{}:
          GoneCwd{0n}
        case AFile{}:
          FileCwd{0n}
        case ADir{}:
          DirCwd{0n}

# the working dir a create names, as Rust reads it: none, or a path and
# what metadata finds there; an empty path names none. The path itself
# is the number 0 (Rust keeps it; the decision reads only whether it is
# empty)
def cwd.of(m: Maybe<&2, String>, s: Stat) -> Cwd:
  match m:
    case None{}:
      NoCwd{}
    case Some{p}:
      cwd.named(String.is_empty(p), s)

# what Rust asks: the check of a socket dir, the peer rule, the mode of
# what eukhe creates, the working dir of a create
type Ask is Data:
  AskDir{k: Node, uid: Nat, own: Nat, mode: Nat}
  AskPeer{peer: Nat, own: Nat}
  AskMade{k: Made}
  AskCwd{cwd: Maybe<&2, String>, s: Stat}
