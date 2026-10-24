# eukhe: the laws of area fsmode

import Base
import ../bend/fsmode.bend as Fs
import ../bend/ffi_fsmode.bend as FFs
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- fsmode ----

# LAWS (G1, file modes, the socket dir and the working dir): who
# reaches eukhe's own state. Each law is an open claim about the model in
# bend/fsmode.bend; PROOF.bend proves them (as Fsmode.<law>) with the lemmas
# of proof/fsmode/.

# (G1) Path policy
# ----------------

# File modes, the socket dir and the working dir
# ----------------------------------------------
# docs/runtime.md "Local access", the model in bend/fsmode.bend, which
# runs as the compiled core (entry bend/ffi_fsmode.bend, laws below).

# LAW socket_dir_owned: the daemon binds in a socket dir only when the dir is a real
# directory (not a link), this uid owns it, and no group or other user
# may write in it
law socket_dir_owned:
  for d: Fs.Seen
  for used: {Fs.socket_dir(d) == Fs.Use{} : Fs.Verdict}
  {Fs.Seen.safe(d) == True{} : Bool}

# LAW socket_dir_progress: a safe socket dir is used (the check refuses nothing it must not)
law socket_dir_progress:
  for d: Fs.Seen
  for safe: {Fs.Seen.safe(d) == True{} : Bool}
  {Fs.socket_dir(d) == Fs.Use{} : Fs.Verdict}

# LAW socket_dir_created: a missing socket dir is created with mode 0700
law socket_dir_created:
  for mine: Bool
  for loose: Bool
  {Fs.socket_dir(Fs.Seen{Fs.Missing{}, mine, loose}) == Fs.Create{Fs.dir_mode()} : Fs.Verdict}

# LAW socket_dir_created_used: the dir the daemon creates with mode 0700 is then used
law socket_dir_created_used:
  {Fs.socket_dir(Fs.made(Fs.dir_mode())) == Fs.Use{} : Fs.Verdict}

# LAW peer_same_uid: a socket peer is accepted only when its uid is this process's uid
law peer_same_uid:
  for p: Nat
  for own: Nat
  for ok: {Fs.peer(p, own) == Fs.Accept{} : Fs.Peer}
  {p == own : Nat}

# LAW peer_own_accepted: a peer of this process's uid is accepted
law peer_own_accepted:
  for own: Nat
  {Fs.peer(own, own) == Fs.Accept{} : Fs.Peer}

# LAW private_on_create: every file and dir eukhe creates under its home has no group or
# other permission bit
law private_on_create:
  for k: Fs.Made
  {Fs.Mode.loose(Fs.made_mode(k)) == False{} : Bool}

# LAW cwd_is_explicit: an accepted session create runs in the dir it named, and that dir
# exists
law cwd_is_explicit:
  for c: Fs.Cwd
  for p: Nat
  for ok: {Fs.open(c) == Fs.Opened{p} : Fs.Open}
  {c == Fs.DirCwd{p} : Fs.Cwd}

# LAW cwd_none_refused: a create that names no working dir is refused
law cwd_none_refused:
  {Fs.open(Fs.NoCwd{}) == Fs.NeedsCwd{} : Fs.Open}

# LAW cwd_gone_refused: a create whose working dir is gone is refused, and the refusal
# names that dir
law cwd_gone_refused:
  for p: Nat
  {Fs.open(Fs.GoneCwd{p}) == Fs.Gone{p} : Fs.Open}

# LAW cwd_file_refused: a create whose working dir is a file is refused, and the refusal
# names that path
law cwd_file_refused:
  for p: Nat
  {Fs.open(Fs.FileCwd{p}) == Fs.NotDir{p} : Fs.Open}

# LAW cwd_dir_opens: a create that names an existing dir runs in it
law cwd_dir_opens:
  for p: Nat
  {Fs.open(Fs.DirCwd{p}) == Fs.Opened{p} : Fs.Open}

# The entry Rust calls
# --------------------
# The socket dir check (prepare_socket_dir), the peer rule of every
# listener, the modes of what eukhe creates and the session cwd check run
# as bend/fsmode.bend through the entry bend/ffi_fsmode.bend. The
# spellers and the reader below are the wire grammar of that entry
# written with the wire primitives alone (laws/wire.bend proves their
# round trips); they never call the entry's own codec. Rust sends the raw
# facts: what symlink_metadata found, the owner's uid, its own uid, the
# permission bits, the peer's uid, the named cwd and what metadata found.

# Terms
# -----

# the permission bit of weight w is set in m: (m / w) mod 2 = 1
def wbit(+m: Nat, w: Nat) -> Bool:
  Nat.is_eq(Nat.mod(Nat.div(m, w), 2n), 1n)

# the reply for a real dir: another owner is refused (2, why 2); a mode
# with the group-write (0o020 = 16) or other-write (0o002 = 2) bit is
# refused (2, why 3); else the dir is used (1)
def dir_reply.dir(mine: Bool, loose: Bool) -> String:
  match mine:
    case False{}:
      Wr.put_nat(2n, Wr.put_nat(2n, ""))
    case True{}:
      match loose:
        case True{}:
          Wr.put_nat(2n, Wr.put_nat(3n, ""))
        case False{}:
          Wr.put_nat(1n, "")

# the reply for a socket dir: a missing dir is created with mode 0700
# (0, then 7 0 0); a link is refused (2, why 0); another file is refused
# (2, why 1); a dir as above
def dir_reply(k: Fs.Node, +u: Nat, +o: Nat, +m: Nat) -> String:
  match k:
    case Fs.Missing{}:
      Wr.put_nat(0n, Wr.put_nat(7n, Wr.put_nat(0n, Wr.put_nat(0n, ""))))
    case Fs.Dir{}:
      dir_reply.dir(Nat.is_eq(u, o), Bool.or(wbit(m, 16n), wbit(m, 2n)))
    case Fs.Link{}:
      Wr.put_nat(2n, Wr.put_nat(0n, ""))
    case Fs.Other{}:
      Wr.put_nat(2n, Wr.put_nat(1n, ""))

# the reply for a named cwd (not empty) and what metadata found: a dir
# opens (0); nothing there is gone (2); a file is not a dir (3)
def cwd_reply.stat(s: Fs.Stat) -> String:
  match s:
    case Fs.Absent{}:
      Wr.put_nat(2n, "")
    case Fs.AFile{}:
      Wr.put_nat(3n, "")
    case Fs.ADir{}:
      Wr.put_nat(0n, "")

def cwd_reply.named(empty: Bool, s: Fs.Stat) -> String:
  match empty:
    case True{}:
      Wr.put_nat(1n, "")
    case False{}:
      cwd_reply.stat(s)

# the reply for a create's cwd: none, or an empty path, names none (1)
def cwd_reply(c: Maybe<&2, String>, s: Fs.Stat) -> String:
  match c:
    case None{}:
      Wr.put_nat(1n, "")
    case Some{p}:
      cwd_reply.named(String.is_empty(p), s)

# Spellers

def spell_node(k: Fs.Node, rest: String) -> String:
  match k:
    case Fs.Missing{}:
      Wr.put_nat(0n, rest)
    case Fs.Dir{}:
      Wr.put_nat(1n, rest)
    case Fs.Link{}:
      Wr.put_nat(2n, rest)
    case Fs.Other{}:
      Wr.put_nat(3n, rest)

def spell_stat(s: Fs.Stat, rest: String) -> String:
  match s:
    case Fs.Absent{}:
      Wr.put_nat(0n, rest)
    case Fs.AFile{}:
      Wr.put_nat(1n, rest)
    case Fs.ADir{}:
      Wr.put_nat(2n, rest)

# the request Rust writes for a
def spell_ask(a: Fs.Ask) -> String:
  match a:
    case Fs.AskDir{k, u, o, m}:
      Wr.put_nat(0n, spell_node(k, Wr.put_nat(u, Wr.put_nat(o, Wr.put_nat(m, "")))))
    case Fs.AskPeer{p, o}:
      Wr.put_nat(1n, Wr.put_nat(p, Wr.put_nat(o, "")))
    case Fs.AskMade{k}:
      match k:
        case Fs.DirMade{}:
          Wr.put_nat(2n, Wr.put_nat(0n, ""))
        case Fs.FileMade{}:
          Wr.put_nat(2n, Wr.put_nat(1n, ""))
    case Fs.AskCwd{c, s}:
      match c:
        case None{}:
          Wr.put_nat(3n, Wr.put_nat(0n, spell_stat(s, "")))
        case Some{p}:
          Wr.put_nat(3n, Wr.put_nat(1n, Wr.put_str(p, spell_stat(s, ""))))

# every number and string of a fits the wire
def ask_fits(a: Fs.Ask) -> Bool:
  match a:
    case Fs.AskDir{k, u, o, m}:
      Bool.and(LawsBase.wire_fits(u), Bool.and(LawsBase.wire_fits(o), LawsBase.wire_fits(m)))
    case Fs.AskPeer{p, o}:
      Bool.and(LawsBase.wire_fits(p), LawsBase.wire_fits(o))
    case Fs.AskMade{k}:
      True{}
    case Fs.AskCwd{c, s}:
      match c:
        case None{}:
          True{}
        case Some{p}:
          LawsBase.wire_fits(String.length(p))

# the reply to a: the socket dir's verdict; a peer is accepted (T) only
# when its uid is this process's; what eukhe creates gets 0700 (a dir) or
# 0600 (a file); the cwd's verdict
def spell_answer(a: Fs.Ask) -> String:
  match a:
    case Fs.AskDir{k, u, o, m}:
      dir_reply(k, u, o, m)
    case Fs.AskPeer{p, o}:
      Wr.put_bool(Nat.is_eq(p, o), "")
    case Fs.AskMade{k}:
      match k:
        case Fs.DirMade{}:
          Wr.put_nat(7n, Wr.put_nat(0n, Wr.put_nat(0n, "")))
        case Fs.FileMade{}:
          Wr.put_nat(6n, Wr.put_nat(0n, Wr.put_nat(0n, "")))
    case Fs.AskCwd{c, s}:
      cwd_reply(c, s)

# Reader: the requests the entry accepts, read with the wire primitives

def read_node.tag(t: Nat, s: String) -> Wr.Dec<Fs.Node>:
  match t:
    case 0n:
      Wr.Got{Fs.Missing{}, s}
    case 1n:
      Wr.Got{Fs.Dir{}, s}
    case 2n:
      Wr.Got{Fs.Link{}, s}
    case 3n:
      Wr.Got{Fs.Other{}, s}
    case 4n+p:
      Wr.Bad{}

def read_node(r: Wr.Dec<Nat>) -> Wr.Dec<Fs.Node>:
  match r:
    case Wr.Got{t, s}:
      read_node.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_dir.mode(k: Fs.Node, u: Nat, o: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Fs.Ask>:
  match r:
    case Wr.Got{m, s}:
      Wr.Got{Fs.AskDir{k, u, o, m}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_dir.own(k: Fs.Node, u: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Fs.Ask>:
  match r:
    case Wr.Got{o, s}:
      read_dir.mode(k, u, o, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_dir.uid(k: Fs.Node, r: Wr.Dec<Nat>) -> Wr.Dec<Fs.Ask>:
  match r:
    case Wr.Got{u, s}:
      read_dir.own(k, u, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_dir(r: Wr.Dec<Fs.Node>) -> Wr.Dec<Fs.Ask>:
  match r:
    case Wr.Got{k, s}:
      read_dir.uid(k, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_peer.own(p: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Fs.Ask>:
  match r:
    case Wr.Got{o, s}:
      Wr.Got{Fs.AskPeer{p, o}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_peer(r: Wr.Dec<Nat>) -> Wr.Dec<Fs.Ask>:
  match r:
    case Wr.Got{p, s}:
      read_peer.own(p, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_made.tag(t: Nat, s: String) -> Wr.Dec<Fs.Ask>:
  match t:
    case 0n:
      Wr.Got{Fs.AskMade{Fs.DirMade{}}, s}
    case 1n:
      Wr.Got{Fs.AskMade{Fs.FileMade{}}, s}
    case 2n+p:
      Wr.Bad{}

def read_made(r: Wr.Dec<Nat>) -> Wr.Dec<Fs.Ask>:
  match r:
    case Wr.Got{t, s}:
      read_made.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_stat.tag(c: Maybe<&2, String>, t: Nat, s: String) -> Wr.Dec<Fs.Ask>:
  match t:
    case 0n:
      Wr.Got{Fs.AskCwd{c, Fs.Absent{}}, s}
    case 1n:
      Wr.Got{Fs.AskCwd{c, Fs.AFile{}}, s}
    case 2n:
      Wr.Got{Fs.AskCwd{c, Fs.ADir{}}, s}
    case 3n+p:
      Wr.Bad{}

def read_stat(c: Maybe<&2, String>, r: Wr.Dec<Nat>) -> Wr.Dec<Fs.Ask>:
  match r:
    case Wr.Got{t, s}:
      read_stat.tag(c, t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_cwd.path(r: Wr.Dec<String>) -> Wr.Dec<Fs.Ask>:
  match r:
    case Wr.Got{p, s}:
      read_stat(Some{p}, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_cwd.tag(t: Nat, s: String) -> Wr.Dec<Fs.Ask>:
  match t:
    case 0n:
      read_stat(None{}, Wr.get_nat(s))
    case 1n:
      read_cwd.path(Wr.get_str(s))
    case 2n+p:
      Wr.Bad{}

def read_cwd(r: Wr.Dec<Nat>) -> Wr.Dec<Fs.Ask>:
  match r:
    case Wr.Got{t, s}:
      read_cwd.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.tag(t: Nat, s: String) -> Wr.Dec<Fs.Ask>:
  match t:
    case 0n:
      read_dir(read_node(Wr.get_nat(s)))
    case 1n:
      read_peer(Wr.get_nat(s))
    case 2n:
      read_made(Wr.get_nat(s))
    case 3n:
      read_cwd(Wr.get_nat(s))
    case 4n+p:
      Wr.Bad{}

def read_ask.go(r: Wr.Dec<Nat>) -> Wr.Dec<Fs.Ask>:
  match r:
    case Wr.Got{t, s}:
      read_ask.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.end(whole: Bool, a: Fs.Ask) -> Maybe<&2, Fs.Ask>:
  match whole:
    case True{}:
      Some{a}
    case False{}:
      None{}

def read_ask.whole(r: Wr.Dec<Fs.Ask>) -> Maybe<&2, Fs.Ask>:
  match r:
    case Wr.Got{a, s}:
      read_ask.end(Wr.end(s), a)
    case Wr.Bad{}:
      None{}

# the request s is, when s is exactly one request
def read_ask(s: String) -> Maybe<&2, Fs.Ask>:
  read_ask.whole(read_ask.go(Wr.get_nat(s)))

# Laws
# ----

# LAW fsmode_ffi_answers: on every request Rust writes, the entry answers: a missing socket dir is created with mode 0700, a link and another file are refused, a dir of another owner or with a group- or other-write bit is refused, any other dir is used; a peer is accepted only with this process's uid; a dir eukhe creates is 0700, a file 0600; a create that names no cwd (or an empty one) is refused, a cwd where nothing is is gone, a file is not a dir, a dir opens
law fsmode_ffi_answers:
  for +a: Fs.Ask
  for fits: {ask_fits(a) == True{} : Bool}
  {FFs.ffi(spell_ask(a)) == spell_answer(a) : String}

# LAW fsmode_ffi_malformed: every input that is not exactly one request gets the error form
law fsmode_ffi_malformed:
  for +s: String
  for no: {read_ask(s) == None{} : Maybe<&2, Fs.Ask>}
  {LawsBase.wire_opens_err(FFs.ffi(s)) == True{} : Bool}

# LAW fsmode_ffi_example: anchor: the strings Rust sends: a missing socket dir, a dir 0700, 0755, 0720 and 0702 of this uid, a dir 0700 of root, a link; a peer of another uid; a file eukhe creates; a cwd that is gone, an empty cwd, a cwd that is a file; input left over is refused
law fsmode_ffi_example:
  {FFs.ffi("0,0,0,1000,0,") == "0,7,0,0," : String} &
  {FFs.ffi("0,1,1000,1000,448,") == "1," : String} &
  {FFs.ffi("0,1,1000,1000,493,") == "1," : String} &
  {FFs.ffi("0,1,1000,1000,464,") == "2,3," : String} &
  {FFs.ffi("0,1,1000,1000,450,") == "2,3," : String} &
  {FFs.ffi("0,1,0,1000,448,") == "2,2," : String} &
  {FFs.ffi("0,2,1000,1000,511,") == "2,0," : String} &
  {FFs.ffi("1,5,6,") == "F" : String} &
  {FFs.ffi("2,1,") == "6,0,0," : String} &
  {FFs.ffi("3,1,4,/tmp0,") == "2," : String} &
  {FFs.ffi("3,1,0,2,") == "1," : String} &
  {FFs.ffi("3,1,4,/tmp1,") == "3," : String} &
  {read_ask("1,5,5,x") == None{} : Maybe<&2, Fs.Ask>} &
  {LawsBase.wire_opens_err(FFs.ffi("1,5,5,x")) == True{} : Bool}

# LAW fsmode_ffi_malformed_exact: every input that is not exactly one request gets exactly the error form 'E ', then "fsmode: malformed request" (the text Rust's Reader reports)
law fsmode_ffi_malformed_exact:
  for +s: String
  for no: {read_ask(s) == None{} : Maybe<&2, Fs.Ask>}
  {FFs.ffi(s) == SCon{'E', SCon{' ', "fsmode: malformed request"}} : String}
