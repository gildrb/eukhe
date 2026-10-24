import Base
import ./wire.bend as W
import ./fsmode.bend as M

# ffi_fsmode: who reaches eukhe's own state (bend/fsmode.bend `socket_dir`
# of `look`, `why`, `peer`, `made_mode`, `open` of `cwd.of`) as an entry
# of the compiled Bend core. Request: a tag, then
#   0  a socket dir: what symlink_metadata found (0 missing, 1 a dir,
#      2 a link, 3 another file), its owner's uid, this process's uid, its
#      permission bits (mode & 0o7777)
#   1  a socket peer: its uid, this process's uid
#   2  what eukhe creates: 0 a dir, 1 a file
#   3  a create's working dir: 0 none | 1 and the path; then what metadata
#      finds there (0 nothing, 1 a file, 2 a dir)
# Reply: a socket dir: 0 create, then the mode's user, group and other
# digits | 1 use | 2 refuse, then why (0 a link, 1 not a dir, 2 another
# owner, 3 a mode others may write); a peer: T accept | F drop; a
# creation: the mode's three digits; a working dir: 0 opened | 1 none
# named | 2 gone | 3 not a dir. Any other input: the error form.

# Decoding
# --------

def get_node.tag(t: Nat, s: String) -> W.Dec<M.Node>:
  match t:
    case 0n:
      W.Got{M.Missing{}, s}
    case 1n:
      W.Got{M.Dir{}, s}
    case 2n:
      W.Got{M.Link{}, s}
    case 3n:
      W.Got{M.Other{}, s}
    case 4n+p:
      W.Bad{}

def get_node(r: W.Dec<Nat>) -> W.Dec<M.Node>:
  match r:
    case W.Got{t, s}:
      get_node.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_dir.mode(k: M.Node, u: Nat, o: Nat, r: W.Dec<Nat>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{m, s}:
      W.Got{M.AskDir{k, u, o, m}, s}
    case W.Bad{}:
      W.Bad{}

def get_dir.own(k: M.Node, u: Nat, r: W.Dec<Nat>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{o, s}:
      get_dir.mode(k, u, o, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_dir.uid(k: M.Node, r: W.Dec<Nat>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{u, s}:
      get_dir.own(k, u, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_dir(r: W.Dec<M.Node>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{k, s}:
      get_dir.uid(k, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_peer.own(p: Nat, r: W.Dec<Nat>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{o, s}:
      W.Got{M.AskPeer{p, o}, s}
    case W.Bad{}:
      W.Bad{}

def get_peer(r: W.Dec<Nat>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{p, s}:
      get_peer.own(p, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_made.tag(t: Nat, s: String) -> W.Dec<M.Ask>:
  match t:
    case 0n:
      W.Got{M.AskMade{M.DirMade{}}, s}
    case 1n:
      W.Got{M.AskMade{M.FileMade{}}, s}
    case 2n+p:
      W.Bad{}

def get_made(r: W.Dec<Nat>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{t, s}:
      get_made.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_stat.tag(m: Maybe<&2, String>, t: Nat, s: String) -> W.Dec<M.Ask>:
  match t:
    case 0n:
      W.Got{M.AskCwd{m, M.Absent{}}, s}
    case 1n:
      W.Got{M.AskCwd{m, M.AFile{}}, s}
    case 2n:
      W.Got{M.AskCwd{m, M.ADir{}}, s}
    case 3n+p:
      W.Bad{}

def get_stat(m: Maybe<&2, String>, r: W.Dec<Nat>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{t, s}:
      get_stat.tag(m, t, s)
    case W.Bad{}:
      W.Bad{}

def get_cwd.path(r: W.Dec<String>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{p, s}:
      get_stat(Some{p}, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_cwd.tag(t: Nat, s: String) -> W.Dec<M.Ask>:
  match t:
    case 0n:
      get_stat(None{}, W.get_nat(s))
    case 1n:
      get_cwd.path(W.get_str(s))
    case 2n+p:
      W.Bad{}

def get_cwd(r: W.Dec<Nat>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{t, s}:
      get_cwd.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_ask.tag(t: Nat, s: String) -> W.Dec<M.Ask>:
  match t:
    case 0n:
      get_dir(get_node(W.get_nat(s)))
    case 1n:
      get_peer(W.get_nat(s))
    case 2n:
      get_made(W.get_nat(s))
    case 3n:
      get_cwd(W.get_nat(s))
    case 4n+p:
      W.Bad{}

def get_ask.go(r: W.Dec<Nat>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{t, s}:
      get_ask.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_ask(s: String) -> W.Dec<M.Ask>:
  get_ask.go(W.get_nat(s))

# Encoding
# --------

def put_mode(m: M.Mode, rest: String) -> String:
  match m:
    case M.Mode{u, g, o}:
      W.put_nat(u, W.put_nat(g, W.put_nat(o, rest)))

def put_why(w: M.Why, rest: String) -> String:
  match w:
    case M.WhyLink{}:
      W.put_nat(0n, rest)
    case M.WhyNotDir{}:
      W.put_nat(1n, rest)
    case M.WhyOwner{}:
      W.put_nat(2n, rest)
    case M.WhyMode{}:
      W.put_nat(3n, rest)

def put_verdict(v: M.Verdict, d: M.Seen) -> String:
  match v:
    case M.Create{m}:
      W.put_nat(0n, put_mode(m, ""))
    case M.Use{}:
      W.put_nat(1n, "")
    case M.Refuse{}:
      W.put_nat(2n, put_why(M.why(d), ""))

def put_peer(p: M.Peer) -> String:
  match p:
    case M.Accept{}:
      W.put_bool(True{}, "")
    case M.Drop{}:
      W.put_bool(False{}, "")

def put_open(o: M.Open) -> String:
  match o:
    case M.Opened{p}:
      W.put_nat(0n, "")
    case M.NeedsCwd{}:
      W.put_nat(1n, "")
    case M.Gone{p}:
      W.put_nat(2n, "")
    case M.NotDir{p}:
      W.put_nat(3n, "")

# The entry
# ---------

def answer.dir(+d: M.Seen) -> String:
  put_verdict(M.socket_dir(d), d)

# the answer to a request
def answer(a: M.Ask) -> String:
  match a:
    case M.AskDir{k, u, o, m}:
      answer.dir(M.look(k, u, o, m))
    case M.AskPeer{p, o}:
      put_peer(M.peer(p, o))
    case M.AskMade{k}:
      put_mode(M.made_mode(k), "")
    case M.AskCwd{c, s}:
      put_open(M.open(M.cwd.of(c, s)))

def fail() -> String:
  W.err("fsmode: malformed request")

def run.end(whole: Bool, a: M.Ask) -> String:
  match whole:
    case True{}:
      answer(a)
    case False{}:
      fail()

def run(r: W.Dec<M.Ask>) -> String:
  match r:
    case W.Got{a, s}:
      run.end(W.end(s), a)
    case W.Bad{}:
      fail()

def ffi(input: String) -> String:
  run(get_ask(input))
