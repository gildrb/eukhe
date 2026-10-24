# eukhe: lemmas the proofs of area fsmode share

import Base
import ../../bend/ffi_fsmode.bend as FFs
import ../../bend/fsmode.bend as Fs
import ../../bend/wire.bend as Wr
import ../../laws/fsmode.bend as Fsmode

def fsmode.pf.BD(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      A
    case False{}:
      Unit

def fsmode.pf.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : fsmode.pf.BD(_, A)
  Unit{}

# The entry: a Some that is None proves anything
def fs.if_none(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def fs.some_none(-A: Data, -x: A, -G: Type, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  %e : fs.if_none(A, _, G)
  Unit{}

# The reader, stage by stage
# --------------------------

def fs.node_tag(t: Nat, s: String) -> {Fsmode.read_node.tag(t, s) == FFs.get_node.tag(t, s) : Wr.Dec<Fs.Node>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n+p:
      {==}

def fs.node(r: Wr.Dec<Nat>) -> {Fsmode.read_node(r) == FFs.get_node(r) : Wr.Dec<Fs.Node>}:
  match r:
    case Wr.Got{t, s}:
      fs.node_tag(t, s)
    case Wr.Bad{}:
      {==}

def fs.dir_mode(k: Fs.Node, u: Nat, o: Nat, r: Wr.Dec<Nat>) -> {Fsmode.read_dir.mode(k, u, o, r) == FFs.get_dir.mode(k, u, o, r) : Wr.Dec<Fs.Ask>}:
  match r:
    case Wr.Got{m, s}:
      {==}
    case Wr.Bad{}:
      {==}

def fs.dir_own(k: Fs.Node, u: Nat, r: Wr.Dec<Nat>) -> {Fsmode.read_dir.own(k, u, r) == FFs.get_dir.own(k, u, r) : Wr.Dec<Fs.Ask>}:
  match r:
    case Wr.Got{o, s}:
      fs.dir_mode(k, u, o, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def fs.dir_uid(k: Fs.Node, r: Wr.Dec<Nat>) -> {Fsmode.read_dir.uid(k, r) == FFs.get_dir.uid(k, r) : Wr.Dec<Fs.Ask>}:
  match r:
    case Wr.Got{u, s}:
      fs.dir_own(k, u, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def fs.dir(r: Wr.Dec<Fs.Node>) -> {Fsmode.read_dir(r) == FFs.get_dir(r) : Wr.Dec<Fs.Ask>}:
  match r:
    case Wr.Got{k, s}:
      fs.dir_uid(k, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def fs.peer_own(p: Nat, r: Wr.Dec<Nat>) -> {Fsmode.read_peer.own(p, r) == FFs.get_peer.own(p, r) : Wr.Dec<Fs.Ask>}:
  match r:
    case Wr.Got{o, s}:
      {==}
    case Wr.Bad{}:
      {==}

def fs.peer(r: Wr.Dec<Nat>) -> {Fsmode.read_peer(r) == FFs.get_peer(r) : Wr.Dec<Fs.Ask>}:
  match r:
    case Wr.Got{p, s}:
      fs.peer_own(p, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def fs.made_tag(t: Nat, s: String) -> {Fsmode.read_made.tag(t, s) == FFs.get_made.tag(t, s) : Wr.Dec<Fs.Ask>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+p:
      {==}

def fs.made(r: Wr.Dec<Nat>) -> {Fsmode.read_made(r) == FFs.get_made(r) : Wr.Dec<Fs.Ask>}:
  match r:
    case Wr.Got{t, s}:
      fs.made_tag(t, s)
    case Wr.Bad{}:
      {==}

def fs.stat_tag(c: Maybe<&2, String>, t: Nat, s: String) -> {Fsmode.read_stat.tag(c, t, s) == FFs.get_stat.tag(c, t, s) : Wr.Dec<Fs.Ask>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+p:
      {==}

def fs.stat(c: Maybe<&2, String>, r: Wr.Dec<Nat>) -> {Fsmode.read_stat(c, r) == FFs.get_stat(c, r) : Wr.Dec<Fs.Ask>}:
  match r:
    case Wr.Got{t, s}:
      fs.stat_tag(c, t, s)
    case Wr.Bad{}:
      {==}

def fs.cwd_path(r: Wr.Dec<String>) -> {Fsmode.read_cwd.path(r) == FFs.get_cwd.path(r) : Wr.Dec<Fs.Ask>}:
  match r:
    case Wr.Got{p, s}:
      fs.stat(Some{p}, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def fs.cwd_tag(t: Nat, s: String) -> {Fsmode.read_cwd.tag(t, s) == FFs.get_cwd.tag(t, s) : Wr.Dec<Fs.Ask>}:
  match t:
    case 0n:
      fs.stat(None{}, Wr.get_nat(s))
    case 1n:
      fs.cwd_path(Wr.get_str(s))
    case 2n+p:
      {==}

def fs.cwd(r: Wr.Dec<Nat>) -> {Fsmode.read_cwd(r) == FFs.get_cwd(r) : Wr.Dec<Fs.Ask>}:
  match r:
    case Wr.Got{t, s}:
      fs.cwd_tag(t, s)
    case Wr.Bad{}:
      {==}

def fs.ask_tag(t: Nat, +s: String) -> {Fsmode.read_ask.tag(t, s) == FFs.get_ask.tag(t, s) : Wr.Dec<Fs.Ask>}:
  match t:
    case 0n:
      %fs.node(Wr.get_nat(s)) : {Fsmode.read_dir(Fsmode.read_node(Wr.get_nat(s))) == FFs.get_dir(_) : Wr.Dec<Fs.Ask>}
      %fs.dir(Fsmode.read_node(Wr.get_nat(s))) : {Fsmode.read_dir(Fsmode.read_node(Wr.get_nat(s))) == _ : Wr.Dec<Fs.Ask>}
      {==}
    case 1n:
      fs.peer(Wr.get_nat(s))
    case 2n:
      fs.made(Wr.get_nat(s))
    case 3n:
      fs.cwd(Wr.get_nat(s))
    case 4n+p:
      {==}

# the entry reads every input as the laws' reader does
def fs.ask(r: Wr.Dec<Nat>) -> {Fsmode.read_ask.go(r) == FFs.get_ask.go(r) : Wr.Dec<Fs.Ask>}:
  match r:
    case Wr.Got{t, s}:
      fs.ask_tag(t, s)
    case Wr.Bad{}:
      {==}

# The decisions
# -------------

# a real dir: the entry's verdict is the laws' on every owner and mode
def fs.dir_reply(mine: Bool, loose: Bool) -> {FFs.answer.dir(Fs.Seen{Fs.Dir{}, mine, loose}) == Fsmode.dir_reply.dir(mine, loose) : String}:
  match mine loose:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# a named cwd: the entry's verdict is the laws'
def fs.cwd_named(empty: Bool, s: Fs.Stat) -> {FFs.put_open(Fs.open(Fs.cwd.named(empty, s))) == Fsmode.cwd_reply.named(empty, s) : String}:
  match empty:
    case True{}:
      {==}
    case False{}:
      match s:
        case Fs.Absent{}:
          {==}
        case Fs.AFile{}:
          {==}
        case Fs.ADir{}:
          {==}
