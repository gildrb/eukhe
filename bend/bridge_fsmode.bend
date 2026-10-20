# bridge_fsmode: runs the local access model (bend/fsmode.bend) on an
# events file and prints what it decided, line for line as the Rust bridge
# test (crates/eukhe-daemon/src/fsmode_bridge.rs) prints the real code.
# Build it with
#
#   bend bend/bridge_fsmode.bend -o <out>
#
# and run `<out> <events>`. One event per line:
#
#   s N M L   a socket dir: node N (m missing, d dir, l link, o other),
#             this uid owns it (M 1) or not (0), a group or other write
#             bit (L 1) or not (0)
#   p P O     a socket peer of uid P, this process's uid O
#   c K       a creation under eukhe's home: K d (a dir) or f (a file)
#   w n       a session create that names no working dir
#   w g P     ... that names path P, where nothing is
#   w f P     ... that names path P, a file
#   w d P     ... that names path P, a dir
#
# It prints, for each event:
#
#   use | refuse | create U G O then use|refuse
#   accept | drop
#   made K U G O
#   ok P | missing | gone P | notdir P
#
# where U G O are the octal digits of a mode (the `then` verdict is the
# one on the dir the create makes).

import Base
import ./fsmode.bend as Fs

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

def bit(s: String) -> Bool:
  match s:
    case SCon{'1', r}:
      True{}
    case r:
      False{}

def node(s: String) -> Fs.Node:
  match s:
    case SCon{'m', r}:
      Fs.Missing{}
    case SCon{'d', r}:
      Fs.Dir{}
    case SCon{'l', r}:
      Fs.Link{}
    case r:
      Fs.Other{}

def made.kind(s: String) -> Fs.Made:
  match s:
    case SCon{'d', r}:
      Fs.DirMade{}
    case r:
      Fs.FileMade{}

def cwd(s: String, p: Nat) -> Fs.Cwd:
  match s:
    case SCon{'g', r}:
      Fs.GoneCwd{p}
    case SCon{'f', r}:
      Fs.FileCwd{p}
    case SCon{'d', r}:
      Fs.DirCwd{p}
    case r:
      Fs.NoCwd{}

# Showing
# -------

def show.mode(m: Fs.Mode) -> String:
  match m:
    case Fs.Mode{u, g, o}:
      String.concat([Nat.show(u), " ", Nat.show(g), " ", Nat.show(o)])

def show.verdict.after(v: Fs.Verdict) -> String:
  match v:
    case Fs.Create{m}:
      "create"
    case Fs.Use{}:
      "use"
    case Fs.Refuse{}:
      "refuse"

def show.verdict(v: Fs.Verdict) -> String:
  match v:
    case Fs.Create{+m}:
      String.concat(["create ", show.mode(m), " then ", show.verdict.after(Fs.socket_dir(Fs.made(m)))])
    case Fs.Use{}:
      "use"
    case Fs.Refuse{}:
      "refuse"

def show.peer(v: Fs.Peer) -> String:
  match v:
    case Fs.Accept{}:
      "accept"
    case Fs.Drop{}:
      "drop"

def show.made(k: String, m: Fs.Mode) -> String:
  String.concat(["made ", k, " ", show.mode(m)])

def show.open(o: Fs.Open) -> String:
  match o:
    case Fs.Opened{p}:
      String.append("ok ", Nat.show(p))
    case Fs.NeedsCwd{}:
      "missing"
    case Fs.Gone{p}:
      String.append("gone ", Nat.show(p))
    case Fs.NotDir{p}:
      String.append("notdir ", Nat.show(p))

# Running
# -------

def line(w: String, +ws: List<&2, String>) -> String:
  match w:
    case SCon{'s', r}:
      String.append(show.verdict(Fs.socket_dir(Fs.Seen{node(tok.at(ws, 1n)), bit(tok.at(ws, 2n)), bit(tok.at(ws, 3n))})), "\n")
    case SCon{'p', r}:
      String.append(show.peer(Fs.peer(arg(ws, 1n), arg(ws, 2n))), "\n")
    case SCon{'c', r}:
      +k = tok.at(ws, 1n)
      String.append(show.made(k, Fs.made_mode(made.kind(k))), "\n")
    case SCon{'w', r}:
      String.append(show.open(Fs.open(cwd(tok.at(ws, 1n), arg(ws, 2n)))), "\n")
    case r:
      ""

def go(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      String.append(line(tok.at(ws, 0n), ws), go(rest))

def read.done(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Done{text}:
      text
    case Fail{e}:
      ""

def read.file(m: File & Result<&1, &1, U32 & String, String>) -> IO(String):
  (f, r) = m
  do IO<String>:
    Unit <- File.close(f)
    IO.pure(String, read.done(r))

def scenario(args: List<String>) -> IO(String):
  match args:
    case Nil{}:
      IO.die(String, 2, "usage: bridge_fsmode <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_fsmode <events>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text)))
