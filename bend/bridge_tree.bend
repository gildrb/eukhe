# bridge_tree: runs the session tree model (bend/tree.bend) on an events
# file and prints what it did, line for line as the Rust bridge test
# prints the Rust tree (crates/eukhe-durable/src/tree/bridge.rs). Build it
# with
#
#   bend bend/bridge_tree.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line:
#
#   p K P V      record Do{Put{K, P, V}}
#   d K          record Do{Del{K}}
#   s            save a copy of the tree (saves count from 0)
#   b N          record Rewind{diff(tree, save N)}
#   x OPS        record Rewind{OPS}; each op is `P K P V` or `D K`
#   j            replay every record so far, from the empty tree
#
# After each event it prints:
#
#   t K:P:V ...  after p, d and x: the tree, one node per key, in order
#   s N          after s: the index of the save
#   w -K +K:P:V  after b: the diff (a Del is -K, a Put +K:P:V), then the
#                `t` line of the tree after the rewind
#   j K:P:V ...  after j: the tree the replay made

import Base
import ./tree.bend as T

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

# one word of an `x` line: a `P` takes the three words after it, a `D`
# the one after it; the numbers themselves add nothing
def ops.word(w: String, +rest: List<&2, String>, more: List<&2, T.Op>) -> List<&2, T.Op>:
  match w:
    case SCon{'P', t}:
      T.Put{arg(rest, 0n), arg(rest, 1n), arg(rest, 2n)} <> more
    case SCon{'D', t}:
      T.Del{arg(rest, 0n)} <> more
    case t:
      more

# the ops of an `x` line
def ops.of(ws: List<&2, String>) -> List<&2, T.Op>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> +rest:
      ops.word(w, rest, ops.of(rest))

# the save n (empty when there is none)
def saved.at(saves: List<&2, List<&2, T.Ent>>, n: Nat) -> List<&2, T.Ent>:
  Maybe.default(&2, List<&2, T.Ent>, List.get(&2, List<&2, T.Ent>, saves, n), Nil{})

# Writing
# -------

def show.ents(t: List<&2, T.Ent>) -> String:
  match t:
    case Nil{}:
      ""
    case +e <> rest:
      String.concat([" ", Nat.show(T.Ent.k(e)), ":", Nat.show(T.Ent.p(e)), ":", Nat.show(T.Ent.v(e)), show.ents(rest)])

def show.op(o: T.Op) -> String:
  match o:
    case T.Put{k, p, v}:
      String.concat([" +", Nat.show(k), ":", Nat.show(p), ":", Nat.show(v)])
    case T.Del{k}:
      String.append(" -", Nat.show(k))

def show.ops(ops: List<&2, T.Op>) -> String:
  match ops:
    case Nil{}:
      ""
    case o <> rest:
      String.append(show.op(o), show.ops(rest))

def show.tree(t: List<&2, T.Ent>) -> String:
  String.concat(["t", show.ents(t), "\n"])

# Running
# -------

# what one line did: the tree, the saves and the records (newest first)
# after it, and its output
type Out is Data:
  Out{t: List<&2, T.Ent>, saves: List<&2, List<&2, T.Ent>>, recs: List<&2, T.Rec>, text: String}

def Out.t(o: Out) -> List<&2, T.Ent>:
  match o:
    case Out{t, s, r, x}:
      t

def Out.saves(o: Out) -> List<&2, List<&2, T.Ent>>:
  match o:
    case Out{t, s, r, x}:
      s

def Out.recs(o: Out) -> List<&2, T.Rec>:
  match o:
    case Out{t, s, r, x}:
      r

def Out.text(o: Out) -> String:
  match o:
    case Out{t, s, r, x}:
      x

# record r: apply it to t and print the tree after it, after head
def record(+r: T.Rec, +t: List<&2, T.Ent>, +saves: List<&2, List<&2, T.Ent>>, +recs: List<&2, T.Rec>, head: String) -> Out:
  +n = T.apply(t, r)
  Out{n, saves, r <> recs, String.append(head, show.tree(n))}

# a rewind to the save n: print the diff, then the tree after it
def back(+d: List<&2, T.Op>, +t: List<&2, T.Ent>, +saves: List<&2, List<&2, T.Ent>>, +recs: List<&2, T.Rec>) -> Out:
  record(T.Rewind{d}, t, saves, recs, String.concat(["w", show.ops(d), "\n"]))

# one line; h is its first word, ws all its words
def line(h: String, +ws: List<&2, String>, +t: List<&2, T.Ent>, +saves: List<&2, List<&2, T.Ent>>, +recs: List<&2, T.Rec>) -> Out:
  match h:
    case SCon{'p', r}:
      record(T.Do{T.Put{arg(ws, 1n), arg(ws, 2n), arg(ws, 3n)}}, t, saves, recs, "")
    case SCon{'d', r}:
      record(T.Do{T.Del{arg(ws, 1n)}}, t, saves, recs, "")
    case SCon{'x', r}:
      record(T.Rewind{ops.of(ws)}, t, saves, recs, "")
    case SCon{'b', r}:
      back(T.diff(t, saved.at(saves, arg(ws, 1n))), t, saves, recs)
    case SCon{'s', r}:
      Out{t, List.append(&2, List<&2, T.Ent>, saves, [t]), recs, String.concat(["s ", Nat.show(List.length(&2, List<&2, T.Ent>, saves)), "\n"])}
    case SCon{'j', r}:
      Out{t, saves, recs, String.concat(["j", show.ents(T.replay(List.reverse(&2, T.Rec, recs))), "\n"])}
    case r:
      Out{t, saves, recs, ""}

def go(ls: List<&2, String>, +t: List<&2, T.Ent>, +saves: List<&2, List<&2, T.Ent>>, +recs: List<&2, T.Rec>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +o = line(tok.at(ws, 0n), ws, t, saves, recs)
      String.append(Out.text(o), go(rest, Out.t(o), Out.saves(o), Out.recs(o)))

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
      IO.die(String, 2, "usage: bridge_tree <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_tree <events>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text), Nil{}, Nil{}, Nil{}))
