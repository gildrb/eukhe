# bridge_config: runs the config model (bend/config.bend) on a scenario
# file and prints what the model says, line for line as the Rust bridge
# test prints the real code (crates/eukhe-core/src/settings/bridge.rs).
# Build it with
#
#   bend bridge/bridge_config.bend -o <out>
#
# and run `<out> <scenario>`. The first line names the kind:
#
#   rmw <read> <edit> <k> <v>   a read/modify/write (read 0: missing,
#                               1: parsed, 2: broken; edit 0: set k to v,
#                               1: delete k); `e <k> <v>` lines are the
#                               document read
#   save <k> <v>                a settings setter of k to v; `l <k> <v>`
#                               lines are the copy it loaded, `e <k> <v>`
#                               lines the document on disk
#   leaf                        `f <path> <outcome>` lines (0: good,
#                               1: bad type, 2: undeclared)
#   limit <shape>               providerMaxInFlight (0: unset, 1: a map,
#                               2: not a map); `s <p> <n>` and `s <p> x`
#                               (malformed) lines are the map
#   trust <t>                   0: trusted, 1: untrusted; `g <k> <v>`
#                               lines are the global document, `i <k>
#                               <class> <v>` the project items (class 0:
#                               preference, 1: limit, 2: prompt,
#                               3: credential)
#   merge                       `G <n> [<k> <v>]*` and `P <n> [<k> <v>]*`
#                               lines are the global and project entries
#
# `q <key>` lines name the keys to print. It prints, for each:
#
#   rmw, save, trust            `<key> <value>` or `<key> -` (none)
#   limit                       `<key> U` (unlimited) or `<key> C <n>`
#   merge                       `<key> -` or `<key>` and ` <k>=<v>` for
#                               each field of the entry
#
# and for each leaf `L` (applies), `R` (named by a diagnostic), `LD`
# (both) or `S` (neither).

import Base
import ../bend/config.bend as Cf

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def words(ls: List<&2, String>) -> List<&2, List<&2, String>>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      String.split(l, ' ') <> words(rest)

def tagged.put(hit: Bool, ws: List<&2, String>, rest: List<&2, List<&2, String>>) -> List<&2, List<&2, String>>:
  match hit:
    case True{}:
      List.drop(&2, String, ws, 1n) <> rest
    case False{}:
      rest

# the lines whose first word is tag, without it
def tagged(ls: List<&2, List<&2, String>>, +tag: String) -> List<&2, List<&2, String>>:
  match ls:
    case Nil{}:
      Nil{}
    case +ws <> rest:
      tagged.put(String.eq(tok.at(ws, 0n), tag), ws, tagged(rest, tag))

def entries(ls: List<&2, List<&2, String>>) -> List<&2, Cf.Entry>:
  match ls:
    case Nil{}:
      Nil{}
    case +ws <> rest:
      Cf.Entry{tok.nat(tok.at(ws, 0n)), tok.nat(tok.at(ws, 1n))} <> entries(rest)

def keys(ls: List<&2, List<&2, String>>) -> List<&2, Nat>:
  match ls:
    case Nil{}:
      Nil{}
    case +ws <> rest:
      tok.nat(tok.at(ws, 0n)) <> keys(rest)

# Writing
# -------

def show.value(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "-"
    case Some{v}:
      Nat.show(v)

def line(k: Nat, s: String) -> String:
  String.concat([Nat.show(k), " ", s, "\n"])

# Writes
# ------

def read.of(+r: Nat, d: List<&2, Cf.Entry>) -> Cf.Read:
  match r:
    case 0n:
      Cf.Missing{}
    case 1n:
      Cf.Parsed{d}
    case _:
      Cf.Broken{}

def edit.of(e: Nat, +k: Nat, v: Nat) -> Cf.Edit:
  match e:
    case 0n:
      Cf.Set{k, v}
    case _:
      Cf.Del{k}

def show.kept(+w: Cf.Write, qs: List<&2, Nat>) -> String:
  match qs:
    case Nil{}:
      ""
    case +q <> rest:
      String.append(line(q, show.value(Cf.kept(w, q))), show.kept(w, rest))

def run.rmw(+head: List<&2, String>, +ls: List<&2, List<&2, String>>) -> String:
  +k = tok.nat(tok.at(head, 3n))
  +r = read.of(tok.nat(tok.at(head, 1n)), entries(tagged(ls, "e")))
  +e = edit.of(tok.nat(tok.at(head, 2n)), k, tok.nat(tok.at(head, 4n)))
  show.kept(Cf.rmw(r, e), keys(tagged(ls, "q")))

def run.save(+head: List<&2, String>, +ls: List<&2, List<&2, String>>) -> String:
  +loaded = entries(tagged(ls, "l"))
  +w = Cf.save(loaded, Cf.Parsed{entries(tagged(ls, "e"))}, tok.nat(tok.at(head, 1n)), tok.nat(tok.at(head, 2n)))
  show.kept(w, keys(tagged(ls, "q")))

# Leaves
# ------

def outcome.of(o: Nat) -> Cf.Outcome:
  match o:
    case 0n:
      Cf.Good{}
    case 1n:
      Cf.BadType{}
    case _:
      Cf.Undeclared{}

def leaves(ls: List<&2, List<&2, String>>) -> List<&2, Cf.Leaf>:
  match ls:
    case Nil{}:
      Nil{}
    case +ws <> rest:
      Cf.Leaf{tok.nat(tok.at(ws, 0n)), outcome.of(tok.nat(tok.at(ws, 1n)))} <> leaves(rest)

def show.leaf(applied: Bool, reported: Bool) -> String:
  match applied reported:
    case True{} False{}:
      "L\n"
    case True{} True{}:
      "LD\n"
    case False{} False{}:
      "S\n"
    case False{} True{}:
      "R\n"

def show.leaves(ls: List<&2, Cf.Leaf>, +all: List<&2, Cf.Leaf>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +p = Cf.Leaf.path(l)
      String.append(show.leaf(Cf.listed(Cf.applied(all), p), Cf.listed(Cf.reported(all), p)), show.leaves(rest, all))

def run.leaf(+ls: List<&2, List<&2, String>>) -> String:
  +all = leaves(tagged(ls, "f"))
  show.leaves(all, all)

# Limits
# ------

def val.pick(malformed: Bool, s: String) -> Cf.Val:
  match malformed:
    case True{}:
      Cf.Malformed{}
    case False{}:
      Cf.Num{tok.nat(s)}

def val.of(+s: String) -> Cf.Val:
  val.pick(String.eq(s, "x"), s)

def slots(ls: List<&2, List<&2, String>>) -> List<&2, Cf.Slot>:
  match ls:
    case Nil{}:
      Nil{}
    case +ws <> rest:
      Cf.Slot{tok.nat(tok.at(ws, 0n)), val.of(tok.at(ws, 1n))} <> slots(rest)

def inflight.of(+shape: Nat, es: List<&2, Cf.Slot>) -> Cf.InFlight:
  match shape:
    case 0n:
      Cf.Unset{}
    case 1n:
      Cf.Entries{es}
    case _:
      Cf.NotMap{}

def show.lim(l: Cf.Lim) -> String:
  match l:
    case Cf.Unlimited{}:
      "U"
    case Cf.Cap{n}:
      String.append("C ", Nat.show(n))

def show.limits(+s: Cf.InFlight, qs: List<&2, Nat>) -> String:
  match qs:
    case Nil{}:
      ""
    case +q <> rest:
      String.append(line(q, show.lim(Cf.limit(s, q))), show.limits(s, rest))

def run.limit(+head: List<&2, String>, +ls: List<&2, List<&2, String>>) -> String:
  +s = inflight.of(tok.nat(tok.at(head, 1n)), slots(tagged(ls, "s")))
  show.limits(s, keys(tagged(ls, "q")))

# Trust
# -----

def class.of(c: Nat) -> Cf.Class:
  match c:
    case 0n:
      Cf.Pref{}
    case 1n:
      Cf.Limit{}
    case 2n:
      Cf.Prompt{}
    case _:
      Cf.Credential{}

def items(ls: List<&2, List<&2, String>>) -> List<&2, Cf.Item>:
  match ls:
    case Nil{}:
      Nil{}
    case +ws <> rest:
      Cf.Item{tok.nat(tok.at(ws, 0n)), class.of(tok.nat(tok.at(ws, 1n))), tok.nat(tok.at(ws, 2n))} <> items(rest)

def trust.of(t: Nat) -> Cf.Trust:
  match t:
    case 0n:
      Cf.Trusted{}
    case _:
      Cf.Untrusted{}

def show.values(+d: List<&2, Cf.Entry>, qs: List<&2, Nat>) -> String:
  match qs:
    case Nil{}:
      ""
    case +q <> rest:
      String.append(line(q, show.value(Cf.lookup(d, q))), show.values(d, rest))

def run.trust(+head: List<&2, String>, +ls: List<&2, List<&2, String>>) -> String:
  +d = Cf.effective(trust.of(tok.nat(tok.at(head, 1n))), entries(tagged(ls, "g")), items(tagged(ls, "i")))
  show.values(d, keys(tagged(ls, "q")))

# Named entries
# -------------

def fields(ws: List<&2, String>) -> List<&2, Cf.Entry>:
  match ws:
    case Nil{}:
      Nil{}
    case k <> rest:
      match rest:
        case Nil{}:
          Nil{}
        case v <> more:
          Cf.Entry{tok.nat(k), tok.nat(v)} <> fields(more)

def named(ls: List<&2, List<&2, String>>) -> List<&2, Cf.Named>:
  match ls:
    case Nil{}:
      Nil{}
    case +ws <> rest:
      Cf.Named{tok.nat(tok.at(ws, 0n)), fields(List.drop(&2, String, ws, 1n))} <> named(rest)

def show.fields(fs: List<&2, Cf.Entry>) -> String:
  match fs:
    case Nil{}:
      ""
    case f <> rest:
      match f:
        case Cf.Entry{k, v}:
          String.concat([" ", Nat.show(k), "=", Nat.show(v), show.fields(rest)])

def show.entry(m: Maybe<&2, List<&2, Cf.Entry>>) -> String:
  match m:
    case None{}:
      " -"
    case Some{fs}:
      show.fields(fs)

def show.entries(+es: List<&2, Cf.Named>, qs: List<&2, Nat>) -> String:
  match qs:
    case Nil{}:
      ""
    case +q <> rest:
      String.concat([Nat.show(q), show.entry(Cf.find(es, q)), "\n", show.entries(es, rest)])

def run.merge(+ls: List<&2, List<&2, String>>) -> String:
  +es = Cf.merge(named(tagged(ls, "G")), named(tagged(ls, "P")))
  show.entries(es, keys(tagged(ls, "q")))

# Running
# -------

def choose(b: Bool, yes: String, no: String) -> String:
  match b:
    case True{}:
      yes
    case False{}:
      no

def run.kind(+kind: String, +head: List<&2, String>, +ls: List<&2, List<&2, String>>) -> String:
  +merge = choose(String.eq(kind, "trust"), run.trust(head, ls), run.merge(ls))
  +limit = choose(String.eq(kind, "limit"), run.limit(head, ls), merge)
  +leaf = choose(String.eq(kind, "leaf"), run.leaf(ls), limit)
  +save = choose(String.eq(kind, "save"), run.save(head, ls), leaf)
  choose(String.eq(kind, "rmw"), run.rmw(head, ls), save)

def report.of(ls: List<&2, List<&2, String>>) -> String:
  match ls:
    case Nil{}:
      ""
    case +head <> rest:
      run.kind(tok.at(head, 0n), head, rest)

def report(text: String) -> String:
  report.of(words(String.lines(text)))

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
      IO.die(String, 2, "usage: bridge_config <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_config <scenario>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(report(text))
