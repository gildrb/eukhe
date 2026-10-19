# bridge_skill_load: runs the loading model (`loaded` and `diags` in
# skill_load.bend) on a scenario file and prints what became of each
# candidate, line for line as the Rust bridge test prints the real skill
# and template loaders over a temp dir
# (crates/eukhe-core/src/skills/bridge.rs). Build it with
#
#   bend bend/bridge_skill_load.bend -o <out>
#
# and run `<out> <scenario>`. A scenario has one candidate file per line;
# the candidate of line i has path i:
#
#   kind outcome
#
#   kind     0: a skill (SKILL.md), 1: a prompt template
#   outcome  0: good, 1: unreadable, 2: malformed frontmatter,
#            3: a skill without a description
#
# For each candidate it prints `L` (loaded, no diagnostic), `LD` (loaded
# and named by a diagnostic), `R k` (named by a diagnostic of kind k, not
# loaded) or `S` (neither: dropped without a word).

import Base
import ./skill_load.bend as Sk

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def outcome.of(o: Nat) -> Sk.Outcome:
  match o:
    case 0n:
      Sk.Good{}
    case 1n:
      Sk.Unreadable{}
    case 2n:
      Sk.Malformed{}
    case _:
      Sk.Incomplete{}

# a line that starts with a number is a candidate; others are skipped
def cand.add(m: Maybe<&2, Nat>, +i: Nat, +ws: List<&2, String>, t: List<&2, Sk.Cand>) -> List<&2, Sk.Cand>:
  match m:
    case None{}:
      t
    case Some{x}:
      Sk.Cand{i, outcome.of(tok.nat(tok.at(ws, 1n)))} <> t

# the candidates of the lines ls, the first with path i
def cands(ls: List<&2, String>, +i: Nat) -> List<&2, Sk.Cand>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      +ws = String.split(l, ' ')
      cand.add(Nat.read(tok.at(ws, 0n)), i, ws, cands(rest, 1n+i))

# Writing
# -------

def kind.here(hit: Bool, k: Nat, later: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{k}
    case False{}:
      later

# the kind of the first diagnostic of ds that names p
def kind(ds: List<&2, Sk.Diag>, +p: Nat) -> Maybe<&2, Nat>:
  match ds:
    case Nil{}:
      None{}
    case d <> rest:
      match d:
        case Sk.Diag{q, k}:
          kind.here(Nat.is_eq(q, p), k, kind(rest, p))

def show.one(loaded: Bool, k: Maybe<&2, Nat>) -> String:
  match loaded k:
    case True{} None{}:
      "L\n"
    case True{} Some{x}:
      "LD\n"
    case False{} None{}:
      "S\n"
    case False{} Some{x}:
      String.concat(["R ", Nat.show(x), "\n"])

# what became of each candidate of all, in the order of cs
def show(cs: List<&2, Sk.Cand>, +all: List<&2, Sk.Cand>) -> String:
  match cs:
    case Nil{}:
      ""
    case c <> rest:
      +p = Sk.Cand.path(c)
      String.append(show.one(Sk.listed(Sk.loaded(all), p), kind(Sk.diags(all), p)), show(rest, all))

# the report of the scenario text
def report(text: String) -> String:
  +cs = cands(String.lines(text), 0n)
  show(cs, cs)

# Running
# -------

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
      IO.die(String, 2, "usage: bridge_skill_load <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_skill_load <scenario>")
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
