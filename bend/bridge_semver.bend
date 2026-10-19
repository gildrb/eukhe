# bridge_semver: runs the release-version model (bend/semver.bend) on a
# scenario file and prints what it decided, line for line as the bridge
# test prints scripts/release/next_version.py
# (scripts/release/test_next_version.py). Build it with
#
#   bend bend/bridge_semver.bend -o <out>
#
# and run `<out> <scenario>`. Each line of the scenario is one case, its
# fields separated by tabs:
#
#   case W T1 T2 ..
#
# W is the workspace version, Ti the tags (any text without a tab or a
# newline). For each case it prints two lines:
#
#   next V            the next release of the series W (`next`), `-`
#                     when W is no version
#   release T TITLE   the release (`release`): its tag and its title,
#                     `-` when there is none

import Base
import ./semver.bend as Sv

def ver.out(m: Maybe<&2, Sv.Ver>) -> String:
  match m:
    case None{}:
      "-"
    case Some{v}:
      Sv.Ver.show(v)

def rel.out(m: Maybe<&2, Sv.Ver>) -> String:
  match m:
    case None{}:
      "-"
    case Some{+v}:
      String.concat([Sv.Tag.of(v), " ", Sv.Rel.title(v)])

def next.of(m: Maybe<&2, Sv.Ver>, +tags: List<&2, String>) -> Maybe<&2, Sv.Ver>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      Some{Sv.Rel.next(s, tags)}

def case.run(+cargo: String, +tags: List<&2, String>) -> String:
  String.concat(["next ", ver.out(next.of(Sv.Ver.parse(cargo), tags)), "\nrelease ", rel.out(Sv.Rel.release(cargo, tags)), "\n"])

def case.of(ok: Bool, fields: List<&2, String>) -> String:
  match ok:
    case True{}:
      match fields:
        case Nil{}:
          ""
        case cargo <> tags:
          case.run(cargo, tags)
    case False{}:
      ""

# a line that does not start with `case` (the empty line after the last)
# prints nothing
def line(ws: List<&2, String>) -> String:
  match ws:
    case Nil{}:
      ""
    case w <> rest:
      case.of(String.eq(w, "case"), rest)

def run(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      String.append(line(String.split(l, '\t')), run(rest))

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
      IO.die(String, 2, "usage: bridge_semver <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_semver <scenario>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(run(String.lines(text)))
