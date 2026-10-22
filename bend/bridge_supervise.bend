# bridge_supervise: runs the model of the timeouts (bend/supervise.bend
# section Timeouts) on an events file and prints the derived values, line
# for line as the Rust bridge test prints the constants
# (crates/eukhe-daemon/src/supervision_bridge.rs,
# `the_timeouts_derive_as_their_model`). The timeouts are Rust `const`
# expressions, so no core call can replace them: the bridge keeps the
# laws on the constants. The restart budget runs as the compiled model
# (bend/ffi_supervise.bend). Build it with
#
#   bend bend/bridge_supervise.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line:
#
#   t V V ...      the timeouts' base values, in the order of Su.Tm (ms)
#
# and it prints, for each `t` line,
#
#   t TD SG DR LW CK LO MA QH WI   the teardown, stop grace, drain,
#                  launcher wait, child kill, lost window, max age,
#                  quiesce hold and restart window

import Base
import ./supervise.bend as Su

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

# Running
# -------

def tm.of(+ws: List<&2, String>) -> Su.Tm:
  Su.Tm{arg(ws, 1n), arg(ws, 2n), arg(ws, 3n), arg(ws, 4n), arg(ws, 5n), arg(ws, 6n), arg(ws, 7n), arg(ws, 8n), arg(ws, 9n), arg(ws, 10n), arg(ws, 11n), arg(ws, 12n), arg(ws, 13n), arg(ws, 14n), arg(ws, 15n), arg(ws, 16n), arg(ws, 17n), arg(ws, 18n), arg(ws, 19n)}

def show.tm(+t: Su.Tm) -> String:
  String.concat(["t ", Nat.show(Su.Tm.teardown(t)), " ", Nat.show(Su.Tm.stop_grace(t)), " ", Nat.show(Su.Tm.drain(t)), " ", Nat.show(Su.Tm.launcher_wait(t)), " ", Nat.show(Su.Tm.child_kill(t)), " ", Nat.show(Su.Tm.lost(t)), " ", Nat.show(Su.Tm.max_age(t)), " ", Nat.show(Su.Tm.quiesce_hold(t)), " ", Nat.show(Su.Tm.window(t)), "\n"])

# one line; h is its first word, ws all its words
def line(out: String, h: String, +ws: List<&2, String>) -> String:
  match h:
    case SCon{'t', r}:
      String.append(out, show.tm(tm.of(ws)))
    case r:
      out

def go(ls: List<&2, String>, out: String) -> String:
  match ls:
    case Nil{}:
      out
    case l <> rest:
      +ws = String.split(l, ' ')
      go(rest, line(out, tok.at(ws, 0n), ws))

def run(text: String) -> String:
  go(String.lines(text), "")

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
      IO.die(String, 2, "usage: bridge_supervise <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_supervise <events>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(run(text))
