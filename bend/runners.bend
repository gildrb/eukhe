# runners: the model of the tools that run code (crates/eukhe-core/src/durable/runner.rs).
#
# The registry. A tool has a name, its caps (the effects the code it runs
# may have, as effect codes) and how the gate covers that code: each step
# of `bash` passes the shell step's verdict, each call of `python` is
# judged as an effect with its caps.
# `registry` is every tool a session installs, in install order, as
# crates/eukhe-core/src/durable/registry.rs installs them. `main_roster` is
# the roster of main (a root session in the `main-worker` shape):
# read-only tools and the worker tools only.
#
# Effect codes (crates/eukhe-types/src/shell.rs, `ShellEffect::code`):
# 0 read, 1 write, 2 exec, 3 net, 4 outside, 5 protected, 6 secret.

import Base

def elem(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, x), elem(rest, x))

# the effect `exec`: runs a program
def exec() -> Nat:
  2n

# The registry
# ------------

type Gate is Data:
  Ungated{}   # the tool runs no code of its own (no `Runner`)
  EachStep{}  # each step passes the shell step's verdict (`bash`)
  EachCall{}  # each call is judged as an effect with its caps (`python`)

type ToolReg is Data:
  ToolReg{name: String, caps: List<&2, Nat>, gate: Gate}

def ToolReg.name(t: ToolReg) -> String:
  match t:
    case ToolReg{n, c, g}:
      n

def ToolReg.caps(t: ToolReg) -> List<&2, Nat>:
  match t:
    case ToolReg{n, c, g}:
      c

def ToolReg.gate(t: ToolReg) -> Gate:
  match t:
    case ToolReg{n, c, g}:
      g

# the tool runs code that may run a program
def runs(+t: ToolReg) -> Bool:
  elem(ToolReg.caps(t), exec())

def Gate.gated(g: Gate) -> Bool:
  match g:
    case Ungated{}:
      False{}
    case EachStep{}:
      True{}
    case EachCall{}:
      True{}

# the gate covers the tool's code
def gated(+t: ToolReg) -> Bool:
  Gate.gated(ToolReg.gate(t))

# a tool that runs no code of its own
def plain(name: String) -> ToolReg:
  ToolReg{name, Nil{}, Ungated{}}

# every tool a session installs, in install order (crates/eukhe-core/src/
# durable/registry.rs): `eukhe.rlm`, `eukhe.optchat` (`zoom` and `date`,
# with or without chat memory: a subagent offers its parent's tool list;
# without chat memory they refuse at call time), `eukhe.workflow`,
# `eukhe.documents`, `eukhe.shell`, `eukhe.dyn`, `codemode` (its script
# runs no program itself: each tool it calls runs through that tool's
# gate; its model tools `classify` and `generateImages` call a model).
# The `workflow` script runs no program either: its agents are child
# sessions with their own gates. A session outside the `main-worker`
# shape's main (a `single` session, every child) has no worker tool.
def registry() -> List<&2, ToolReg>:
  [
    ToolReg{"python", [exec()], EachCall{}},
    plain("zoom"),
    plain("date"),
    plain("workflow"),
    plain("read"),
    plain("write"),
    plain("edit"),
    plain("grep"),
    plain("glob"),
    ToolReg{"bash", [0n, 1n, 2n, 3n, 4n, 5n, 6n], EachStep{}},
    plain("dyn"),
    plain("codemode"),
    plain("pi.codemode.models.classify"),
    plain("pi.codemode.models.generateImages"),
  ]

# the worker tools (`eukhe.children`): main's hand-overs to its workers
def worker.tools() -> List<&2, ToolReg>:
  [plain("worker_assign"), plain("worker_forward"), plain("worker_status")]

# the read-only tools of `eukhe.documents`, in install order
def read.tools() -> List<&2, ToolReg>:
  [plain("read"), plain("grep"), plain("glob")]

# the tools of the chat memory (`eukhe.optchat`) on main's roster: main
# offers them only when it has chat memory
def chat.tools(chat: Bool) -> List<&2, ToolReg>:
  match chat:
    case True{}:
      [plain("zoom"), plain("date")]
    case False{}:
      []

# main's roster (a root session in the `main-worker` shape), in install
# order: the chat memory's tools when chat holds, the worker tools, the
# read-only document tools. Main runs no code, edits no file and spawns
# nothing but workers.
def main_roster(chat: Bool) -> List<&2, ToolReg>:
  List.append(&2, ToolReg, chat.tools(chat), List.append(&2, ToolReg, worker.tools(), read.tools()))

# every tool of ts that runs code is gated
def covered(ts: List<&2, ToolReg>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case +t <> rest:
      Bool.and(Bool.or(Bool.not(runs(t)), gated(t)), covered(rest))

# the first tool of ts is named n
def named.at(+ts: List<&2, ToolReg>, +n: String) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case t <> rest:
      String.eq(ToolReg.name(t), n)

# the first tool of ts named n; hit is named.at(ts, n)
def find.go(ts: List<&2, ToolReg>, +n: String, hit: Bool) -> Maybe<&2, ToolReg>:
  match ts:
    case Nil{}:
      None{}
    case t <> +rest:
      match hit:
        case True{}:
          Some{t}
        case False{}:
          find.go(rest, n, named.at(rest, n))

def find(+ts: List<&2, ToolReg>, +n: String) -> Maybe<&2, ToolReg>:
  find.go(ts, n, named.at(ts, n))
