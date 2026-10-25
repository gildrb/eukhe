# runners: the model of the tools that run code (docs/tools.md, S7;
# crates/eukhe-core/src/durable/runner.rs).
#
# 1. The registry. A tool has a name, its caps (the effects the code it
#    runs may have, as effect codes) and how the approval gate covers that
#    code. `registry` is every tool a session installs, in install order,
#    as crates/eukhe-core/src/durable/registry.rs installs them; the
#    registry bridge test dumps the real one and compares.
# 2. The cell gate. A tool the gate covers at each call (`ipython`) runs
#    its code unasked only when its caps are within the auto set. Else it
#    asks the attached client, and runs only when the user approves.
#
# Effect codes (crates/eukhe-types/src/shell.rs, `ShellEffect::code`):
# 0 read, 1 write, 2 exec, 3 net, 4 outside, 5 protected, 6 secret. Only
# 0 to 5 are grantable: an auto set never holds 6.

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

# 1. The registry
# ---------------

type Gate is Data:
  Ungated{}   # the tool runs no code of its own (no `Runner`)
  EachStep{}  # each step asks unless within the auto set (`bash`)
  EachCall{}  # each call asks unless within the auto set (`ipython`)

type Tool is Data:
  Tool{name: String, caps: List<&2, Nat>, gate: Gate}

def Tool.name(t: Tool) -> String:
  match t:
    case Tool{n, c, g}:
      n

def Tool.caps(t: Tool) -> List<&2, Nat>:
  match t:
    case Tool{n, c, g}:
      c

def Tool.gate(t: Tool) -> Gate:
  match t:
    case Tool{n, c, g}:
      g

# the tool runs code that may run a program
def runs(+t: Tool) -> Bool:
  elem(Tool.caps(t), exec())

def Gate.gated(g: Gate) -> Bool:
  match g:
    case Ungated{}:
      False{}
    case EachStep{}:
      True{}
    case EachCall{}:
      True{}

# the gate covers the tool's code
def gated(+t: Tool) -> Bool:
  Gate.gated(Tool.gate(t))

# a tool that runs no code of its own
def plain(name: String) -> Tool:
  Tool{name, Nil{}, Ungated{}}

# the tools of the chat memory (`eukhe.optchat`): only a session that has
# chat memory installs them
def chat.tools(chat: Bool) -> List<&2, Tool>:
  match chat:
    case True{}:
      [plain("zoom"), plain("date")]
    case False{}:
      []

# every tool a session installs, in install order (crates/eukhe-core/src/
# durable/registry.rs): `eukhe.rlm`, `eukhe.optchat` when chat holds,
# `eukhe.children` (the worker tools: assign, forward, status),
# `eukhe.workflow`, `eukhe.documents`, `eukhe.shell`, `eukhe.dyn`,
# `codemode` (its script runs no program itself: each tool it calls runs
# through that tool's gate; its model tools `classify` and
# `generateImages` call a model). The `workflow` script runs no program
# either: its agents are child sessions with their own gates.
def registry(chat: Bool) -> List<&2, Tool>:
  Tool{"ipython", [exec()], EachCall{}} <> List.append(&2, Tool, chat.tools(chat), [
    plain("worker_assign"),
    plain("worker_forward"),
    plain("worker_status"),
    plain("workflow"),
    plain("read"),
    plain("edit"),
    plain("grep"),
    plain("glob"),
    Tool{"bash", [0n, 1n, 2n, 3n, 4n, 5n, 6n], EachStep{}},
    plain("dyn"),
    plain("codemode"),
    plain("pi.codemode.models.classify"),
    plain("pi.codemode.models.generateImages"),
  ])

# every tool of ts that runs code is gated
def covered(ts: List<&2, Tool>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case +t <> rest:
      Bool.and(Bool.or(Bool.not(runs(t)), gated(t)), covered(rest))

# the first tool of ts is named n
def named.at(+ts: List<&2, Tool>, +n: String) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case t <> rest:
      String.eq(Tool.name(t), n)

# the first tool of ts named n; hit is named.at(ts, n)
def find.go(ts: List<&2, Tool>, +n: String, hit: Bool) -> Maybe<&2, Tool>:
  match ts:
    case Nil{}:
      None{}
    case t <> +rest:
      match hit:
        case True{}:
          Some{t}
        case False{}:
          find.go(rest, n, named.at(rest, n))

def find(+ts: List<&2, Tool>, +n: String) -> Maybe<&2, Tool>:
  find.go(ts, n, named.at(ts, n))

# 2. The cell gate
# ----------------

# an effect the auto set may hold: every effect but secret (6)
def grantable(c: Nat) -> Bool:
  Nat.is_lt(c, 6n)

# every cap is in the auto set (the auto set keeps only grantable effects)
def within(caps: List<&2, Nat>, +auto: List<&2, Nat>) -> Bool:
  match caps:
    case Nil{}:
      True{}
    case +c <> rest:
      Bool.and(Bool.and(grantable(c), elem(auto, c)), within(rest, auto))

# Who answers a question
type Asker is Data:
  NoClient{}       # no approver attached
  Silent{}         # an approver, who gives no answer
  Says{yes: Bool}  # an approver, who approves (True) or denies (False)

# the asker approves
def Asker.yes(a: Asker) -> Bool:
  match a:
    case NoClient{}:
      False{}
    case Silent{}:
      False{}
    case Says{y}:
      y

type How is Data:
  Auto{}      # within the auto set: unasked
  Approved{}  # the user approved

type Why is Data:
  Denied{}      # the user denied
  Unanswered{}  # no approver, or no answer

type End is Data:
  Ran{how: How}
  Refused{why: Why}

# How a call went: whether it asked, and how it ended
type Out is Data:
  Out{asked: Bool, end: End}

def Out.end(o: Out) -> End:
  match o:
    case Out{a, e}:
      e

def End.ran(e: End) -> Bool:
  match e:
    case Ran{h}:
      True{}
    case Refused{w}:
      False{}

# the code ran
def ran(o: Out) -> Bool:
  End.ran(Out.end(o))

# a gated call; free is within(caps, auto)
def cell.go(free: Bool, a: Asker) -> Out:
  match free:
    case True{}:
      Out{False{}, Ran{Auto{}}}
    case False{}:
      match a:
        case NoClient{}:
          Out{False{}, Refused{Unanswered{}}}
        case Silent{}:
          Out{True{}, Refused{Unanswered{}}}
        case Says{y}:
          match y:
            case True{}:
              Out{True{}, Ran{Approved{}}}
            case False{}:
              Out{True{}, Refused{Denied{}}}

# a call of a tool with caps under the auto set auto, answered by a
def cell(caps: List<&2, Nat>, +auto: List<&2, Nat>, a: Asker) -> Out:
  cell.go(within(caps, auto), a)
