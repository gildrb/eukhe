# approvals: the model of where a question of the approval gate goes
# (docs/tools.md G5; crates/eukhe-daemon/src/shell_approval.rs).
#
# A `bash` step or an `ipython` cell runs unasked when its effects are
# within the auto set (bend/tools.bend `within`); the default auto set is
# every grantable effect. Any other step asks the user. A chain is the
# sessions from the one that asks up to its root: the asking session
# first, then its parent, and so on. Each session, when the question
# reaches it, is one of:
#
#   Away{}       no client is attached: the session hands the question to
#                its parent at once (`relay_shell_approval`).
#   Left{}       its clients get the question (a `shell_approval` frame),
#                and all of them detach without an answer: the session
#                hands the question to its parent then.
#   Says{yes}    its clients get the question, and the first answer
#                approves (True) or denies (False). The phone gateway may
#                be attached too: it is not asked.
#   Phone{}      its only clients are the phone gateway, which shows no
#                question: no frame, and the gateway rule of the session
#                answers at once.
#   PhoneLeft{}  its interactive clients get the question and all detach
#                without an answer, while the phone gateway stays: the
#                gateway rule answers then.
#
# The question goes up the chain until a session's clients answer or a
# session's gateway rule does; above the root there is no one, and the
# question is unanswered (a denial). A frame on a session above the asker
# names the subagent that asks.
#
# The gateway rule: a step that writes a protected path (effect 5) or
# reads or writes a secret (effect 6) is refused; every other step runs.
# The effects are their codes (bend/tools.bend `Eff.code`).

import Base
import ./tools.bend as Tl

type Desk is Data:
  Away{}
  Left{}
  Says{yes: Bool}
  Phone{}
  PhoneLeft{}

# How a question ended: the clients of session `at` (0: the asker, 1: its
# parent, ...) answered, no one did, or the gateway rule of session `at`
# answered
type End is Data:
  Answered{at: Nat, yes: Bool}
  Unanswered{}
  Ruled{at: Nat}

# What becomes of the step (crates/eukhe-types `ShellAnswer`): it runs, a
# client denied it, no one answered, or the gateway rule refused it
type Fate is Data:
  Runs{}
  Denied{}
  Unheard{}
  GatewayRefused{}

# The sessions that showed the question (a frame to their clients), in
# order, and how it ended
type Out is Data:
  Out{shown: List<&2, Nat>, end: End}

def Out.end(o: Out) -> End:
  match o:
    case Out{s, e}:
      e

def Out.shown(o: Out) -> List<&2, Nat>:
  match o:
    case Out{s, e}:
      s

# The clients of the session, or its gateway rule, answer
def Desk.says(d: Desk) -> Bool:
  match d:
    case Away{}:
      False{}
    case Left{}:
      False{}
    case Says{y}:
      True{}
    case Phone{}:
      True{}
    case PhoneLeft{}:
      True{}

# No session of the chain has clients (or a gateway rule) that answer
def quiet(ds: List<&2, Desk>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case d <> rest:
      Bool.and(Bool.not(Desk.says(d)), quiet(rest))

def End.up(e: End) -> End:
  match e:
    case Answered{a, y}:
      Answered{1n+a, y}
    case Unanswered{}:
      Unanswered{}
    case Ruled{a}:
      Ruled{1n+a}

def ups(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      (1n+x) <> ups(rest)

# The parent's outcome, as its child sees it: every session one further
def Out.up(o: Out) -> Out:
  match o:
    case Out{s, e}:
      Out{ups(s), End.up(e)}

# The asker (session 0) showed the question before its parent's outcome
def Out.first(o: Out) -> Out:
  match o:
    case Out{s, e}:
      Out{0n <> s, e}

# Where the question of the first session of ds goes, and how it ends
def route(ds: List<&2, Desk>) -> Out:
  match ds:
    case Nil{}:
      Out{Nil{}, Unanswered{}}
    case d <> rest:
      match d:
        case Away{}:
          Out.up(route(rest))
        case Left{}:
          Out.first(Out.up(route(rest)))
        case Says{y}:
          Out{[0n], Answered{0n, y}}
        case Phone{}:
          Out{Nil{}, Ruled{0n}}
        case PhoneLeft{}:
          Out{[0n], Ruled{0n}}

# A frame on session k names the subagent that asks: every session but the
# asker's own
def named(k: Nat) -> Bool:
  match k:
    case 0n:
      False{}
    case 1n+p:
      True{}

# The auto set of a session whose user sets none (`shell.autoEffects`):
# every effect but secret
def default_auto() -> List<&2, Nat>:
  [0n, 1n, 2n, 3n, 4n, 5n]

def guard(g: Bool) -> Fate:
  match g:
    case True{}:
      GatewayRefused{}
    case False{}:
      Runs{}

# The gateway rule on a step with the effects es
def rule(+es: List<&2, Nat>) -> Fate:
  guard(Bool.or(Tl.elem(es, 5n), Tl.elem(es, 6n)))

def yes.fate(y: Bool) -> Fate:
  match y:
    case True{}:
      Runs{}
    case False{}:
      Denied{}

# What becomes of a step with the effects es whose question ended so
def fate(+es: List<&2, Nat>, e: End) -> Fate:
  match e:
    case Answered{a, y}:
      yes.fate(y)
    case Unanswered{}:
      Unheard{}
    case Ruled{a}:
      rule(es)

# How a step goes: within the auto set it runs, and no one is asked; else
# its question goes its route o, and the step fares f
type Gated is Data:
  Unasked{}
  Routed{o: Out, f: Fate}

def routed(+es: List<&2, Nat>, +o: Out) -> Gated:
  Routed{o, fate(es, Out.end(o))}

def gate.by(w: Bool, +es: List<&2, Nat>, ds: List<&2, Desk>) -> Gated:
  match w:
    case True{}:
      Unasked{}
    case False{}:
      routed(es, route(ds))

# A step with the effects es, under the auto set auto, of the session
# that heads the chain ds
def gate(+auto: List<&2, Nat>, +es: List<&2, Nat>, ds: List<&2, Desk>) -> Gated:
  gate.by(Tl.within(es, auto), es, ds)

# One session's decision (crates/eukhe-daemon/src/shell_approval.rs
# `route`, run as the compiled core): who answers a question of the
# session now
type Here is Data:
  Nobody{}       # no client is attached
  GatewayOnly{}  # clients are attached, and all are the phone gateway
  Clients{}      # an interactive client is attached

# What the session does with the question
type Next is Data:
  Show{}         # a frame to its clients: their answer, or their leaving, decides
  Relay{}        # hand it to the parent session (`relay_shell_approval`)
  Ends{f: Fate}  # it ends here: the step fares f

# a session with no client: up to its parent, else no one answers
def next.alone(+es: List<&2, Nat>, parent: Bool) -> Next:
  match parent:
    case True{}:
      Relay{}
    case False{}:
      Ends{fate(es, Out.end(route(Nil{})))}

# what a session that is h, with a parent or not, does with the question
# of a step with the effects es
def next(+es: List<&2, Nat>, h: Here, parent: Bool) -> Next:
  match h:
    case Nobody{}:
      next.alone(es, parent)
    case GatewayOnly{}:
      Ends{fate(es, Out.end(route([Phone{}])))}
    case Clients{}:
      Show{}

# what the answer yes of a session's clients makes of the step
def answered(+es: List<&2, Nat>, yes: Bool) -> Fate:
  fate(es, Out.end(route([Says{yes}])))
