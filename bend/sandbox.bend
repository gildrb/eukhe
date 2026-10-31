# sandbox: the model of the host and the sandbox.
#
# 1. The protocol. The host decides; the sandbox executes. The sandbox
#    stub sends frames to the host. The host reads each frame: a frame
#    longer than `max`, or of a kind the host does not allow, gets an
#    error reply and does nothing. Every frame gets exactly one reply, in
#    order. Only a frame the host accepted makes an effect.
# 2. A copy-on-write workspace. A subagent works on a copy of the
#    workspace at its start (the base). When it ends, the host takes its
#    changes back into the parent's workspace, path by path:
#    - a path the child did not change keeps the parent's content;
#    - a path the child changed and the parent did not gets the child's;
#    - a path both changed to the same content keeps it;
#    - a path both changed to different contents keeps the parent's and
#      is reported as a conflict. No change is lost in silence.
#
# A recursive scan takes the test of its first item as a parameter (Bend
# matches only parameters); `*.at` computes that test.

import Base

def elem(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, x), elem(rest, x))

# 1. The protocol
# ---------------

type Frame is Data:
  Frame{id: Nat, len: Nat, kind: Nat}

def Frame.id(f: Frame) -> Nat:
  match f:
    case Frame{i, l, k}:
      i

type Reply is Data:
  Ok{id: Nat}
  Err{id: Nat}

def Reply.id(r: Reply) -> Nat:
  match r:
    case Ok{i}:
      i
    case Err{i}:
      i

# the host accepts frame f
def accepts(+max: Nat, +allowed: List<&2, Nat>, f: Frame) -> Bool:
  match f:
    case Frame{i, l, k}:
      Bool.and(Nat.is_le(l, max), elem(allowed, k))

# What the host did: its replies and the frames it ran, in order
type Host is Data:
  Host{replies: List<&2, Reply>, ran: List<&2, Frame>}

def Host.replies(h: Host) -> List<&2, Reply>:
  match h:
    case Host{r, x}:
      r

def Host.ran(h: Host) -> List<&2, Frame>:
  match h:
    case Host{r, x}:
      x

def host.add(good: Bool, +f: Frame, h: Host) -> Host:
  match good:
    case True{}:
      match h:
        case Host{rs, xs}:
          Host{Ok{Frame.id(f)} <> rs, f <> xs}
    case False{}:
      match h:
        case Host{rs, xs}:
          Host{Err{Frame.id(f)} <> rs, xs}

# the host reads frames, in order
def serve(fs: List<&2, Frame>, +max: Nat, +allowed: List<&2, Nat>) -> Host:
  match fs:
    case Nil{}:
      Host{Nil{}, Nil{}}
    case +f <> rest:
      host.add(accepts(max, allowed, f), f, serve(rest, max, allowed))

# the ids of the replies, in order
def reply.ids(rs: List<&2, Reply>) -> List<&2, Nat>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      Reply.id(r) <> reply.ids(rest)

def frame.ids(fs: List<&2, Frame>) -> List<&2, Nat>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      Frame.id(f) <> frame.ids(rest)

# every frame of fs is accepted
def all_ok(fs: List<&2, Frame>, +max: Nat, +allowed: List<&2, Nat>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case +f <> rest:
      Bool.and(accepts(max, allowed, f), all_ok(rest, max, allowed))

def one(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# the number of frames of fs the host accepts
def oks(fs: List<&2, Frame>, +max: Nat, +allowed: List<&2, Nat>) -> Nat:
  match fs:
    case Nil{}:
      0n
    case +f <> rest:
      Nat.add(one(accepts(max, allowed, f)), oks(rest, max, allowed))

# The gate of one host-request frame, as the Rust host runs it
# (crates/eukhe-core/src/kernel/manager/frames.rs `Gate::admit`, through
# the compiled core): Rust reads the frame's facts (its id is fresh or
# seen before, its length, its type and whether the host serves that
# type); the gate refuses a repeated id first, then a frame longer than
# `max`, then a frame with no type or of a type the host does not serve,
# and serves the rest.
type Typed is Data:
  Unnamed{}            # no type (or not a string, or empty)
  Named{served: Bool}  # a type, and whether the host serves it

type Verdict is Data:
  Serve{}
  Duplicate{}
  Oversize{}
  Kindless{}
  NotServed{}

def admit.kind(k: Typed) -> Verdict:
  match k:
    case Unnamed{}:
      Kindless{}
    case Named{s}:
      match s:
        case True{}:
          Serve{}
        case False{}:
          NotServed{}

# fits: the frame is within the limit
def admit.size(fits: Bool, k: Typed) -> Verdict:
  match fits:
    case True{}:
      admit.kind(k)
    case False{}:
      Oversize{}

def admit.fresh(fresh: Bool, +max: Nat, +len: Nat, k: Typed) -> Verdict:
  match fresh:
    case True{}:
      admit.size(Nat.is_le(len, max), k)
    case False{}:
      Duplicate{}

# the verdict on a host-request frame of `len` bytes under the limit
# `max`, whose id is fresh or not, of the type k
def admit(+max: Nat, fresh: Bool, +len: Nat, k: Typed) -> Verdict:
  admit.fresh(fresh, max, len, k)

def Verdict.serve(v: Verdict) -> Bool:
  match v:
    case Serve{}:
      True{}
    case Duplicate{}:
      False{}
    case Oversize{}:
      False{}
    case Kindless{}:
      False{}
    case NotServed{}:
      False{}

# 2. A copy-on-write workspace
# ----------------------------
# A workspace maps paths to contents: None is no file.

type Doc is Data:
  Doc{path: Nat, body: Nat}

def Doc.path(f: Doc) -> Nat:
  match f:
    case Doc{p, b}:
      p

def Doc.body(f: Doc) -> Nat:
  match f:
    case Doc{p, b}:
      b

def path.at(+ws: List<&2, Doc>, +p: Nat) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case f <> rest:
      Nat.is_eq(Doc.path(f), p)

# the content of path p in workspace ws; hit is path.at(ws, p)
def read.go(ws: List<&2, Doc>, +p: Nat, hit: Bool) -> Maybe<&2, Nat>:
  match ws:
    case Nil{}:
      None{}
    case f <> +rest:
      match hit:
        case True{}:
          Some{Doc.body(f)}
        case False{}:
          read.go(rest, p, path.at(rest, p))

def read(+ws: List<&2, Doc>, +p: Nat) -> Maybe<&2, Nat>:
  read.go(ws, p, path.at(ws, p))

def m.eq(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Bool:
  match a:
    case None{}:
      match b:
        case None{}:
          True{}
        case Some{y}:
          False{}
    case Some{x}:
      match b:
        case None{}:
          False{}
        case Some{y}:
          Nat.is_eq(x, y)

# The merge of one path: the parent's content, the base's, the child's
type One is Data:
  One{body: Maybe<&2, Nat>, clash: Bool}

def One.body(o: One) -> Maybe<&2, Nat>:
  match o:
    case One{b, c}:
      b

def One.clash(o: One) -> Bool:
  match o:
    case One{b, c}:
      c

def merge.at(child_changed: Bool, parent_changed: Bool, same: Bool, p: Maybe<&2, Nat>, c: Maybe<&2, Nat>) -> One:
  match child_changed:
    case False{}:
      One{p, False{}}
    case True{}:
      match parent_changed:
        case False{}:
          One{c, False{}}
        case True{}:
          match same:
            case True{}:
              One{p, False{}}
            case False{}:
              One{p, True{}}

def merge1(+p: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +c: Maybe<&2, Nat>) -> One:
  merge.at(Bool.not(m.eq(c, b)), Bool.not(m.eq(p, b)), m.eq(p, c), p, c)

# The plan of one path, as the Rust hand-back runs it: the parent's
# content stays (taken: the child's change is the parent's content
# already), a conflict, the child's file goes in (unless its place in the
# parent is blocked: a directory there, or a file where one of its
# directories goes; then it is a conflict), or the child removed the file
# and the parent's goes. Contents are compared only for equality, so the
# Rust caller passes equal contents as equal ids.
type Plan is Data:
  Keep{taken: Bool}
  Clash{}
  Take{}
  Drop{}

def plan.file(c: Maybe<&2, Nat>) -> Plan:
  match c:
    case None{}:
      Drop{}
    case Some{x}:
      Take{}

def plan.at(calm: Bool, still: Bool, same: Bool, c: Maybe<&2, Nat>) -> Plan:
  match calm:
    case True{}:
      Keep{False{}}
    case False{}:
      match still:
        case True{}:
          plan.file(c)
        case False{}:
          match same:
            case True{}:
              Keep{True{}}
            case False{}:
              Clash{}

# the plan of a path with the parent's content p, the base's b and the
# child's c
def plan(+p: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +c: Maybe<&2, Nat>) -> Plan:
  plan.at(m.eq(c, b), m.eq(p, b), m.eq(p, c), c)

# the merge a plan carries out
def Plan.merge(x: Plan, p: Maybe<&2, Nat>, c: Maybe<&2, Nat>) -> One:
  match x:
    case Keep{t}:
      One{p, False{}}
    case Clash{}:
      One{p, True{}}
    case Take{}:
      One{c, False{}}
    case Drop{}:
      One{c, False{}}

# The hand-back: the parent's new workspace and the conflicts
type Back is Data:
  Back{ws: List<&2, Doc>, clashes: List<&2, Nat>}

def Back.ws(x: Back) -> List<&2, Doc>:
  match x:
    case Back{w, c}:
      w

def Back.clashes(x: Back) -> List<&2, Nat>:
  match x:
    case Back{w, c}:
      c

def back.file(+k: Nat, m: Maybe<&2, Nat>) -> List<&2, Doc>:
  match m:
    case None{}:
      Nil{}
    case Some{v}:
      [Doc{k, v}]

def back.clash(+k: Nat, c: Bool) -> List<&2, Nat>:
  match c:
    case True{}:
      [k]
    case False{}:
      Nil{}

def back.add(+k: Nat, +o: One, x: Back) -> Back:
  match x:
    case Back{w, c}:
      Back{List.append(&2, Doc, back.file(k, One.body(o)), w), List.append(&2, Nat, back.clash(k, One.clash(o)), c)}

# take the child's changes back into the parent, over the paths ks (every
# path of the parent, the base and the child, once each)
def back(ks: List<&2, Nat>, +par: List<&2, Doc>, +base: List<&2, Doc>, +child: List<&2, Doc>) -> Back:
  match ks:
    case Nil{}:
      Back{Nil{}, Nil{}}
    case +k <> rest:
      back.add(k, merge1(read(par, k), read(base, k), read(child, k)), back(rest, par, base, child))
