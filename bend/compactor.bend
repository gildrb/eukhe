# compactor: the decisions that make a compactor call end (docs/harness.md
# H1) and the wait for a settled view end (H2), against any model reply.
#
# - A line (H1): at most `tries` calls; an empty or thinking-only reply is
#   a try that ends the call; a follow-up not shorter than the best reply
#   ends it too; the first reply that fits wins, else the shortest reply
#   cut to `node` bytes at a character boundary, else the input cut so.
#   A provider error fails the call.
# - The settle (H2): every view line not built yet is a pending line with
#   the failures it has left before the cap builds it from its input. Each
#   outcome that counts (a saved line, a failed call) of a pending line's
#   call lowers the measure (the failures left plus one, summed); a disk
#   error and a stop change nothing. So the view settles after a bounded
#   number of counted outcomes. A waiting turn stops no call it needs, and
#   the queue starts one whenever a job slot is free and a needed line
#   has no call.
#
# Text is a list of characters by their UTF-8 width: lengths are bytes,
# and a cut never splits a character. LAWS.bend states the laws (H1, H2);
# PROOF.bend section compactor proves them; bridge/bridge_compactor.bend runs
# `line` on the scenarios of the Rust bridge test.

import Base
import ./optchat.bend as O

# Text
# ----

# one character, by its UTF-8 width in bytes
type W is Data:
  W1{}
  W2{}
  W3{}
  W4{}

def W.size(c: W) -> Nat:
  match c:
    case W1{}:
      1n
    case W2{}:
      2n
    case W3{}:
      3n
    case W4{}:
      4n

# bytes
def Text.len(t: List<&2, W>) -> Nat:
  match t:
    case Nil{}:
      0n
    case c <> rest:
      Nat.add(W.size(c), Text.len(rest))

def W.eq(a: W, b: W) -> Bool:
  match a b:
    case W1{} W1{}:
      True{}
    case W2{} W2{}:
      True{}
    case W3{} W3{}:
      True{}
    case W4{} W4{}:
      True{}
    case _ _:
      False{}

def Text.eq(a: List<&2, W>, b: List<&2, W>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} y <> ys:
      False{}
    case x <> xs Nil{}:
      False{}
    case x <> xs y <> ys:
      Bool.and(W.eq(x, y), Text.eq(xs, ys))

# the longest start of t within room bytes: never inside a character
def cut(t: List<&2, W>, room: Nat) -> List<&2, W>:
  match t:
    case Nil{}:
      Nil{}
    case c <> rest:
      match c room:
        case W1{} 1n+r:
          W1{} <> cut(rest, r)
        case W2{} 2n+r:
          W2{} <> cut(rest, r)
        case W3{} 3n+r:
          W3{} <> cut(rest, r)
        case W4{} 4n+r:
          W4{} <> cut(rest, r)
        case _ _:
          Nil{}

# the start of t a cut of room bytes reads: every character that fits,
# then the next one (all the compactor sends of a long input)
def Text.lead(t: List<&2, W>, room: Nat) -> List<&2, W>:
  match t:
    case Nil{}:
      Nil{}
    case c <> rest:
      match c room:
        case W1{} 1n+r:
          W1{} <> Text.lead(rest, r)
        case W2{} 2n+r:
          W2{} <> Text.lead(rest, r)
        case W3{} 3n+r:
          W3{} <> Text.lead(rest, r)
        case W4{} 4n+r:
          W4{} <> Text.lead(rest, r)
        case c _:
          [c]

# A line (H1)
# -----------

# A reply: a provider error (or no reply by the call's deadline), or its
# text, thinking dropped and trimmed ([] when empty or thinking only).
type Reply is Data:
  Erred{}
  Says{text: List<&2, W>}

# how many calls a line made, and the line (None: the call failed)
type Line is Data:
  Line{calls: Nat, line: Maybe<&2, List<&2, W>>}

def Line.calls(o: Line) -> Nat:
  match o:
    case Line{c, l}:
      c

def Line.line(o: Line) -> Maybe<&2, List<&2, W>>:
  match o:
    case Line{c, l}:
      l

def Line.more(o: Line) -> Line:
  match o:
    case Line{c, l}:
      Line{1n+c, l}

# a reply of len bytes is shorter than the best reply so far, of bl bytes
# (any reply is, before the first)
def shorter(+len: Nat, best: Maybe<&2, List<&2, W>>, bl: Nat) -> Bool:
  match best:
    case None{}:
      True{}
    case Some{b}:
      Nat.is_lt(len, bl)

# the line when no reply fits: the best reply cut, else the input cut
def line.end(+node: Nat, best: Maybe<&2, List<&2, W>>, input: List<&2, W>) -> List<&2, W>:
  match best:
    case None{}:
      cut(input, node)
    case Some{b}:
      cut(b, node)

def line.next(fit: Bool, less: Bool, ws: List<&2, W>, +node: Nat, best: Maybe<&2, List<&2, W>>, input: List<&2, W>, rec: Line) -> Line:
  match fit less:
    case True{} _:
      Line{1n, Some{ws}}
    case False{} False{}:
      Line{1n, Some{line.end(node, best, input)}}
    case False{} True{}:
      Line.more(rec)

# one call per try, while tries are left: rs are the model's replies in
# order, best the shortest reply so far (each follow-up is shorter) and bl
# its length
def line.go(tries: Nat, +node: Nat, +best: Maybe<&2, List<&2, W>>, +bl: Nat, rs: List<&2, Reply>, +input: List<&2, W>) -> Line:
  match tries:
    case 0n:
      Line{0n, Some{line.end(node, best, input)}}
    case 1n+p:
      match rs:
        case Nil{}:
          Line{1n, None{}}
        case r <> rest:
          match r:
            case Erred{}:
              Line{1n, None{}}
            case Says{ws}:
              match ws:
                case Nil{}:
                  Line{1n, Some{line.end(node, best, input)}}
                case +w <> +t:
                  +len = Text.len(w <> t)
                  line.next(Nat.is_le(len, node), shorter(len, best, bl), w <> t, node, best, input, line.go(p, node, Some{w <> t}, len, rest, input))

# the line of a node: input, at most tries calls, node bytes
def line(tries: Nat, +node: Nat, +input: List<&2, W>, rs: List<&2, Reply>) -> Line:
  line.go(tries, node, None{}, 0n, rs, input)

# The line, one reply at a time
# ------------------------------
# The shipped decision: the compactor asks the model, and before it asks
# again it hands the reply to line.step, which ends the line or asks for
# the next reply. Driven over the replies, the steps are `line` itself
# (law line_steps), so every law of `line` holds for them.

# a line being written: tries left, calls made, its size, the shortest
# reply so far and its length, the input
type Lst is Data:
  Lst{left: Nat, made: Nat, node: Nat, best: Maybe<&2, List<&2, W>>, bl: Nat, input: List<&2, W>}

# how a line ends: the reply just read, whole, or cut to the node (the last
# try); the best reply before it cut so; the input cut so; a failed call
type Fin is Data:
  Whole{text: List<&2, W>}
  CutReply{text: List<&2, W>}
  CutBest{text: List<&2, W>}
  CutInput{text: List<&2, W>}
  Lost{}

# after a reply: the line ends after so many calls, or the next call goes
type Next is Data:
  Ends{calls: Nat, end: Fin}
  Asks{st: Lst}

def Lst.made(st: Lst) -> Nat:
  match st:
    case Lst{left, made, node, best, bl, input}:
      made

def end.of(best: Maybe<&2, List<&2, W>>, input: List<&2, W>) -> Fin:
  match best:
    case None{}:
      CutInput{input}
    case Some{b}:
      CutBest{b}

# the line an end stands for
def Fin.line(+node: Nat, e: Fin) -> Maybe<&2, List<&2, W>>:
  match e:
    case Whole{ws}:
      Some{ws}
    case CutReply{ws}:
      Some{cut(ws, node)}
    case CutBest{b}:
      Some{cut(b, node)}
    case CutInput{i}:
      Some{cut(i, node)}
    case Lost{}:
      None{}

# with tries left, the next call goes; with none, the line ends
def line.again(left: Nat, st: Lst) -> Next:
  match left st:
    case 0n Lst{l, made, node, best, bl, input}:
      Ends{made, end.of(best, input)}
    case 1n+q st:
      Asks{st}

def line.says(fit: Bool, less: Bool, +p: Nat, +made: Nat, +node: Nat, best: Maybe<&2, List<&2, W>>, input: List<&2, W>, ws: List<&2, W>, +len: Nat) -> Next:
  match fit less:
    case True{} _:
      Ends{1n+made, Whole{ws}}
    case False{} False{}:
      Ends{1n+made, end.of(best, input)}
    case False{} True{}:
      match p:
        case 0n:
          Ends{1n+made, CutReply{ws}}
        case 1n+q:
          Asks{Lst{1n+q, 1n+made, node, Some{ws}, len, input}}

# one reply of a line with tries left
def line.step(st: Lst, r: Reply) -> Next:
  match st:
    case Lst{left, made, +node, best, +bl, input}:
      match left:
        case 0n:
          Ends{made, end.of(best, input)}
        case 1n+p:
          match r:
            case Erred{}:
              Ends{1n+made, Lost{}}
            case Says{ws}:
              match ws:
                case Nil{}:
                  Ends{1n+made, end.of(best, input)}
                case +w <> +t:
                  +len = Text.len(w <> t)
                  +b = best
                  line.says(Nat.is_le(len, node), shorter(len, b, bl), p, made, node, b, input, w <> t, len)

# a line starts: with no tries, it is the input cut
def line.open(+tries: Nat, node: Nat, input: List<&2, W>) -> Next:
  line.again(tries, Lst{tries, 0n, node, None{}, 0n, input})

# the steps over the replies, in order (a missing reply fails the call)
def line.drive(rs: List<&2, Reply>, n: Next, +node: Nat) -> Line:
  match rs n:
    case _ Ends{c, e}:
      Line{c, Fin.line(node, e)}
    case Nil{} Asks{st}:
      Line{1n+Lst.made(st), None{}}
    case r <> rest Asks{st}:
      line.drive(rest, line.step(st, r), node)

# the first n replies: the ones a line of n calls read
def read(n: Nat, rs: List<&2, Reply>) -> List<&2, Reply>:
  match n rs:
    case 0n _:
      Nil{}
    case 1n+p Nil{}:
      Nil{}
    case 1n+p r <> rest:
      r <> read(p, rest)

def first_fit.pick(fit: Bool, ws: List<&2, W>, rec: Maybe<&2, List<&2, W>>) -> Maybe<&2, List<&2, W>>:
  match fit:
    case True{}:
      Some{ws}
    case False{}:
      rec

# the first reply of rs that fits: not empty, at most node bytes
def first_fit(+node: Nat, rs: List<&2, Reply>) -> Maybe<&2, List<&2, W>>:
  match rs:
    case Nil{}:
      None{}
    case r <> rest:
      match r:
        case Erred{}:
          first_fit(node, rest)
        case Says{ws}:
          match ws:
            case Nil{}:
              first_fit(node, rest)
            case +w <> +t:
              first_fit.pick(Nat.is_le(Text.len(w <> t), node), w <> t, first_fit(node, rest))

# the line is the first fitting reply the call read, when there is one
def line.first(want: Maybe<&2, List<&2, W>>, got: Maybe<&2, List<&2, W>>) -> Bool:
  match want got:
    case None{} _:
      True{}
    case Some{f} None{}:
      False{}
    case Some{f} Some{g}:
      Text.eq(f, g)

# a line of 1 to node bytes, or a failed call
def line.fits(+node: Nat, m: Maybe<&2, List<&2, W>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+t}:
      Bool.and(O.Nat.is_pos(Text.len(t)), Nat.is_le(Text.len(t), node))

# The settle (H2)
# ---------------

# A view line: built, or pending with n failures left before the failure
# cap builds it from its input.
type Pend is Data:
  Made{}
  Owed{n: Nat}

# how a call of a pending line ends: its line is saved; the call failed
# (a provider error, or past its deadline; at the cap the input cut is
# saved then); the disk failed (the line's input could not be read, its
# line or the input cut not saved); a waiting turn stopped it (H2.1)
type Outcome is Data:
  Built{}
  Failed{}
  Disk{}
  Stopped{}

# a saved line builds the line, and so does the failure with no failures
# left (the cap); any other failure counts down; the disk and a stop
# change nothing
def Owed.after(o: Outcome, n: Nat) -> Pend:
  match o:
    case Built{}:
      Made{}
    case Failed{}:
      match n:
        case 0n:
          Made{}
        case 1n+m:
          Owed{m}
    case Disk{}:
      Owed{n}
    case Stopped{}:
      Owed{n}

def Pend.after(p: Pend, o: Outcome) -> Pend:
  match p:
    case Made{}:
      Made{}
    case Owed{n}:
      Owed.after(o, n)

# the outcome counts: a line is saved, or the call failed
def Outcome.lands(o: Outcome) -> Bool:
  match o:
    case Built{}:
      True{}
    case Failed{}:
      True{}
    case Disk{}:
      False{}
    case Stopped{}:
      False{}

# the measure: per pending line, its failures left plus one
def Pend.weight(p: Pend) -> Nat:
  match p:
    case Made{}:
      0n
    case Owed{n}:
      1n+n

def measure(ps: List<&2, Pend>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case p <> rest:
      Nat.add(Pend.weight(p), measure(rest))

def Pend.done(p: Pend) -> Bool:
  match p:
    case Made{}:
      True{}
    case Owed{n}:
      False{}

def settled(ps: List<&2, Pend>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case p <> rest:
      Bool.and(Pend.done(p), settled(rest))

def Pend.pending(p: Pend) -> Bool:
  Bool.not(Pend.done(p))

# line k is pending
def pending_at(ps: List<&2, Pend>, k: Nat) -> Bool:
  match ps k:
    case Nil{} _:
      False{}
    case p <> rest 0n:
      Pend.pending(p)
    case p <> rest 1n+j:
      pending_at(rest, j)

# a call of view line k ends with o; a call of no pending line (a built
# line, a merge outside the view, a stale call) changes no line
def hit(ps: List<&2, Pend>, k: Nat, o: Outcome) -> List<&2, Pend>:
  match ps k:
    case Nil{} _:
      Nil{}
    case p <> rest 0n:
      Pend.after(p, o) <> rest
    case p <> rest 1n+j:
      p <> hit(rest, j, o)

# a call of view line k ended with o
type End is Data:
  End{k: Nat, o: Outcome}

# the calls' outcomes, in the order they end
def run(es: List<&2, End>, ps: List<&2, Pend>) -> List<&2, Pend>:
  match es:
    case Nil{}:
      ps
    case End{k, o} <> rest:
      run(rest, hit(ps, k, o))

# how many of them counted (a saved line, a failed call) for a pending line
def hits(es: List<&2, End>, +ps: List<&2, Pend>) -> Nat:
  match es:
    case Nil{}:
      0n
    case End{+k, +o} <> rest:
      Nat.add(O.bit(Bool.and(pending_at(ps, k), Outcome.lands(o)), 0n), hits(rest, hit(ps, k, o)))

# a line after the outcomes of its calls, in order
def Pend.run(os: List<&2, Outcome>, p: Pend) -> Pend:
  match os:
    case Nil{}:
      p
    case o <> rest:
      Pend.run(rest, Pend.after(p, o))

# how many of them are failed calls
def failures(os: List<&2, Outcome>) -> Nat:
  match os:
    case Nil{}:
      0n
    case o <> rest:
      match o:
        case Built{}:
          failures(rest)
        case Failed{}:
          1n+failures(rest)
        case Disk{}:
          failures(rest)
        case Stopped{}:
          failures(rest)

# the view's lines when a turn starts to wait, cap = 1+p failures each
def settle.line(built: Bool, +p: Nat) -> Pend:
  match built:
    case True{}:
      Made{}
    case False{}:
      Owed{p}

def settle.start(+p: Nat, +info: O.Info, v: List<&2, O.Node>) -> List<&2, Pend>:
  match v:
    case Nil{}:
      Nil{}
    case h <> rest:
      settle.line(O.Info.built(info, h), p) <> settle.start(p, info, rest)

# the view's lines not built
def unbuilt(+info: O.Info, v: List<&2, O.Node>) -> Nat:
  match v:
    case Nil{}:
      0n
    case h <> rest:
      Nat.add(O.bit(Bool.not(O.Info.built(info, h)), 0n), unbuilt(info, rest))

# Need first (H2.1)
# -----------------

# every node of ns is a line of v that is not built
def needed(+info: O.Info, +v: List<&2, O.Node>, ns: List<&2, O.Node>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case +n <> rest:
      Bool.and(Bool.and(O.Nodes.has(v, n), Bool.not(O.Info.built(info, n))), needed(info, v, rest))

# every node of bs that is a line of v not built is in ws: a stop that
# leaves ws running spared every call the view needs
def kept(+info: O.Info, +v: List<&2, O.Node>, bs: List<&2, O.Node>, +ws: List<&2, O.Node>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case +b <> rest:
      Bool.and(O.Bool.implies(Bool.and(O.Nodes.has(v, b), Bool.not(O.Info.built(info, b))), O.Nodes.has(ws, b)), kept(info, v, rest, ws))

# some line of v is neither built nor busy: a line the turn needs that no
# call builds
def idle(+info: O.Info, v: List<&2, O.Node>, +busy: List<&2, O.Node>) -> Bool:
  match v:
    case Nil{}:
      False{}
    case +h <> rest:
      Bool.or(Bool.and(Bool.not(O.Info.built(info, h)), Bool.not(O.Nodes.has(busy, h))), idle(info, rest, busy))
