# eukhe: the laws of area doc_glob
#
# Requirements (section F11 of the documents laws: glob's ranking and
# pages; bend/doc_glob.bend, bend/ffi_doc_glob.bend; Rust
# crates/eukhe-docs/src/glob.rs):
# R1 a glob ranks the matched paths newest first, then by path (char by
#    char, by code point; a path before its extensions), each path once at
#    its newest time; its page, continuation and past-the-end count are
#    the section header's below; the entry asks for a path whole only when
#    it can still be on the page or tell that more follow, keeping at most
#    S + K + 1 paths (bounded memory).
# R2 an open that is not exactly a spelled skip and limit (0, or 1 then
#    the limit) that fit the wire answers "doc_glob: malformed open", and
#    every text after it answers "doc_glob: the open was refused": no page
#    ever follows a refused open.
# R3 in an open glob, a text that is not exactly one spelled event (a
#    path's time, a path whole, the page) that fits the wire answers
#    "doc_glob: malformed event" and changes nothing.
# R4 the entry answers every walk Rust feeds it, and any events in any
#    order, that fit the wire, with the replies of R1.
# Coverage: R1, R4 glob_walk_runs, glob_events_answer; R2
# glob_open_malformed_unless_open, glob_refused_open_stays_refused; R3
# glob_step_malformed_unless_event, glob_step_malformed_keeps. Anchors
# (no coverage): glob_walk_example, glob_refuses_example; witness:
# glob_fits_example.

import Base
import ../bend/doc_glob.bend as Gb
import ../bend/ffi_doc_glob.bend as FGb
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (F11) Glob's ranking and pages
# ------------------------------
# bend/doc_glob.bend, bend/ffi_doc_glob.bend. Rust walks the targets,
# reads each matched path's change time and spells its display path; the
# entry decides the rest. Every input is free: any skip, any limit (none
# or any number), any walk (any times, any paths, in any order, a path met
# any number of times at any times), any order of events, any request
# text.
# A glob ranks the matched paths newest first, then by path (char by
# char, by code point; a path before its extensions), each path once at
# its newest time. Its page is the K ranked paths after the first S, K the
# limit but at most 200 (200 with no limit); the continuation is S + K
# when K is not 0 and a ranked path follows the page; the past-the-end
# notice gives the number of ranked paths when there is one and S is at
# or past it. The entry asks for a path whole only when it can still be
# on the page or tell that more follow: not when it keeps S + K + 1 paths
# and every one is newer.
# NOT PINNED here: which paths match, their display spelling and times
# (the walk), the deadline, the notice wording, the rendering.

# a matched path: changed at m (ms since the epoch), shown as p
type glob.Hit is Data:
  glob.Hit{m: Nat, p: String}

def glob.If(-A: Data, b: Bool, x: A, y: A) -> A:
  match b:
    case True{}:
      x
    case False{}:
      y

def glob.When(b: Bool, v: Nat) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{v}
    case False{}:
      None{}

# Ranking
# -------

def glob.code(c: Char) -> Nat:
  match c:
    case Chr{x}:
      U32.to_nat(x)

# a comes before b: char by char, by code point; a proper prefix first
def glob.Lt(a: String, b: String) -> Bool:
  match a b:
    case SNil{} SNil{}:
      False{}
    case SNil{} SCon{y, u}:
      True{}
    case SCon{x, t} SNil{}:
      False{}
    case SCon{+x, t} SCon{+y, u}:
      Bool.or(Nat.is_lt(glob.code(x), glob.code(y)), Bool.and(Nat.is_eq(glob.code(x), glob.code(y)), glob.Lt(t, u)))

# a and b are one path: the same chars
def glob.Eq(a: String, b: String) -> Bool:
  match a b:
    case SNil{} SNil{}:
      True{}
    case SNil{} SCon{y, u}:
      False{}
    case SCon{x, t} SNil{}:
      False{}
    case SCon{x, t} SCon{y, u}:
      Bool.and(Nat.is_eq(glob.code(x), glob.code(y)), glob.Eq(t, u))

# x ranks before y: newer, or as new and its path first
def glob.Before(x: glob.Hit, y: glob.Hit) -> Bool:
  match x y:
    case glob.Hit{+a, p} glob.Hit{+b, q}:
      Bool.or(Nat.is_gt(a, b), Bool.and(Nat.is_eq(a, b), glob.Lt(p, q)))

# x and y are hits of one path
def glob.Same(x: glob.Hit, y: glob.Hit) -> Bool:
  match x y:
    case glob.Hit{a, p} glob.Hit{b, q}:
      glob.Eq(p, q)

# ys without its first hit of x's path
def glob.Unsame(+x: glob.Hit, ys: List<&2, glob.Hit>) -> List<&2, glob.Hit>:
  match ys:
    case Nil{}:
      Nil{}
    case +y <> +t:
      glob.If(List<&2, glob.Hit>, glob.Same(x, y), t, y <> glob.Unsame(x, t))

# x put into the ranked hits ys: before the first hit it ranks before,
# where the older hit of its path (if any) leaves; dropped when a hit of
# its path ranks at least as high
def glob.Put(+x: glob.Hit, ys: List<&2, glob.Hit>) -> List<&2, glob.Hit>:
  match ys:
    case Nil{}:
      [x]
    case +y <> +t:
      glob.If(List<&2, glob.Hit>, glob.Before(x, y), x <> glob.Unsame(x, y <> t), glob.If(List<&2, glob.Hit>, glob.Same(x, y), y <> t, y <> glob.Put(x, t)))

# the ranked hits after the walk ws, met after the ranked hits rs: each
# path once, newest first, then by path
def glob.Ranked(ws: List<&2, glob.Hit>, rs: List<&2, glob.Hit>) -> List<&2, glob.Hit>:
  match ws:
    case Nil{}:
      rs
    case +w <> t:
      glob.Ranked(t, glob.Put(w, rs))

# Pages
# -----

# the first c hits of rs
def glob.First(rs: List<&2, glob.Hit>, c: Nat) -> List<&2, glob.Hit>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match c:
        case 0n:
          Nil{}
        case 1n+d:
          r <> glob.First(t, d)

# rs after its first s hits
def glob.Drop(rs: List<&2, glob.Hit>, s: Nat) -> List<&2, glob.Hit>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match s:
        case 0n:
          r <> t
        case 1n+j:
          glob.Drop(t, j)

def glob.Len(rs: List<&2, glob.Hit>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case r <> t:
      1n+glob.Len(t)

# the oldest time of the hits t and of one changed at m
def glob.Low.go(t: List<&2, glob.Hit>, +m: Nat) -> Nat:
  match t:
    case Nil{}:
      m
    case y <> u:
      match y:
        case glob.Hit{a, q}:
          Nat.min(m, glob.Low.go(u, a))

# the oldest time of the hits rs (0 for none)
def glob.Low(rs: List<&2, glob.Hit>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case y <> t:
      match y:
        case glob.Hit{a, q}:
          glob.Low.go(t, a)

# the page size: the limit, at most 200; 200 with no limit
def glob.Size(lim: Maybe<&2, Nat>) -> Nat:
  match lim:
    case None{}:
      200n
    case Some{l}:
      Nat.min(l, 200n)

# the k ranked hits after the first s
def glob.Window(rs: List<&2, glob.Hit>, s: Nat, k: Nat) -> List<&2, glob.Hit>:
  glob.First(glob.Drop(rs, s), k)

# the continuation of the page (s, k) of n ranked hits: s + k when k is
# not 0 and a hit follows the page
def glob.More(+n: Nat, +s: Nat, +k: Nat) -> Maybe<&2, Nat>:
  glob.When(Bool.and(Nat.is_lt(0n, k), Nat.is_lt(Nat.add(s, k), n)), Nat.add(s, k))

# the past-the-end count: n when there is a ranked hit and the skip s is
# at or past n
def glob.Past(+n: Nat, +s: Nat) -> Maybe<&2, Nat>:
  glob.When(Bool.and(Nat.is_le(n, s), Nat.is_lt(0n, n)), n)

# the entry wants the hit x whole after the ranked hits rs, keeping c:
# unless it keeps c hits and every one is newer than x
def glob.Wants(x: glob.Hit, +c: Nat, +rs: List<&2, glob.Hit>) -> Bool:
  match x:
    case glob.Hit{m, p}:
      Bool.not(Bool.and(Nat.is_le(c, glob.Len(glob.First(rs, c))), Nat.is_lt(m, glob.Low(glob.First(rs, c)))))

# Spellings
# ---------

def glob.spell_opt(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{v}:
      Wr.put_nat(1n, Wr.put_nat(v, rest))

def glob.spell_hit(h: glob.Hit, rest: String) -> String:
  match h:
    case glob.Hit{m, p}:
      Wr.put_nat(m, Wr.put_str(p, rest))

# the open: the skip, then the limit (a Maybe<Nat>)
def glob.spell_open(s: Nat, lim: Maybe<&2, Nat>) -> String:
  Wr.put_nat(s, glob.spell_opt(lim, ""))

# the events: a hit's time (0); a hit whole (1); the page (2)
def glob.spell_met(h: glob.Hit) -> String:
  match h:
    case glob.Hit{m, p}:
      Wr.put_nat(0n, Wr.put_nat(m, ""))

def glob.spell_add(h: glob.Hit) -> String:
  Wr.put_nat(1n, glob.spell_hit(h, ""))

def glob.spell_show() -> String:
  Wr.put_nat(2n, "")

# the reply to the page of the ranked hits rs: the continuation, the
# past-the-end count, the page's hits
def glob.spell_page(+rs: List<&2, glob.Hit>, +s: Nat, +k: Nat) -> String:
  glob.spell_opt(glob.More(glob.Len(rs), s, k), glob.spell_opt(glob.Past(glob.Len(rs), s), Wr.put_list(~glob.Hit, ~glob.spell_hit, glob.Window(rs, s, k), "")))

# every number of the hits fits the wire: each time and path length
def glob.HitsFit(ws: List<&2, glob.Hit>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case w <> t:
      match w:
        case glob.Hit{+m, +p}:
          Bool.and(Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(String.length(p))), glob.HitsFit(t))

def glob.Fits(+s: Nat, lim: Maybe<&2, Nat>, ws: List<&2, glob.Hit>) -> Bool:
  Bool.and(LawsBase.wire_fits(s), Bool.and(LawsBase.core_mfits(lim), glob.HitsFit(ws)))

# The entry
# ---------

def glob.Fst(r: FGb.St & String) -> FGb.St:
  match r:
    case (st, out):
      st

def glob.Snd(r: FGb.St & String) -> String:
  match r:
    case (st, out):
      out

# the open's state and reply for the page (s, lim)
def glob.Open(+s: Nat, +lim: Maybe<&2, Nat>) -> FGb.St & String:
  FGb.open(glob.spell_open(s, lim))

# a reply is exactly T
def glob.Yes.of(d: Wr.Dec<Bool>) -> Bool:
  match d:
    case Wr.Got{b, rest}:
      Bool.and(b, String.is_empty(rest))
    case Wr.Bad{}:
      False{}

def glob.Yes(reply: String) -> Bool:
  glob.Yes.of(Wr.get_bool(reply))

# Rust's side of a walk: each hit's time, then the hit whole when the
# entry answers T; then the page. The entry's replies, in order
def glob.Drive(ws: List<&2, glob.Hit>, +st: FGb.St) -> List<&2, String>:
  match ws:
    case Nil{}:
      [glob.Snd(FGb.step(st, glob.spell_show()))]
    case +w <> t:
      +said = glob.Snd(FGb.step(st, glob.spell_met(w)))
      +met = glob.Fst(FGb.step(st, glob.spell_met(w)))
      +y = glob.Yes(said)
      List.append(&2, String, glob.If(List<&2, String>, y, [said, glob.Snd(FGb.step(met, glob.spell_add(w)))], [said]), glob.Drive(t, glob.If(FGb.St, y, glob.Fst(FGb.step(met, glob.spell_add(w))), met)))

# the spec's replies to a walk after the ranked hits rs, page (s, k),
# keeping c: per hit T and the empty reply to the hit whole when wanted,
# else F; then the page of every hit met
def glob.Trace(ws: List<&2, glob.Hit>, +s: Nat, +k: Nat, +c: Nat, +rs: List<&2, glob.Hit>) -> List<&2, String>:
  match ws:
    case Nil{}:
      [glob.spell_page(rs, s, k)]
    case +w <> t:
      +y = glob.Wants(w, c, rs)
      List.append(&2, String, glob.If(List<&2, String>, y, [Wr.put_bool(True{}, ""), ""], [Wr.put_bool(False{}, "")]), glob.Trace(t, s, k, c, glob.Put(w, rs)))

# LAW glob_walk_runs (R1, R4): a glob that Rust feeds a walk (open with skip s and
# limit lim; per matched path its time, and the path whole when the entry
# answers T; then the page) gets the empty reply to the open, T or F per
# path as the spec decides (F only when the S + K + 1 hits kept are all
# newer), the empty reply to each path sent whole, and the page of every
# path met, ranked newest first then by path, each path once at its
# newest time: the continuation, the past-the-end count and the K paths
# after the first S with their times, K = min(lim, 200), 200 with no limit
# EXCLUDES: a page that loses a path the entry said F to although it
# ranks on the page; another order (oldest first, ties by a later path,
# by bytes of another encoding); a path twice, or at an older time; a
# continuation or past-the-end notice off by one or of another count; a
# page size not capped at 200 or not 200 without a limit; memory that
# grows with the walk (T to every path is allowed by no law but this one)
law glob_walk_runs:
  for +s: Nat
  for +lim: Maybe<&2, Nat>
  for +ws: List<&2, glob.Hit>
  for +h: {glob.Fits(s, lim, ws) == True{} : Bool}
  {glob.Snd(glob.Open(s, lim)) <> glob.Drive(ws, glob.Fst(glob.Open(s, lim))) == "" <> glob.Trace(ws, s, glob.Size(lim), 1n+Nat.add(s, glob.Size(lim)), Nil{}) : List<&2, String>}

# an event of the glob stepper, in any order: a hit's time, a hit whole,
# the page
type glob.Ev is Data:
  glob.EMet{h: glob.Hit}
  glob.EAdd{h: glob.Hit}
  glob.EShow{}

def glob.spell_ev(e: glob.Ev) -> String:
  match e:
    case glob.EMet{h}:
      glob.spell_met(h)
    case glob.EAdd{h}:
      glob.spell_add(h)
    case glob.EShow{}:
      glob.spell_show()

def glob.EvsFit(es: List<&2, glob.Ev>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> t:
      match e:
        case glob.EMet{h}:
          Bool.and(glob.HitsFit([h]), glob.EvsFit(t))
        case glob.EAdd{h}:
          Bool.and(glob.HitsFit([h]), glob.EvsFit(t))
        case glob.EShow{}:
          glob.EvsFit(t)

# the stepper's replies to the events es from st
def glob.Steps(es: List<&2, glob.Ev>, +st: FGb.St) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      glob.Snd(FGb.step(st, glob.spell_ev(e))) <> glob.Steps(t, glob.Fst(FGb.step(st, glob.spell_ev(e))))

# the spec's replies to the events es after the ranked hits rs sent
# whole: T or F to a time, empty to a hit whole, the page of the hits
# sent whole
def glob.Answers(es: List<&2, glob.Ev>, +s: Nat, +k: Nat, +c: Nat, +rs: List<&2, glob.Hit>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case e <> t:
      match e:
        case glob.EMet{h}:
          Wr.put_bool(glob.Wants(h, c, rs), "") <> glob.Answers(t, s, k, c, rs)
        case glob.EAdd{h}:
          "" <> glob.Answers(t, s, k, c, glob.Put(h, rs))
        case glob.EShow{}:
          glob.spell_page(rs, s, k) <> glob.Answers(t, s, k, c, rs)

# LAW glob_events_answer (R1, R4): after an open, any events in any order that fit
# the wire get the spec's replies: a time T or F as the spec decides over
# the paths sent whole so far, the empty reply to a path whole, the page
# of the paths sent whole (each event counts, in order)
# EXCLUDES: a stepper that drifts from the spec on an order Rust does not
# use (a page asked twice or mid-walk, a path sent whole after F, a path
# sent whole twice)
law glob_events_answer:
  for +s: Nat
  for +lim: Maybe<&2, Nat>
  for +es: List<&2, glob.Ev>
  for +h: {Bool.and(Bool.and(LawsBase.wire_fits(s), LawsBase.core_mfits(lim)), glob.EvsFit(es)) == True{} : Bool}
  {glob.Snd(glob.Open(s, lim)) <> glob.Steps(es, glob.Fst(glob.Open(s, lim))) == "" <> glob.Answers(es, s, glob.Size(lim), 1n+Nat.add(s, glob.Size(lim)), Nil{}) : List<&2, String>}

# the replies to the texts xs from the state and reply of r
def glob.Texts(xs: List<&2, String>, r: FGb.St & String) -> List<&2, String>:
  match xs:
    case Nil{}:
      [glob.Snd(r)]
    case x <> t:
      match r:
        case (st, out):
          out <> glob.Texts(t, FGb.step(st, x))

# The refusals
# ------------

# the n copies of the reply t
def glob.Rep(n: Nat, +t: String) -> List<&2, String>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      t <> glob.Rep(m, t)

# LAW glob_open_malformed_unless_open (R2): every open text the entry
# answers with anything but the error form "doc_glob: malformed open" is
# the spelling of a skip and a limit (0, or 1 then the limit) that fit the
# wire, with nothing after it
# EXCLUDES: an open with a limit tag of 2 or more, a cut limit, input left
#   over, or no skip, read as some page (a default skip or limit) or
#   answered with another error text
law glob_open_malformed_unless_open:
  for +x: String
  for other: {String.eq(glob.Snd(FGb.open(x)), Wr.err("doc_glob: malformed open")) == False{} : Bool}
  exs s: Nat
  exs lim: Maybe<&2, Nat>
  {x == glob.spell_open(s, lim) : String} & {Bool.and(LawsBase.wire_fits(s), LawsBase.core_mfits(lim)) == True{} : Bool}

# LAW glob_refused_open_stays_refused (R2): after an open the entry
# answers with "doc_glob: malformed open", it answers every later text,
# whatever and however many, with "doc_glob: the open was refused"
# EXCLUDES: a refused open that still keeps paths, or answers a page (of a
#   default skip and limit), T or F, or the empty reply; another error
#   text
law glob_refused_open_stays_refused:
  for +x: String
  for +ts: List<&2, String>
  for refused: {String.eq(glob.Snd(FGb.open(x)), Wr.err("doc_glob: malformed open")) == True{} : Bool}
  {glob.Texts(ts, FGb.open(x)) == Wr.err("doc_glob: malformed open") <> glob.Rep(List.length(&2, String, ts), Wr.err("doc_glob: the open was refused")) : List<&2, String>}

# LAW glob_step_malformed_unless_event (R3): in any open glob (any page,
# any paths kept), every text the entry answers with anything but the
# error form "doc_glob: malformed event" is the spelling of one event (a
# path's time, a path whole, the page) whose numbers fit the wire, with
# nothing after it
# EXCLUDES: an unknown tag, a cut time or path, or input left over, read
#   as some event (a guessed time, path or page) or answered with another
#   error text
law glob_step_malformed_unless_event:
  for +s: Nat
  for +k: Nat
  for +c: Nat
  for +len: Nat
  for +low: Nat
  for +xs: List<&2, Gb.It>
  for +x: String
  for other: {String.eq(glob.Snd(FGb.step(FGb.Gl{s, k, c, len, low, xs}, x)), Wr.err("doc_glob: malformed event")) == False{} : Bool}
  exs e: glob.Ev
  {x == glob.spell_ev(e) : String} & {glob.EvsFit([e]) == True{} : Bool}

# LAW glob_step_malformed_keeps (R3): in any open glob, a text the entry
# answers with "doc_glob: malformed event" changes nothing: the glob after
# it is the glob before it
# EXCLUDES: a malformed event that still keeps a path, moves the page or
#   the oldest time kept, or forgets paths
law glob_step_malformed_keeps:
  for +s: Nat
  for +k: Nat
  for +c: Nat
  for +len: Nat
  for +low: Nat
  for +xs: List<&2, Gb.It>
  for +x: String
  for bad: {String.eq(glob.Snd(FGb.step(FGb.Gl{s, k, c, len, low, xs}, x)), Wr.err("doc_glob: malformed event")) == True{} : Bool}
  {glob.Fst(FGb.step(FGb.Gl{s, k, c, len, low, xs}, x)) == FGb.Gl{s, k, c, len, low, xs} : FGb.St}

# LAW glob_walk_example (anchor): the texts Rust writes: an open of skip
# 1 and limit 1; b, a (both at 5), c (at 9), b again (at 5) are sent
# whole, old (at 1) is not wanted; the page is a (at 5), with the
# continuation 2
# EXCLUDES: a codec Rust's text would misread, another tie order
law glob_walk_example:
  {glob.Texts(["0,5,", "1,5,1,b", "0,5,", "1,5,1,a", "0,9,", "1,9,1,c", "0,5,", "1,5,1,b", "0,1,", "2,"], FGb.open("1,1,1,")) == ["", "T", "", "T", "", "T", "", "T", "", "F", "1,2,0,1,5,1,a"] : List<&2, String>}

# LAW glob_refuses_example (anchor): a limit tag of 2, an open with input
# left over, a path shorter than its length, an unknown tag are refused
# EXCLUDES: a codec that accepts what Rust never writes
law glob_refuses_example:
  {FGb.open("1,2,") == (FGb.Shut{}, Wr.err("doc_glob: malformed open")) : FGb.St & String} & {FGb.open("1,0,x") == (FGb.Shut{}, Wr.err("doc_glob: malformed open")) : FGb.St & String} & {glob.Texts(["1,5,2,a", "3,", "2,"], FGb.open("0,0,")) == ["", Wr.err("doc_glob: malformed event"), Wr.err("doc_glob: malformed event"), "0,0,0,"] : List<&2, String>}

# LAW glob_fits_example (witness): a walk of the example fits the wire
# (glob_walk_runs is not vacuous)
law glob_fits_example:
  {glob.Fits(1n, Some{1n}, [glob.Hit{5n, "b"}, glob.Hit{9n, "c"}]) == True{} : Bool}
