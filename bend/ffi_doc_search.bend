# ffi_doc_search: the entry of the compiled Bend core for grep
# (crates/eukhe-docs/src/grep/mod.rs), over
# the rules of bend/doc_search.bend. Every request and every reply is one
# list of Nats of the wire (bend/wire.bend: its count, then its items); a
# Bool is 0 (false) or 1 (true), a Maybe<Nat> is 0 (none) or 1 + its
# value.
#
# The calls (`ffi`):
#   page    [0, t, s, k, multi]      grep: the page of t matching files
#     reply [next, past, i ...]      the files on the page (walk order)
#   limit   [1, l, c ...]            the match limit l over the page's
#                                    files with c matches each
#     reply [cut, kept ...]          what each file keeps
#   scope   [2, roots, dirs, skip, lim]  grep's scope: the path's roots,
#                                    how many are directories, the skip
#                                    and the match limit asked (Maybe)
#     reply [multi, p, s, k]         several files; matches a file keeps;
#                                    the page (S, K)
#
# The stepper of grep's walk (`open`, `step`), one file at a time:
#   open    [p, s, k, rem, t, maxb]  P matches a file at most, the page
#                                    (S, K), REM matches in all, t files,
#                                    MAXB bytes searched of a file
#     reply empty
#   ask     [0, (start, stop) ...]   the next file, its line ranges (stop:
#                                    0 open, 1 + its end line)
#     reply [0, t] | [1, fetch]      stop: the t files left are not
#                                    searched | search it, fetch matches
#   opened  [1, h, big]              the file holds h matches (in the part
#                                    searched; big: over MAXB)
#   skipped [2, why]                 0 binary, 1 unreadable, 2 excluded,
#                                    3 symlink, 4 walk error
#     reply [class, cut, partial, kept]   class: 0 no match, 1 shown (its
#                                    bytes are kept for the page), 2 paged
#                                    out, 3 not searched, 4 + why skipped
#
# A malformed input (one that is not the list of a request, has input
# left over, or a list of another shape) answers the wire's error form; a
# step keeps the walk then, and a malformed open opens the refused state,
# which answers every step with the error form. laws/doc_search.bend pins
# the entry.

import Base
import ./wire.bend as W
import ./doc_search.bend as M

# Values as Nats
# --------------

def bitn(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def maybn(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{v}:
      1n+v

def why.n(r: M.Reason) -> Nat:
  match r:
    case M.Binary{}:
      0n
    case M.Unreadable{}:
      1n
    case M.Excluded{}:
      2n
    case M.Link{}:
      3n
    case M.Broken{}:
      4n

def cls.n(c: M.Class) -> Nat:
  match c:
    case M.NoMatch{}:
      0n
    case M.Shown{}:
      1n
    case M.PagedOut{}:
      2n
    case M.Unsearched{}:
      3n
    case M.Skipped{w}:
      Nat.add(4n, why.n(w))

# Nats as values
# --------------

def bit(n: Nat) -> Maybe<&2, Bool>:
  match n:
    case 0n:
      Some{False{}}
    case 1n+m:
      match m:
        case 0n:
          Some{True{}}
        case 1n+x:
          None{}

def why(n: Nat) -> Maybe<&2, M.Reason>:
  match n:
    case 0n:
      Some{M.Binary{}}
    case 1n:
      Some{M.Unreadable{}}
    case 2n:
      Some{M.Excluded{}}
    case 3n:
      Some{M.Link{}}
    case 4n:
      Some{M.Broken{}}
    case 5n+x:
      None{}

def stop(n: Nat) -> Maybe<&2, Nat>:
  match n:
    case 0n:
      None{}
    case 1n+e:
      Some{e}

def ranges.cons(a: M.Range, r: Maybe<&2, List<&2, M.Range>>) -> Maybe<&2, List<&2, M.Range>>:
  match r:
    case None{}:
      None{}
    case Some{t}:
      Some{a <> t}

# the ranges of start, stop pairs
def ranges(xs: List<&2, Nat>) -> Maybe<&2, List<&2, M.Range>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case a <> t:
      match t:
        case Nil{}:
          None{}
        case z <> u:
          ranges.cons(M.Range{a, stop(z)}, ranges(u))

# The calls
# ---------

type Req is Data:
  PageQ{t: Nat, s: Nat, k: Nat, multi: Bool}
  LimitQ{l: Nat, cs: List<&2, Nat>}
  ScopeQ{roots: Nat, dirs: Nat, skip: Nat, lim: Maybe<&2, Nat>}

def req.page(+t: Nat, +s: Nat, +k: Nat, b: Maybe<&2, Bool>) -> Maybe<&2, Req>:
  match b:
    case None{}:
      None{}
    case Some{m}:
      Some{PageQ{t, s, k, m}}

def req.p(xs: List<&2, Nat>) -> Maybe<&2, Req>:
  match xs:
    case Nil{}:
      None{}
    case t <> a:
      match a:
        case Nil{}:
          None{}
        case s <> b:
          match b:
            case Nil{}:
              None{}
            case k <> c:
              match c:
                case Nil{}:
                  None{}
                case m <> d:
                  match d:
                    case Nil{}:
                      req.page(t, s, k, bit(m))
                    case x <> e:
                      None{}

def req.l(xs: List<&2, Nat>) -> Maybe<&2, Req>:
  match xs:
    case Nil{}:
      None{}
    case l <> cs:
      Some{LimitQ{l, cs}}

def req.c(xs: List<&2, Nat>) -> Maybe<&2, Req>:
  match xs:
    case Nil{}:
      None{}
    case r <> a:
      match a:
        case Nil{}:
          None{}
        case d <> b:
          match b:
            case Nil{}:
              None{}
            case s <> c:
              match c:
                case Nil{}:
                  None{}
                case l <> e:
                  match e:
                    case Nil{}:
                      Some{ScopeQ{r, d, s, stop(l)}}
                    case x <> f:
                      None{}

# the request a list spells
def req(xs: List<&2, Nat>) -> Maybe<&2, Req>:
  match xs:
    case Nil{}:
      None{}
    case tag <> t:
      match tag:
        case 0n:
          req.p(t)
        case 1n:
          req.l(t)
        case 2n:
          req.c(t)
        case 3n+x:
          None{}

def answer.page(+ps: List<&2, Nat>, +s: Nat, +k: Nat, +multi: Bool) -> List<&2, Nat>:
  maybn(M.grep.next(multi, ps, s, k)) <> bitn(M.grep.past(multi, ps, s)) <> M.page(ps, s, k)

def answer.scope(sc: M.Scope) -> List<&2, Nat>:
  match sc:
    case M.Scope{m, p, s, k}:
      [bitn(m), p, s, k]

# the answer of a call, as its list
def answer(q: Req) -> List<&2, Nat>:
  match q:
    case PageQ{t, s, k, m}:
      answer.page(M.upto(t), s, k, m)
    case LimitQ{+l, +cs}:
      bitn(M.rr.cut(cs, l)) <> M.rr(cs, l)
    case ScopeQ{r, d, s, l}:
      answer.scope(M.scope(r, d, s, l))

def ffi.ask(q: Maybe<&2, Req>) -> String:
  match q:
    case None{}:
      W.err("doc_search: malformed request")
    case Some{r}:
      W.put_list(~Nat, ~W.put_nat, answer(r), "")

def ffi.end(done: Bool, xs: List<&2, Nat>) -> String:
  match done:
    case True{}:
      ffi.ask(req(xs))
    case False{}:
      W.err("doc_search: malformed request")

def ffi.got(r: W.Dec<List<&2, Nat>>) -> String:
  match r:
    case W.Got{xs, rest}:
      ffi.end(W.end(rest), xs)
    case W.Bad{}:
      W.err("doc_search: malformed request")

# ffi: one call (a page, the match limit, a glob)
def ffi(input: String) -> String:
  ffi.got(W.get_list(~Nat, ~W.get_nat, input))

# The walk of grep
# ----------------

# a walk: P matches a file at most, the page (S, K), REM matches left, N
# matching files so far, T files not met yet, MAXB bytes searched of a
# file; or a refused open
type St is Data:
  Walk{p: Nat, s: Nat, k: Nat, rem: Nat, n: Nat, t: Nat, maxb: Nat}
  Shut{}

# an event of the walk: the next file is asked for, with its line ranges;
# or what the file met held
type Ev is Data:
  Ask{rs: List<&2, M.Range>}
  Met{f: M.Form}

def ev.ask(r: Maybe<&2, List<&2, M.Range>>) -> Maybe<&2, Ev>:
  match r:
    case None{}:
      None{}
    case Some{rs}:
      Some{Ask{rs}}

def ev.opened(+h: Nat, b: Maybe<&2, Bool>) -> Maybe<&2, Ev>:
  match b:
    case None{}:
      None{}
    case Some{big}:
      Some{Met{M.Opened{h, big}}}

def ev.skip(r: Maybe<&2, M.Reason>) -> Maybe<&2, Ev>:
  match r:
    case None{}:
      None{}
    case Some{w}:
      Some{Met{M.Skip{w}}}

def ev.o(xs: List<&2, Nat>) -> Maybe<&2, Ev>:
  match xs:
    case Nil{}:
      None{}
    case h <> a:
      match a:
        case Nil{}:
          None{}
        case b <> c:
          match c:
            case Nil{}:
              ev.opened(h, bit(b))
            case x <> d:
              None{}

def ev.s(xs: List<&2, Nat>) -> Maybe<&2, Ev>:
  match xs:
    case Nil{}:
      None{}
    case w <> a:
      match a:
        case Nil{}:
          ev.skip(why(w))
        case x <> b:
          None{}

# the event a list spells
def ev(xs: List<&2, Nat>) -> Maybe<&2, Ev>:
  match xs:
    case Nil{}:
      None{}
    case tag <> t:
      match tag:
        case 0n:
          ev.ask(ranges(t))
        case 1n:
          ev.o(t)
        case 2n:
          ev.s(t)
        case 3n+x:
          None{}

def lims(xs: List<&2, Nat>) -> Maybe<&2, St>:
  match xs:
    case Nil{}:
      None{}
    case p <> a:
      match a:
        case Nil{}:
          None{}
        case s <> b:
          match b:
            case Nil{}:
              None{}
            case k <> c:
              match c:
                case Nil{}:
                  None{}
                case rem <> d:
                  match d:
                    case Nil{}:
                      None{}
                    case t <> e:
                      match e:
                        case Nil{}:
                          None{}
                        case maxb <> f:
                          match f:
                            case Nil{}:
                              Some{Walk{p, s, k, rem, 0n, t, maxb}}
                            case x <> g:
                              None{}

def open.of(m: Maybe<&2, St>) -> St & String:
  match m:
    case None{}:
      (Shut{}, W.err("doc_search: malformed open"))
    case Some{st}:
      (st, "")

def open.end(done: Bool, xs: List<&2, Nat>) -> St & String:
  match done:
    case True{}:
      open.of(lims(xs))
    case False{}:
      (Shut{}, W.err("doc_search: malformed open"))

def open.got(r: W.Dec<List<&2, Nat>>) -> St & String:
  match r:
    case W.Got{xs, rest}:
      open.end(W.end(rest), xs)
    case W.Bad{}:
      (Shut{}, W.err("doc_search: malformed open"))

# open: a walk with the limits of the input, no matching file met yet
def open(input: String) -> St & String:
  open.got(W.get_list(~Nat, ~W.get_nat, input))

def reply(xs: List<&2, Nat>) -> String:
  W.put_list(~Nat, ~W.put_nat, xs, "")

# the next file: none when no match is left to keep (the t files left are
# not searched), else the matches to fetch from it
def step.ask(+p: Nat, +s: Nat, +k: Nat, rem: Nat, +n: Nat, +t: Nat, +maxb: Nat, rs: List<&2, M.Range>) -> St & String:
  match rem:
    case 0n:
      (Walk{p, s, k, 0n, n, t, maxb}, reply([0n, t]))
    case 1n++r:
      (Walk{p, s, k, 1n+r, n, t, maxb}, reply([1n, M.fetch(rs, p, 1n+r, maxb)]))

def step.met.nats(o: M.Out, +kept: Nat) -> List<&2, Nat>:
  match o:
    case M.Out{i, c, cut, pa}:
      [cls.n(c), bitn(cut), bitn(pa), kept]

# what a file held: its class, cut, searched in part, matches kept
def step.met(+p: Nat, +s: Nat, +k: Nat, +rem: Nat, +n: Nat, t: Nat, +maxb: Nat, f: M.Form) -> St & String:
  +e = {M.Ent{0n, f} : M.Ent}
  +o = M.out(e, p, s, k, rem, n)
  (Walk{p, s, k, M.left(e, p, rem), M.seen(e, rem, n), Nat.sub(t, 1n), maxb}, reply(step.met.nats(o, M.kept(e, p, rem))))

def step.ev(st: St, m: Maybe<&2, Ev>) -> St & String:
  match st:
    case Walk{p, s, k, rem, n, t, maxb}:
      match m:
        case None{}:
          (Walk{p, s, k, rem, n, t, maxb}, W.err("doc_search: malformed event"))
        case Some{e}:
          match e:
            case Ask{rs}:
              step.ask(p, s, k, rem, n, t, maxb, rs)
            case Met{f}:
              step.met(p, s, k, rem, n, t, maxb, f)
    case Shut{}:
      (Shut{}, W.err("doc_search: the open was refused"))

def step.end(st: St, done: Bool, xs: List<&2, Nat>) -> St & String:
  match done:
    case True{}:
      step.ev(st, ev(xs))
    case False{}:
      step.ev(st, None{})

def step.got(st: St, r: W.Dec<List<&2, Nat>>) -> St & String:
  match r:
    case W.Got{xs, rest}:
      step.end(st, W.end(rest), xs)
    case W.Bad{}:
      step.ev(st, None{})

# step: one event of the walk; the reply is the decision on it
def step(st: St, input: String) -> St & String:
  step.got(st, W.get_list(~Nat, ~W.get_nat, input))
