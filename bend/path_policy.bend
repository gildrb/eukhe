# path_policy: the model of the path policy (docs/tools.md S7, LAWS
# (G1), crates/eukhe-types/src/path_policy.rs and the document tools'
# gate, crates/eukhe-core/src/durable/path_policy.rs). It extends the
# path of bend/tools.bend §3 (segments under a root) to real filesystem
# paths with symlinks.
#
# 1. The real path. A path is a list of segments from `/`. A link sits
#    at its real location (names, deepest first) and points to segments,
#    from `/` (abs) or from its directory. A resolution follows every
#    link it meets, at most max_links() of them (fuel); past that, the
#    path loops. `..` of `/` is `/`.
# 2. The class of a real path under a policy: Secret (under a secret
#    entry), Protected (a rule covers it, or it is an ancestor of a rule's
#    entry or of a secret), Inside (under a workspace root), Outside. A
#    path that loops is never Inside.
# 3. The gate. An access's effects (codes: read 0, write 1, exec 2, net
#    3, outside 4, protected 5, secret 6) run without a question only when
#    the auto set holds each of them and each is grantable (below 4);
#    else only the user's yes runs them.
# 4. The store. An agent's writes through any paths, each judged by the
#    gate on its real path, with answers that are never yes, leave every
#    guarded (protected or secret) location as it was.
#
# A recursive scan takes the test of its first item as a parameter (Bend
# matches only parameters).

import Base
import ./tools.bend as Tl

# 1. The real path
# ----------------

# A symlink at `at` to `to`
type Link is Data:
  Link{at: List<&2, Nat>, abs: Bool, to: List<&2, Tl.Seg>}

def Link.at(l: Link) -> List<&2, Nat>:
  match l:
    case Link{a, b, t}:
      a

# The most links one resolution follows (eukhe_types MAX_LINKS)
def max_links() -> Nat:
  40n

# l when hit, else the rest's answer
def link.pick(hit: Bool, l: Link, rest: Maybe<&2, Link>) -> Maybe<&2, Link>:
  match hit:
    case True{}:
      Some{l}
    case False{}:
      rest

# the link at `at`, if any
def link.find(ls: List<&2, Link>, +at: List<&2, Nat>) -> Maybe<&2, Link>:
  match ls:
    case Nil{}:
      None{}
    case +l <> rest:
      link.pick(Tl.ids.eq(Link.at(l), at), l, link.find(rest, at))

# the link the first segment of segs reaches from `at`, if any
def look.at(+ls: List<&2, Link>, segs: List<&2, Tl.Seg>, at: List<&2, Nat>) -> Maybe<&2, Link>:
  match segs:
    case Nil{}:
      None{}
    case s <> rest:
      match s:
        case Tl.Name{n}:
          link.find(ls, n <> at)
        case Tl.Up{}:
          None{}
        case Tl.Here{}:
          None{}

# the parent of `at`; `/` stays `/`
def up(at: List<&2, Nat>) -> List<&2, Nat>:
  match at:
    case Nil{}:
      Nil{}
    case a <> above:
      above

# A resolved path and whether its links looped
type Res is Data:
  Res{at: List<&2, Nat>, looped: Bool}

def Res.at(r: Res) -> List<&2, Nat>:
  match r:
    case Res{a, l}:
      a

def Res.looped(r: Res) -> Bool:
  match r:
    case Res{a, l}:
      l

# resolve segs from `at` with `fuel` links left; look is
# look.at(ls, segs, at)
def go(fuel: Nat, segs: List<&2, Tl.Seg>, +ls: List<&2, Link>, +at: List<&2, Nat>, looped: Bool, look: Maybe<&2, Link>) -> Res:
  match fuel:
    case 0n:
      match segs:
        case Nil{}:
          Res{at, looped}
        case s <> +rest:
          match s:
            case Tl.Name{+n}:
              go(0n, rest, ls, n <> at, Bool.or(looped, Maybe.is_some(&2, Link, look)), look.at(ls, rest, n <> at))
            case Tl.Up{}:
              go(0n, rest, ls, up(at), looped, look.at(ls, rest, up(at)))
            case Tl.Here{}:
              go(0n, rest, ls, at, looped, look.at(ls, rest, at))
    case 1n+f:
      match segs:
        case Nil{}:
          Res{at, looped}
        case s <> +rest:
          match s:
            case Tl.Name{+n}:
              match look:
                case None{}:
                  go(1n+f, rest, ls, n <> at, looped, look.at(ls, rest, n <> at))
                case Some{l}:
                  match l:
                    case Link{la, abs, +to}:
                      match abs:
                        case True{}:
                          go(f, List.append(&2, Tl.Seg, to, rest), ls, Nil{}, looped, look.at(ls, List.append(&2, Tl.Seg, to, rest), Nil{}))
                        case False{}:
                          go(f, List.append(&2, Tl.Seg, to, rest), ls, at, looped, look.at(ls, List.append(&2, Tl.Seg, to, rest), at))
            case Tl.Up{}:
              go(1n+f, rest, ls, up(at), looped, look.at(ls, rest, up(at)))
            case Tl.Here{}:
              go(1n+f, rest, ls, at, looped, look.at(ls, rest, at))

# the real path of segs (from `/`)
def real(+ls: List<&2, Link>, +segs: List<&2, Tl.Seg>) -> Res:
  go(max_links(), segs, ls, Nil{}, False{}, look.at(ls, segs, Nil{}))

# no prefix of `at` (it, its parent, ...) is a link
def linkfree(+ls: List<&2, Link>, at: List<&2, Nat>) -> Bool:
  match at:
    case Nil{}:
      True{}
    case a <> +above:
      Bool.and(Maybe.is_none(&2, Link, link.find(ls, a <> above)), linkfree(ls, above))

# 2. The class
# ------------

type Rule is Data:
  Tree{p: List<&2, Nat>}    # the path and everything under it
  Dir{p: List<&2, Nat>}     # the directory and its direct entries
  Named{n: Nat}             # a name below the workspace root

type Pol is Data:
  Pol{roots: List<&2, List<&2, Nat>>, rules: List<&2, Rule>, secret: List<&2, List<&2, Nat>>}

def Pol.roots(p: Pol) -> List<&2, List<&2, Nat>>:
  match p:
    case Pol{r, u, s}:
      r

def Pol.rules(p: Pol) -> List<&2, Rule>:
  match p:
    case Pol{r, u, s}:
      u

def Pol.secret(p: Pol) -> List<&2, List<&2, Nat>>:
  match p:
    case Pol{r, u, s}:
      s

type Cls is Data:
  Inside{}
  Outside{}
  Protected{}
  Secret{}

# `p` is `real` or one of its ancestors (deepest first: a suffix)
def under(+p: List<&2, Nat>, real: List<&2, Nat>) -> Bool:
  match real:
    case Nil{}:
      Tl.ids.eq(p, Nil{})
    case +x <> +r:
      Bool.or(Tl.ids.eq(p, x <> r), under(p, r))

def any_under(ps: List<&2, List<&2, Nat>>, +real: List<&2, Nat>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> rest:
      Bool.or(under(p, real), any_under(rest, real))

# `real` is a strict ancestor of an entry of ps
def any_ancestor(ps: List<&2, List<&2, Nat>>, +real: List<&2, Nat>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case +p <> rest:
      Bool.or(Bool.and(under(real, p), Bool.not(Tl.ids.eq(real, p))), any_ancestor(rest, real))

# the concrete entries of the rules
def entries(rs: List<&2, Rule>) -> List<&2, List<&2, Nat>>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      match r:
        case Tree{p}:
          p <> entries(rest)
        case Dir{p}:
          p <> entries(rest)
        case Named{n}:
          entries(rest)

def longer.pick(b_longer: Bool, a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  match b_longer:
    case True{}:
      b
    case False{}:
      a

# the longer of a and b (a when equal)
def longer(+a: List<&2, Nat>, +b: List<&2, Nat>) -> List<&2, Nat>:
  longer.pick(Nat.is_lt(List.length(&2, Nat, a), List.length(&2, Nat, b)), a, b)

def root.pick(hit: Bool, +p: List<&2, Nat>, best: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  match hit:
    case False{}:
      best
    case True{}:
      match best:
        case None{}:
          Some{p}
        case Some{b}:
          Some{longer(p, b)}

# the deepest root `real` is under, if any
def root.of(rs: List<&2, List<&2, Nat>>, +real: List<&2, Nat>) -> Maybe<&2, List<&2, Nat>>:
  match rs:
    case Nil{}:
      None{}
    case +p <> rest:
      root.pick(under(p, real), p, root.of(rest, real))

def strip.pick(hit: Bool, x: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match hit:
    case True{}:
      Nil{}
    case False{}:
      x <> rest

# the names of `real` below `root` (deepest first)
def strip(real: List<&2, Nat>, +root: List<&2, Nat>) -> List<&2, Nat>:
  match real:
    case Nil{}:
      Nil{}
    case +x <> +r:
      strip.pick(Tl.ids.eq(x <> r, root), x, strip(r, root))

# the names of `real` below its root (all of them with no root)
def below(+real: List<&2, Nat>, root: Maybe<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match root:
    case None{}:
      real
    case Some{p}:
      strip(real, p)

def parent_is(+real: List<&2, Nat>, +p: List<&2, Nat>) -> Bool:
  match real:
    case Nil{}:
      False{}
    case x <> r:
      Tl.ids.eq(r, p)

def covers(r: Rule, +real: List<&2, Nat>, +low: List<&2, Nat>) -> Bool:
  match r:
    case Tree{p}:
      under(p, real)
    case Dir{+p}:
      Bool.or(Tl.ids.eq(real, p), parent_is(real, p))
    case Named{n}:
      Tl.elem(low, n)

def any_covers(rs: List<&2, Rule>, +real: List<&2, Nat>, +low: List<&2, Nat>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> rest:
      Bool.or(covers(r, real, low), any_covers(rest, real, low))

def cls.pick(sec: Bool, prot: Bool, inside: Bool) -> Cls:
  match sec:
    case True{}:
      Secret{}
    case False{}:
      match prot:
        case True{}:
          Protected{}
        case False{}:
          match inside:
            case True{}:
              Inside{}
            case False{}:
              Outside{}

# `real` is protected: a rule covers it, or it is an ancestor of an entry
def protects(+pol: Pol, +real: List<&2, Nat>) -> Bool:
  Bool.or(any_covers(Pol.rules(pol), real, below(real, root.of(Pol.roots(pol), real))), any_ancestor(List.append(&2, List<&2, Nat>, entries(Pol.rules(pol)), Pol.secret(pol)), real))

# the class of a real path
def class_of(+pol: Pol, +real: List<&2, Nat>) -> Cls:
  cls.pick(any_under(Pol.secret(pol), real), protects(pol, real), Maybe.is_some(&2, List<&2, Nat>, root.of(Pol.roots(pol), real)))

# a path whose links looped is never Inside
def demote(c: Cls, looped: Bool) -> Cls:
  match c:
    case Inside{}:
      match looped:
        case True{}:
          Outside{}
        case False{}:
          Inside{}
    case Outside{}:
      Outside{}
    case Protected{}:
      Protected{}
    case Secret{}:
      Secret{}

def class_res(+pol: Pol, r: Res) -> Cls:
  match r:
    case Res{at, looped}:
      demote(class_of(pol, at), looped)

# the class of segs under pol, judged on its real path
def class(+pol: Pol, +ls: List<&2, Link>, +segs: List<&2, Tl.Seg>) -> Cls:
  class_res(pol, real(ls, segs))

# no secret covers it, nothing protects it, and a root holds it
def inside_ok(sec: Bool, prot: Bool, ins: Bool) -> Bool:
  Bool.and(Bool.not(sec), Bool.and(Bool.not(prot), ins))

# a resolved path is safe to write unasked: its links did not loop, no
# secret covers it, no rule protects it, it is no ancestor of an entry,
# and a workspace root holds it
def safe(+pol: Pol, r: Res) -> Bool:
  match r:
    case Res{+at, looped}:
      Bool.and(Bool.not(looped), inside_ok(any_under(Pol.secret(pol), at), protects(pol, at), Maybe.is_some(&2, List<&2, Nat>, root.of(Pol.roots(pol), at))))

# segs is a secret or a directory that holds one
def holds(+pol: Pol, +ls: List<&2, Link>, +segs: List<&2, Tl.Seg>) -> Bool:
  +at = Res.at(real(ls, segs))
  Bool.or(any_under(Pol.secret(pol), at), any_ancestor(Pol.secret(pol), at))

# 3. The gate
# -----------

# What a document tool does: read a file, list a directory, search a
# directory (holds: it holds a secret), write
type Acc is Data:
  Rd{}
  Ls{}
  Sr{holds: Bool}
  Wr{}

# The user's answer to a question; Gone: no client answered
type Ans is Data:
  Yes{}
  No{}
  Gone{}

def read_of(c: Cls) -> List<&2, Nat>:
  match c:
    case Inside{}:
      [0n]
    case Outside{}:
      [0n]
    case Protected{}:
      [0n]
    case Secret{}:
      [0n, 6n]

def write_of(c: Cls) -> List<&2, Nat>:
  match c:
    case Inside{}:
      [1n]
    case Outside{}:
      [1n, 4n]
    case Protected{}:
      [1n, 5n]
    case Secret{}:
      [1n, 6n]

def search_of(holds: Bool, c: Cls) -> List<&2, Nat>:
  match holds:
    case True{}:
      [0n, 6n]
    case False{}:
      read_of(c)

# the effects of access a to a path of class c
def effs(c: Cls, a: Acc) -> List<&2, Nat>:
  match a:
    case Rd{}:
      read_of(c)
    case Ls{}:
      read_of(c)
    case Sr{h}:
      search_of(h, c)
    case Wr{}:
      write_of(c)

# the user may put effect e in the auto set (read, write, exec, net)
def grantable(e: Nat) -> Bool:
  Nat.is_lt(e, 4n)

# every effect is in the auto set and grantable
def allows(+auto: List<&2, Nat>, es: List<&2, Nat>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(grantable(e), Bool.and(allows(auto, rest), Tl.elem(auto, e)))

def Ans.yes(a: Ans) -> Bool:
  match a:
    case Yes{}:
      True{}
    case No{}:
      False{}
    case Gone{}:
      False{}

# the access runs: the auto set allows it, or the user said yes
def runs(c: Cls, a: Acc, +auto: List<&2, Nat>, ans: Ans) -> Bool:
  Bool.or(allows(auto, effs(c, a)), Ans.yes(ans))

# the gate asked the user
def asks(c: Cls, a: Acc, +auto: List<&2, Nat>) -> Bool:
  Bool.not(allows(auto, effs(c, a)))

def Cls.inside(c: Cls) -> Bool:
  match c:
    case Inside{}:
      True{}
    case Outside{}:
      False{}
    case Protected{}:
      False{}
    case Secret{}:
      False{}

# protected or secret
def Cls.guarded(c: Cls) -> Bool:
  match c:
    case Inside{}:
      False{}
    case Outside{}:
      False{}
    case Protected{}:
      True{}
    case Secret{}:
      True{}

def Cls.secret(c: Cls) -> Bool:
  match c:
    case Inside{}:
      False{}
    case Outside{}:
      False{}
    case Protected{}:
      False{}
    case Secret{}:
      True{}

# a read of a secret: a read or list of one, a search of a directory
# that holds one
def secret_read(c: Cls, a: Acc) -> Bool:
  match a:
    case Rd{}:
      Cls.secret(c)
    case Ls{}:
      Cls.secret(c)
    case Sr{h}:
      Bool.or(h, Cls.secret(c))
    case Wr{}:
      False{}

# 4. The store
# ------------

# one file's content at its real location
type Cell is Data:
  Cell{at: List<&2, Nat>, val: Nat}

def Cell.at(c: Cell) -> List<&2, Nat>:
  match c:
    case Cell{a, v}:
      a

# the cell c, or v at `at` in its place; rest follows the new cell, done
# (rest with the write) follows c
def set.pick(hit: Bool, c: Cell, +at: List<&2, Nat>, +v: Nat, rest: List<&2, Cell>, done: List<&2, Cell>) -> List<&2, Cell>:
  match hit:
    case True{}:
      Cell{at, v} <> rest
    case False{}:
      c <> done

# write v at `at`: in place of the first cell there, else at the end
def set(cs: List<&2, Cell>, +at: List<&2, Nat>, +v: Nat) -> List<&2, Cell>:
  match cs:
    case Nil{}:
      [Cell{at, v}]
    case +c <> +rest:
      set.pick(Tl.ids.eq(Cell.at(c), at), c, at, v, rest, set(rest, at, v))

# An agent's write of v through segs, and the user's answer if asked
type Put is Data:
  Put{segs: List<&2, Tl.Seg>, v: Nat, ans: Ans}

def put.pick(go: Bool, cs: List<&2, Cell>, +at: List<&2, Nat>, +v: Nat) -> List<&2, Cell>:
  match go:
    case True{}:
      set(cs, at, v)
    case False{}:
      cs

# one write: the gate judges it on its real path; it lands there
def step(+pol: Pol, +ls: List<&2, Link>, +auto: List<&2, Nat>, cs: List<&2, Cell>, p: Put) -> List<&2, Cell>:
  match p:
    case Put{+segs, v, ans}:
      put.pick(runs(class(pol, ls, segs), Wr{}, auto, ans), cs, Res.at(real(ls, segs)), v)

def run(es: List<&2, Put>, +pol: Pol, +ls: List<&2, Link>, +auto: List<&2, Nat>, cs: List<&2, Cell>) -> List<&2, Cell>:
  match es:
    case Nil{}:
      cs
    case e <> rest:
      run(rest, pol, ls, auto, step(pol, ls, auto, cs, e))

# the user said yes to one of the writes
def any_yes(es: List<&2, Put>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> rest:
      match e:
        case Put{s, v, a}:
          Bool.or(Ans.yes(a), any_yes(rest))

def keep.pick(keep: Bool, c: Cell, rest: List<&2, Cell>) -> List<&2, Cell>:
  match keep:
    case True{}:
      c <> rest
    case False{}:
      rest

# the cells at guarded locations: eukhe's config and the secrets
def guarded(cs: List<&2, Cell>, +pol: Pol) -> List<&2, Cell>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> rest:
      keep.pick(Cls.guarded(class_of(pol, Cell.at(c))), c, guarded(rest, pol))
