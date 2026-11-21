# path_own: the own paths (spec/README.md I3): Eukhe's own config and
# credentials (the agent dir itself and its direct entries, the agent
# profiles dir, every settings file the session reads), the session record
# (the sessions and sessions-archive trees) and the protected files of a
# check under acceptance. A write to one is refused, whatever the path
# policy's judge made of the path (bend/path_policy.bend `judge`); a read
# is never refused for it. The rules and the path are real paths, names
# deepest first (bend/path_policy.bend §1): the caller resolves the path
# and the rules, so an own path is refused at its real location, whatever
# link names it.
#
# The write class of an access is the judge's class, unless it writes a
# path an own rule names: then it is Own, with the place of the first rule
# that names the path (from 0), so the caller can say why.

import Base
import ./tools.bend as Tl
import ./path_policy.bend as Pp

# An own rule
type Rule is Data:
  Tree{p: List<&2, Nat>}    # the path and everything under it
  Dir{p: List<&2, Nat>}     # the directory and its direct entries

# The write class of an access
type Wc is Data:
  Judged{c: Pp.Cls}    # the judge's class: no own rule names the write
  Own{i: Nat}          # a write the rule at place i names: refused

# rule r names the real path `at`
def names(r: Rule, +at: List<&2, Nat>) -> Bool:
  match r:
    case Tree{p}:
      Pp.under(p, at)
    case Dir{+p}:
      Bool.or(Tl.ids.eq(at, p), Pp.parent_is(at, p))

# place i when hit, else the rest's answer
def first.pick(hit: Bool, i: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{i}
    case False{}:
      rest

# the place of the first rule of rs that names `at`, counting from i
def first(rs: List<&2, Rule>, +at: List<&2, Nat>, +i: Nat) -> Maybe<&2, Nat>:
  match rs:
    case Nil{}:
      None{}
    case r <> rest:
      first.pick(names(r, at), i, first(rest, at, 1n+i))

def of(m: Maybe<&2, Nat>, c: Pp.Cls) -> Wc:
  match m:
    case None{}:
      Judged{c}
    case Some{i}:
      Own{i}

# the class of an access to the real path `at` the judge classed c: a
# write (w) an own rule of rs names is Own; anything else keeps c
def class(rs: List<&2, Rule>, +at: List<&2, Nat>, c: Pp.Cls, w: Bool) -> Wc:
  match w:
    case True{}:
      of(first(rs, at, 0n), c)
    case False{}:
      Judged{c}
