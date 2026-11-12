# eukhe: the laws of area cvar: the compiled entry

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase
import ./model.bend as CvarModel

# ---- cvar expansion ----

# This section closes the model's section (laws/cvar/model.bend): the
# alias table and the key binds (R9, R10 of laws/cvar/model.bend), stated
# from the requirement (crates/eukhe-bend/src/rules/cvar.rs `expand`: a
# run of an alias runs the body of its first alias; a run of an alias that
# does not exist is unknown; the first error, left to right, stops it; a
# press runs the commands of its key's first bind), never by a copy of the
# model's depth-bounded walk. The premises are the laws' own checks on the
# table, never the model's lookups.

# no alias of as is named n
def spec_no_alias(as: List<&2, Cv.Alias>, +n: Nat) -> Bool:
  match as:
    case Nil{}:
      True{}
    case Cv.Alias{m, b} <> rest:
      Bool.and(Bool.not(Nat.is_eq(m, n)), spec_no_alias(rest, n))

# the command c sets or toggles a cvar
def spec_sets(c: Cv.Cmd) -> Bool:
  match c:
    case Cv.CSet{i, v}:
      True{}
    case Cv.CToggle{i}:
      True{}
    case Cv.CRun{n}:
      False{}
    case Cv.CGone{n}:
      False{}

# every command of cs sets or toggles a cvar: none runs an alias
def spec_sets_only(cs: List<&2, Cv.Cmd>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case c <> rest:
      Bool.and(spec_sets(c), spec_sets_only(rest))

# no bind of bs is for key k
def spec_no_bind(bs: List<&2, Cv.KeyBind>, +k: Nat) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Cv.KeyBind{j, c} <> rest:
      Bool.and(Bool.not(Nat.is_eq(j, k)), spec_no_bind(rest, k))

# LAW alias_sets_stay: a list of commands that only set or toggle cvars expands to exactly itself, in order, whatever the alias table
# EXCLUDES: a set or toggle lost, added, reordered or changed by the
#   expansion, a list without runs refused or reported as a cycle
law alias_sets_stay:
  for +cs: List<&2, Cv.Cmd>
  for +as: List<&2, Cv.Alias>
  for only: {spec_sets_only(cs) == True{} : Bool}
  {Cv.expand(cs, as) == Cv.Flat{cs} : Cv.Exp}

# LAW alias_gone_reported: a list whose first command names a missing alias (CGone n) expands to "unknown n", whatever follows it and whatever the table
# EXCLUDES: a missing alias skipped, reported under another name, or a
#   later command looked at after it
law alias_gone_reported:
  for +n: Nat
  for +rest: List<&2, Cv.Cmd>
  for +as: List<&2, Cv.Alias>
  {Cv.expand(Cv.CGone{n} <> rest, as) == Cv.Unknown{n} : Cv.Exp}

# LAW alias_runs_first_of_name: a run of alias n runs the body of the first alias named n: in pre ++ [Alias{n, b}] ++ post, where no alias of pre is named n and b only sets or toggles cvars, [run n] expands to exactly b, whatever post holds (a later alias named n included)
# EXCLUDES: a later alias of the name used, an alias of another name run,
#   a body lost, reordered or changed
law alias_runs_first_of_name:
  for +pre: List<&2, Cv.Alias>
  for +n: Nat
  for +b: List<&2, Cv.Cmd>
  for +post: List<&2, Cv.Alias>
  for fresh: {spec_no_alias(pre, n) == True{} : Bool}
  for only: {spec_sets_only(b) == True{} : Bool}
  {Cv.expand([Cv.CRun{n}], List.append(&2, Cv.Alias, pre, Cv.Alias{n, b} <> post)) == Cv.Flat{b} : Cv.Exp}

# LAW alias_missing_unknown: a run of a name no alias of the table has expands to "unknown", naming it
# EXCLUDES: a run of a missing alias that runs nothing, runs another
#   alias, or is reported as a cycle or under another name
law alias_missing_unknown:
  for +n: Nat
  for +as: List<&2, Cv.Alias>
  for none: {spec_no_alias(as, n) == True{} : Bool}
  {Cv.expand([Cv.CRun{n}], as) == Cv.Unknown{n} : Cv.Exp}

def spec_alias.pick(hit: Bool, b: List<&2, Cv.Cmd>, r: Maybe<&2, List<&2, Cv.Cmd>>) -> Maybe<&2, List<&2, Cv.Cmd>>:
  match hit:
    case True{}:
      Some{b}
    case False{}:
      r

# the body of the first alias named n in as, if any (the premises' own
# reading of the table: which alias a name means)
def spec_alias(as: List<&2, Cv.Alias>, +n: Nat) -> Maybe<&2, List<&2, Cv.Cmd>>:
  match as:
    case Nil{}:
      None{}
    case Cv.Alias{m, b} <> rest:
      spec_alias.pick(Nat.is_eq(m, n), b, spec_alias(rest, n))

# LAW alias_runs_nested: a run of an alias whose body runs another alias expands that alias's body in place: when the first alias named a has the body ps ++ [run b] and the first alias named b has the body qs, where ps and qs only set or toggle (so b is not a), a run of a expands to exactly ps ++ qs, whatever else the table holds and wherever the two aliases stand in it
# EXCLUDES: a nested run lost, run before the outer commands, refused for
#   a nesting bound too small (a false cycle), or run with a later alias
#   of the inner name
law alias_runs_nested:
  for +as: List<&2, Cv.Alias>
  for +a: Nat
  for +b: Nat
  for +ps: List<&2, Cv.Cmd>
  for +qs: List<&2, Cv.Cmd>
  for fp: {spec_sets_only(ps) == True{} : Bool}
  for fq: {spec_sets_only(qs) == True{} : Bool}
  for ha: {spec_alias(as, a) == Some{List.append(&2, Cv.Cmd, ps, [Cv.CRun{b}])} : Maybe<&2, List<&2, Cv.Cmd>>}
  for hb: {spec_alias(as, b) == Some{qs} : Maybe<&2, List<&2, Cv.Cmd>>}
  {Cv.expand([Cv.CRun{a}], as) == Cv.Flat{List.append(&2, Cv.Cmd, ps, qs)} : Cv.Exp}

# n is one of ns
def spec_in(ns: List<&2, Nat>, +n: Nat) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case +m <> rest:
      Bool.or(Nat.is_eq(m, n), spec_in(rest, n))

# cs sets or toggles, then runs an alias named in ns (what follows that
# run is free)
def spec_runs_into(cs: List<&2, Cv.Cmd>, +ns: List<&2, Nat>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case c <> rest:
      match c:
        case Cv.CSet{i, v}:
          spec_runs_into(rest, ns)
        case Cv.CToggle{i}:
          spec_runs_into(rest, ns)
        case Cv.CRun{m}:
          spec_in(ns, m)
        case Cv.CGone{m}:
          False{}

def spec_runs_into.at(m: Maybe<&2, List<&2, Cv.Cmd>>, +ns: List<&2, Nat>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{cs}:
      spec_runs_into(cs, ns)

# every name of xs has an alias whose first body runs into ns
def spec_closed(+as: List<&2, Cv.Alias>, xs: List<&2, Nat>, +ns: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(spec_runs_into.at(spec_alias(as, x), ns), spec_closed(as, rest, ns))

# the expansion is a cycle named in ns
def spec_cycle_in(e: Cv.Exp, +ns: List<&2, Nat>) -> Bool:
  match e:
    case Cv.Flat{cs}:
      False{}
    case Cv.Cycle{n}:
      spec_in(ns, n)
    case Cv.Unknown{n}:
      False{}

# LAW alias_cycle_closed: any cycle of aliases, of any length, is reported as a cycle named by one of its aliases: when every name of ns has an alias whose first body sets or toggles and then runs an alias named in ns (a cycle through the names of ns, whatever follows each run, whatever else the table holds), a run of any name of ns expands to a cycle named in ns
# EXCLUDES: a cycle through two or more aliases expanded without end,
#   reported as a flat list or an unknown alias, or named after an alias
#   outside the cycle
law alias_cycle_closed:
  for +as: List<&2, Cv.Alias>
  for +ns: List<&2, Nat>
  for +n: Nat
  for one: {spec_in(ns, n) == True{} : Bool}
  for closed: {spec_closed(as, ns, ns) == True{} : Bool}
  {spec_cycle_in(Cv.expand([Cv.CRun{n}], as), ns) == True{} : Bool}

# LAW alias_nesting_example: anchor: the premises of alias_runs_nested and alias_cycle_closed hold of real tables: alias 3 = [toggle 1, run 4], alias 4 = [toggle 2] runs as [toggle 1, toggle 2]; aliases 0 = [toggle 9, run 1] and 1 = [run 0, toggle 8] beside an unrelated alias 2 close {0, 1}, and a run of 0 is the cycle at 0
# EXCLUDES: vacuous alias_runs_nested or alias_cycle_closed (premises no
#   table meets)
law alias_nesting_example:
  {(spec_alias([Cv.Alias{3n, [Cv.CToggle{1n}, Cv.CRun{4n}]}, Cv.Alias{4n, [Cv.CToggle{2n}]}], 3n), Cv.expand([Cv.CRun{3n}], [Cv.Alias{3n, [Cv.CToggle{1n}, Cv.CRun{4n}]}, Cv.Alias{4n, [Cv.CToggle{2n}]}])) == (Some{[Cv.CToggle{1n}, Cv.CRun{4n}]}, Cv.Flat{[Cv.CToggle{1n}, Cv.CToggle{2n}]}) : Maybe<&2, List<&2, Cv.Cmd>> & Cv.Exp} &
  {(spec_closed([Cv.Alias{0n, [Cv.CToggle{9n}, Cv.CRun{1n}]}, Cv.Alias{1n, [Cv.CRun{0n}, Cv.CToggle{8n}]}, Cv.Alias{2n, [Cv.CToggle{7n}]}], [0n, 1n], [0n, 1n]), Cv.expand([Cv.CRun{0n}], [Cv.Alias{0n, [Cv.CToggle{9n}, Cv.CRun{1n}]}, Cv.Alias{1n, [Cv.CRun{0n}, Cv.CToggle{8n}]}, Cv.Alias{2n, [Cv.CToggle{7n}]}])) == (True{}, Cv.Cycle{0n}) : Bool & Cv.Exp}

# Expansion at any nesting depth (R9)
# -----------------------------------
# The laws' own expansion, the textbook unfolding: a set or a toggle stays,
# a run of a missing alias is unknown, a run of n is the expansion of the
# body of the first alias named n, in place, and the first error, left to
# right, stops it. It remembers the aliases it is inside of (the path) and
# fails (None) on a run of one of them, an alias that runs itself through
# any chain; and it fails when the nest is deeper than its fuel f. The law
# below holds for EVERY fuel, so it pins the code at every nesting depth:
# whenever this unfolding ends, at any depth, the code's expansion is its
# result. It never reads the code's depth bound (1 + the table's length).

# the body a run of n runs: the first alias named n, else a run of a
# missing alias
def spec_body.of(m: Maybe<&2, List<&2, Cv.Cmd>>, +n: Nat) -> List<&2, Cv.Cmd>:
  match m:
    case None{}:
      [Cv.CGone{n}]
    case Some{b}:
      b

def spec_body(+as: List<&2, Cv.Alias>, +n: Nat) -> List<&2, Cv.Cmd>:
  spec_body.of(spec_alias(as, n), n)

# the command c, then the expansion m of the rest
def spec_put(c: Cv.Cmd, m: Maybe<&2, Cv.Exp>) -> Maybe<&2, Cv.Exp>:
  match m:
    case None{}:
      None{}
    case Some{e}:
      match e:
        case Cv.Flat{xs}:
          Some{Cv.Flat{c <> xs}}
        case Cv.Cycle{k}:
          Some{Cv.Cycle{k}}
        case Cv.Unknown{k}:
          Some{Cv.Unknown{k}}

# the expansion a, then the expansion b: the commands of both, in order;
# an error of a stops it before b
def spec_then(a: Maybe<&2, Cv.Exp>, b: Maybe<&2, Cv.Exp>) -> Maybe<&2, Cv.Exp>:
  match a:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Cv.Flat{xs}:
          match b:
            case None{}:
              None{}
            case Some{y}:
              match y:
                case Cv.Flat{ys}:
                  Some{Cv.Flat{List.append(&2, Cv.Cmd, xs, ys)}}
                case Cv.Cycle{k}:
                  Some{Cv.Cycle{k}}
                case Cv.Unknown{k}:
                  Some{Cv.Unknown{k}}
        case Cv.Cycle{k}:
          Some{Cv.Cycle{k}}
        case Cv.Unknown{k}:
          Some{Cv.Unknown{k}}

# a run met while inside the alias it names (on the path) fails; else its
# body's expansion b, then the rest's expansion r
def spec_run(on_path: Bool, b: Maybe<&2, Cv.Exp>, r: Maybe<&2, Cv.Exp>) -> Maybe<&2, Cv.Exp>:
  match on_path:
    case True{}:
      None{}
    case False{}:
      spec_then(b, r)

# the expansion of cs with the alias table as, inside the aliases of the
# path p, nesting at most f runs deep (None: a run on the path, or a nest
# deeper than f)
def spec_exp(f: Nat, cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +p: List<&2, Nat>) -> Maybe<&2, Cv.Exp>:
  match f:
    case 0n:
      match cs:
        case Nil{}:
          Some{Cv.Flat{Nil{}}}
        case c <> rest:
          match c:
            case Cv.CSet{i, v}:
              spec_put(Cv.CSet{i, v}, spec_exp(0n, rest, as, p))
            case Cv.CToggle{i}:
              spec_put(Cv.CToggle{i}, spec_exp(0n, rest, as, p))
            case Cv.CRun{n}:
              None{}
            case Cv.CGone{n}:
              Some{Cv.Unknown{n}}
    case 1n+(+g):
      match cs:
        case Nil{}:
          Some{Cv.Flat{Nil{}}}
        case c <> rest:
          match c:
            case Cv.CSet{i, v}:
              spec_put(Cv.CSet{i, v}, spec_exp(1n+g, rest, as, p))
            case Cv.CToggle{i}:
              spec_put(Cv.CToggle{i}, spec_exp(1n+g, rest, as, p))
            case Cv.CRun{+n}:
              spec_run(spec_in(p, n), spec_exp(g, spec_body(as, n), as, n <> p), spec_exp(1n+g, rest, as, p))
            case Cv.CGone{n}:
              Some{Cv.Unknown{n}}

# LAW alias_expands_any_depth (R9): alias expansion is right at every nesting depth, on every alias table: for every fuel f, when the laws' unfolding of cs (spec_exp above: each run replaced in place by the expansion of the body of the first alias of its name, a missing alias unknown, the first error left to right stopping it; it fails on an alias met again inside itself, and past f nested runs) ends with an outcome e, the code's expansion of cs is exactly e. So on a table with no cycle every expansion, however deep its aliases nest, is that unfolding; the code's nesting bound never cuts a nest that ends (no false cycle), nor lets a deep nest through changed
# EXCLUDES: a depth bound below the depth a cycle-free table can nest (a
#   false cycle at depth 2, 3 or the table's length), a nested body
#   expanded with a later alias of its name, out of order, partly, or
#   after the commands that follow its run, an unknown alias deep in a
#   nest reported under another name, a set or toggle of a nested body
#   lost or added
law alias_expands_any_depth:
  for +f: Nat
  for +cs: List<&2, Cv.Cmd>
  for +as: List<&2, Cv.Alias>
  for +e: Cv.Exp
  for ends: {spec_exp(f, cs, as, Nil{}) == Some{e} : Maybe<&2, Cv.Exp>}
  {Cv.expand(cs, as) == e : Cv.Exp}

# LAW alias_any_depth_example: anchor: alias_expands_any_depth's premise holds of a nest three runs deep: aliases 0 = [toggle 1, run 1], 1 = [run 2, toggle 2], 2 = [toggle 3]; the unfolding of [run 0] with fuel 3 is [toggle 1, toggle 3, toggle 2], and so is the code's expansion
# EXCLUDES: a vacuous alias_expands_any_depth (an unfolding that never
#   ends past one level)
law alias_any_depth_example:
  {(spec_exp(3n, [Cv.CRun{0n}], [Cv.Alias{0n, [Cv.CToggle{1n}, Cv.CRun{1n}]}, Cv.Alias{1n, [Cv.CRun{2n}, Cv.CToggle{2n}]}, Cv.Alias{2n, [Cv.CToggle{3n}]}], Nil{}), Cv.expand([Cv.CRun{0n}], [Cv.Alias{0n, [Cv.CToggle{1n}, Cv.CRun{1n}]}, Cv.Alias{1n, [Cv.CRun{2n}, Cv.CToggle{2n}]}, Cv.Alias{2n, [Cv.CToggle{3n}]}])) == (Some{Cv.Flat{[Cv.CToggle{1n}, Cv.CToggle{3n}, Cv.CToggle{2n}]}}, Cv.Flat{[Cv.CToggle{1n}, Cv.CToggle{3n}, Cv.CToggle{2n}]}) : Maybe<&2, Cv.Exp> & Cv.Exp}

# The laws' own test of a nest that never ends: the unfolding of cs, the
# same walk as spec_exp above (a set or a toggle passes, a run of n walks
# the body of the first alias named n with n on the path, then the rest),
# meets a run of an alias it is already inside of before it meets a
# missing alias or the end of its fuel f. Such a nest runs an alias
# inside itself, so its unfolding never ends; and a nest that never ends
# must run some alias inside itself, as the table holds finitely many,
# whether its aliases form a closed cycle or it reaches one after other
# runs. With alias_expands_any_depth (every nest that ends), this covers
# the code's expansion at every depth on every table, cyclic or not: the
# exact outcome of a nest that ends, a cycle for one that does not.

# the rest's test, after the body's: the body loops (lb), or it ended (eb)
# with commands only and the rest loops (lr)
def spec_loop.then(lb: Bool, eb: Maybe<&2, Cv.Exp>, lr: Bool) -> Bool:
  match lb:
    case True{}:
      True{}
    case False{}:
      match eb:
        case None{}:
          False{}
        case Some{x}:
          match x:
            case Cv.Flat{xs}:
              lr
            case Cv.Cycle{k}:
              False{}
            case Cv.Unknown{k}:
              False{}

# a run met inside the alias it names (on the path) loops; else the body's
# test, then the rest's
def spec_loop.run(on_path: Bool, lb: Bool, eb: Maybe<&2, Cv.Exp>, lr: Bool) -> Bool:
  match on_path:
    case True{}:
      True{}
    case False{}:
      spec_loop.then(lb, eb, lr)

# the unfolding of cs with the alias table as, inside the aliases of the
# path p, with fuel f, runs an alias it is inside of before any error
def spec_loop(f: Nat, cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +p: List<&2, Nat>) -> Bool:
  match f:
    case 0n:
      match cs:
        case Nil{}:
          False{}
        case c <> rest:
          match c:
            case Cv.CSet{i, v}:
              spec_loop(0n, rest, as, p)
            case Cv.CToggle{i}:
              spec_loop(0n, rest, as, p)
            case Cv.CRun{n}:
              spec_in(p, n)
            case Cv.CGone{n}:
              False{}
    case 1n+(+g):
      match cs:
        case Nil{}:
          False{}
        case c <> rest:
          match c:
            case Cv.CSet{i, v}:
              spec_loop(1n+g, rest, as, p)
            case Cv.CToggle{i}:
              spec_loop(1n+g, rest, as, p)
            case Cv.CRun{+n}:
              spec_loop.run(spec_in(p, n), spec_loop(g, spec_body(as, n), as, n <> p), spec_exp(g, spec_body(as, n), as, n <> p), spec_loop(1n+g, rest, as, p))
            case Cv.CGone{n}:
              False{}

# the expansion is a cycle (of any name)
def spec_is_cycle(e: Cv.Exp) -> Bool:
  match e:
    case Cv.Flat{cs}:
      False{}
    case Cv.Cycle{n}:
      True{}
    case Cv.Unknown{n}:
      False{}

# LAW alias_endless_is_cycle (R9): an alias nest that never ends is reported as a cycle, on every table, at any depth: for every fuel f, when the laws' unfolding of cs (spec_loop above: the walk of spec_exp, each run walking the first alias of its name) runs an alias it is already inside of before any missing alias, the code's expansion of cs is a cycle, whether that alias belongs to a closed cycle or is reached through other runs and after commands and nests that end
# EXCLUDES: a nest that never ends expanded without end, cut short and
#   reported as a flat list of the commands so far, or as an unknown
#   alias; a cycle entered from an alias outside it, or after a nested
#   run that ends, missed
law alias_endless_is_cycle:
  for +f: Nat
  for +cs: List<&2, Cv.Cmd>
  for +as: List<&2, Cv.Alias>
  for loops: {spec_loop(f, cs, as, Nil{}) == True{} : Bool}
  {spec_is_cycle(Cv.expand(cs, as)) == True{} : Bool}

# LAW alias_endless_example: anchor: alias_endless_is_cycle's premise holds of a nest that is no closed cycle: aliases 0 = [toggle 1, run 1], 1 = [run 2, toggle 2], 2 = [run 3, run 1], 3 = [toggle 3] (alias 3 runs nothing, so no set of these aliases is closed); the unfolding of [run 0] with fuel 4 runs 1 inside itself, and the code's expansion of [run 0] is a cycle
# EXCLUDES: a vacuous alias_endless_is_cycle (a loop test no table meets)
law alias_endless_example:
  {(spec_loop(4n, [Cv.CRun{0n}], [Cv.Alias{0n, [Cv.CToggle{1n}, Cv.CRun{1n}]}, Cv.Alias{1n, [Cv.CRun{2n}, Cv.CToggle{2n}]}, Cv.Alias{2n, [Cv.CRun{3n}, Cv.CRun{1n}]}, Cv.Alias{3n, [Cv.CToggle{3n}]}], Nil{}), spec_is_cycle(Cv.expand([Cv.CRun{0n}], [Cv.Alias{0n, [Cv.CToggle{1n}, Cv.CRun{1n}]}, Cv.Alias{1n, [Cv.CRun{2n}, Cv.CToggle{2n}]}, Cv.Alias{2n, [Cv.CRun{3n}, Cv.CRun{1n}]}, Cv.Alias{3n, [Cv.CToggle{3n}]}]))) == (True{}, True{}) : Bool & Bool}

# LAW bind_absent_runs_nothing: a press of a key no bind of the table names runs nothing
# EXCLUDES: an unbound key that runs a default or another key's commands
law bind_absent_runs_nothing:
  for +bs: List<&2, Cv.KeyBind>
  for +k: Nat
  for +as: List<&2, Cv.Alias>
  for +none: {spec_no_bind(bs, k) == True{} : Bool}
  {Cv.press(bs, k, as) == Cv.Flat{Nil{}} : Cv.Exp}

# LAW bind_other_key_skipped: a bind of another key does not change a press: a press of k on KeyBind{j, c} <> bs, j not k, is the press of k on bs (with bind_first_wins and bind_absent_runs_nothing: a press runs the commands of its key's first bind, else nothing)
# EXCLUDES: a press that runs the first bind whatever its key, or a bind
#   of another key
law bind_other_key_skipped:
  for +j: Nat
  for +c: List<&2, Cv.Cmd>
  for +bs: List<&2, Cv.KeyBind>
  for +k: Nat
  for +as: List<&2, Cv.Alias>
  for other: {Nat.is_eq(j, k) == False{} : Bool}
  {Cv.press(Cv.KeyBind{j, c} <> bs, k, as) == Cv.press(bs, k, as) : Cv.Exp}

# ---- cvar_entry ----

# LAWS (S4, the compiled core): the entries of bend/ffi_cvar.bend run the
# expansion and the key presses for the Rust code. Each law is an open
# claim about those entries; PROOF.bend proves them (as Cvar.<law>) with
# the lemmas of proof/cvar/.

# The entries of the compiled core (bend/ffi_cvar.bend)
# ------------------------------------------------------
# The Rust code (crates/eukhe-bend/src/rules/cvar.rs) numbers the aliases
# and the keys, and keeps every command that is not a run aside: such a
# command crosses as CToggle{its place} (the model passes it through
# unchanged: alias_runs_body, alias_expands_in_order).

# the numbers of a value fit the wire
def cvar_val_fits(v: Cv.Val) -> Bool:
  match v:
    case Cv.VNat{n}:
      LawsBase.wire_fits(n)
    case Cv.VBool{b}:
      True{}

# the numbers of a command fit the wire
def cvar_cmd_fits(c: Cv.Cmd) -> Bool:
  match c:
    case Cv.CSet{i, v}:
      Bool.and(LawsBase.wire_fits(i), cvar_val_fits(v))
    case Cv.CToggle{i}:
      LawsBase.wire_fits(i)
    case Cv.CRun{n}:
      LawsBase.wire_fits(n)
    case Cv.CGone{n}:
      LawsBase.wire_fits(n)

# every item of xs fits the wire
def cvar_cmds_all(xs: List<&2, Cv.Cmd>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(cvar_cmd_fits(x), cvar_cmds_all(t))

# a command list fits the wire
def cvar_cmds_fit(+cs: List<&2, Cv.Cmd>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Cv.Cmd, cs)), cvar_cmds_all(cs))

# an alias fits the wire
def cvar_alias_fits(a: Cv.Alias) -> Bool:
  match a:
    case Cv.Alias{n, b}:
      Bool.and(LawsBase.wire_fits(n), cvar_cmds_fit(b))

# every item of xs fits the wire
def cvar_aliases_all(xs: List<&2, Cv.Alias>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(cvar_alias_fits(x), cvar_aliases_all(t))

# a key bind fits the wire
def cvar_bind_fits(k: Cv.KeyBind) -> Bool:
  match k:
    case Cv.KeyBind{n, c}:
      Bool.and(LawsBase.wire_fits(n), cvar_cmds_fit(c))

# every item of xs fits the wire
def cvar_binds_all(xs: List<&2, Cv.KeyBind>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(cvar_bind_fits(x), cvar_binds_all(t))

# an alias table fits the wire
def cvar_aliases_fit(+as: List<&2, Cv.Alias>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Cv.Alias, as)), cvar_aliases_all(as))

# a bind table fits the wire
def cvar_binds_fit(+bs: List<&2, Cv.KeyBind>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Cv.KeyBind, bs)), cvar_binds_all(bs))

# LAW cvar_ffi_round_trip: an expand request that fits reads back whole
# EXCLUDES: an alias, a command or a number lost, swapped or misread on
#   the way to the model
law cvar_ffi_round_trip:
  for +as: List<&2, Cv.Alias>
  for +cs: List<&2, Cv.Cmd>
  for +rest: String
  for h: {Bool.and(cvar_aliases_fit(as), cvar_cmds_fit(cs)) == True{} : Bool}
  {FCv.get_xreq(FCv.put_xreq(FCv.Xreq{as, cs}, rest)) == Wr.Got{FCv.Xreq{as, cs}, rest} : Wr.Dec<FCv.Xreq>}

# LAW cvar_ffi_is_expand: the expand entry answers the model's expansion
# EXCLUDES: an entry that expands by any other rule, or answers a default
law cvar_ffi_is_expand:
  for +as: List<&2, Cv.Alias>
  for +cs: List<&2, Cv.Cmd>
  for h: {Bool.and(cvar_aliases_fit(as), cvar_cmds_fit(cs)) == True{} : Bool}
  {FCv.ffi(FCv.put_xreq(FCv.Xreq{as, cs}, "")) == FCv.put_exp(Cv.expand(cs, as), "") : String}

# LAW cvar_ffi_malformed: a malformed expand request answers the error form
# EXCLUDES: a default expansion (nothing to run) for bad input
law cvar_ffi_malformed:
  for +s: String
  for h: {FCv.get_xreq(s) == Wr.Bad{} : Wr.Dec<FCv.Xreq>}
  {FCv.ffi(s) == Wr.err("cvar: malformed expand request") : String}

# LAW cvar_ffi_open: a bind table that fits opens the press state of that table
# EXCLUDES: a table read with a bind or an alias lost or changed
law cvar_ffi_open:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for h: {Bool.and(cvar_binds_fit(bs), cvar_aliases_fit(as)) == True{} : Bool}
  {FCv.open(FCv.put_table(bs, as, "")) == (FCv.Table{bs, as}, "") : FCv.St & String}

# LAW cvar_ffi_open_malformed: a malformed bind table opens the refused state, with the error form
# EXCLUDES: an empty table (every key unbound) for bad input
law cvar_ffi_open_malformed:
  for +s: String
  for h: {FCv.get_table(s) == Wr.Bad{} : Wr.Dec<FCv.St>}
  {FCv.open(s) == (FCv.Refused{}, Wr.err("cvar: malformed press table")) : FCv.St & String}

# LAW cvar_ffi_press: a press of a key answers the model's press, and the table stays
# EXCLUDES: a press by any other rule, a table that changes between
#   presses
law cvar_ffi_press:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for +k: Nat
  for h: {LawsBase.wire_fits(k) == True{} : Bool}
  {FCv.step(FCv.Table{bs, as}, Wr.put_nat(k, "")) == (FCv.Table{bs, as}, FCv.put_exp(Cv.press(bs, k, as), "")) : FCv.St & String}

# LAW cvar_ffi_refused: a refused table answers every press with the error form
# EXCLUDES: a press that runs anything after a refused open
law cvar_ffi_refused:
  for +s: String
  {FCv.step(FCv.Refused{}, s) == (FCv.Refused{}, Wr.err("cvar: the press table was refused")) : FCv.St & String}

# LAW cvar_fits_example: witness: a table and a command list fit
law cvar_fits_example:
  {Bool.and(cvar_binds_fit([Cv.KeyBind{0n, [Cv.CRun{1n}, Cv.CToggle{0n}]}]), Bool.and(cvar_aliases_fit([Cv.Alias{1n, [Cv.CSet{2n, Cv.VBool{True{}}}, Cv.CGone{3n}]}]), cvar_cmds_fit([Cv.CSet{0n, Cv.VNat{7n}}]))) == True{} : Bool}

# The bytes of the entries, spelled
# ---------------------------------
# The grammar Rust writes and reads (crates/eukhe-bend/src/rules/cvar.rs),
# spelled from the wire primitives only, never the entry's put_*/get_*:
# Val = 0 n | 1 b; Cmd = 0 i Val | 1 i | 2 n | 3 n; a list is its count,
# then its items; Alias = name, body; KeyBind = key, commands; Exp = 0
# commands (Flat) | 1 n (Cycle) | 2 n (Unknown). An expand request is the
# aliases, then the commands; a press table the binds, then the aliases;
# a press the key.

def cvar_spell_val(v: Cv.Val, rest: String) -> String:
  match v:
    case Cv.VNat{n}:
      Wr.put_nat(0n, Wr.put_nat(n, rest))
    case Cv.VBool{b}:
      Wr.put_nat(1n, Wr.put_bool(b, rest))

def cvar_spell_cmd(c: Cv.Cmd, rest: String) -> String:
  match c:
    case Cv.CSet{i, v}:
      Wr.put_nat(0n, Wr.put_nat(i, cvar_spell_val(v, rest)))
    case Cv.CToggle{i}:
      Wr.put_nat(1n, Wr.put_nat(i, rest))
    case Cv.CRun{n}:
      Wr.put_nat(2n, Wr.put_nat(n, rest))
    case Cv.CGone{n}:
      Wr.put_nat(3n, Wr.put_nat(n, rest))

def cvar_spell_cmds.items(cs: List<&2, Cv.Cmd>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case Con{c, t}:
      cvar_spell_cmd(c, cvar_spell_cmds.items(t, rest))

def cvar_spell_cmds(+cs: List<&2, Cv.Cmd>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Cv.Cmd, cs), cvar_spell_cmds.items(cs, rest))

def cvar_spell_alias(a: Cv.Alias, rest: String) -> String:
  match a:
    case Cv.Alias{n, b}:
      Wr.put_nat(n, cvar_spell_cmds(b, rest))

def cvar_spell_aliases.items(xs: List<&2, Cv.Alias>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      cvar_spell_alias(x, cvar_spell_aliases.items(t, rest))

def cvar_spell_aliases(+xs: List<&2, Cv.Alias>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Cv.Alias, xs), cvar_spell_aliases.items(xs, rest))

def cvar_spell_bind(k: Cv.KeyBind, rest: String) -> String:
  match k:
    case Cv.KeyBind{n, c}:
      Wr.put_nat(n, cvar_spell_cmds(c, rest))

def cvar_spell_binds.items(xs: List<&2, Cv.KeyBind>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      cvar_spell_bind(x, cvar_spell_binds.items(t, rest))

def cvar_spell_binds(+xs: List<&2, Cv.KeyBind>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Cv.KeyBind, xs), cvar_spell_binds.items(xs, rest))

def cvar_spell_exp(e: Cv.Exp, rest: String) -> String:
  match e:
    case Cv.Flat{cs}:
      Wr.put_nat(0n, cvar_spell_cmds(cs, rest))
    case Cv.Cycle{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))
    case Cv.Unknown{n}:
      Wr.put_nat(2n, Wr.put_nat(n, rest))

# the state of a stepper's answer
def cvar_st_of(r: FCv.St & String) -> FCv.St:
  match r:
    case (st, a):
      st

# the reply of a stepper's answer
def cvar_reply_of(r: FCv.St & String) -> String:
  match r:
    case (st, a):
      a

def cvar_refused_with.at(st: FCv.St, a: String, text: String) -> Bool:
  match st:
    case FCv.Table{bs, as}:
      False{}
    case FCv.Refused{}:
      String.eq(a, Wr.err(text))

# the answer is the refused state with the error form of text
def cvar_refused_with(r: FCv.St & String, text: String) -> Bool:
  match r:
    case (st, a):
      cvar_refused_with.at(st, a, text)

# LAW cvar_ffi_answers_spelled: an expand request spelled by the grammar, every number within
# the wire, answers the spelled expansion of the model (Cv.expand)
# EXCLUDES: a command, value or expansion tag or a field order that drifts
#   from Rust's grammar on both sides of the entry alike, a field lost or
#   swapped, a reversed Bool, an expansion by another rule
law cvar_ffi_answers_spelled:
  for +as: List<&2, Cv.Alias>
  for +cs: List<&2, Cv.Cmd>
  for fits: {Bool.and(cvar_aliases_fit(as), cvar_cmds_fit(cs)) == True{} : Bool}
  {FCv.ffi(cvar_spell_aliases(as, cvar_spell_cmds(cs, ""))) == cvar_spell_exp(Cv.expand(cs, as), "") : String}

# LAW cvar_ffi_left_over_spelled: a spelled expand request that fits, then any more input,
# answers the error form "cvar: input left over"
# EXCLUDES: trailing input ignored or read as part of the request, another error text
law cvar_ffi_left_over_spelled:
  for +as: List<&2, Cv.Alias>
  for +cs: List<&2, Cv.Cmd>
  for fits: {Bool.and(cvar_aliases_fit(as), cvar_cmds_fit(cs)) == True{} : Bool}
  for +c: Char
  for +t: String
  {FCv.ffi(cvar_spell_aliases(as, cvar_spell_cmds(cs, SCon{c, t}))) == Wr.err("cvar: input left over") : String}

# LAW cvar_ffi_reads_only_requests: an expand answer that is not the error form answers a
# request: the input is exactly a spelled request that fits, the answer its spelled expansion
# EXCLUDES: a decoder that accepts an unknown tag, a missing or extra field
#   or item, a number past the wire or input left over, and answers it anyway
law cvar_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FCv.ffi(s)) == False{} : Bool}
  exs as: List<&2, Cv.Alias>
  exs cs: List<&2, Cv.Cmd>
  {(s, (Bool.and(cvar_aliases_fit(as), cvar_cmds_fit(cs)), FCv.ffi(s))) == (cvar_spell_aliases(as, cvar_spell_cmds(cs, "")), (True{}, cvar_spell_exp(Cv.expand(cs, as), ""))) : String & (Bool & String)}

# LAW cvar_ffi_malformed_unless_request: every expand answer but the error form "cvar:
# malformed expand request" comes from an input that begins with a spelled request that fits
# EXCLUDES: the left-over error or an expansion for input that holds no
#   request (an unknown tag, a short list, a number past the wire), the
#   malformed error spelled with another text
law cvar_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FCv.ffi(s), Wr.err("cvar: malformed expand request")) == False{} : Bool}
  exs as: List<&2, Cv.Alias>
  exs cs: List<&2, Cv.Cmd>
  exs rest: String
  {(s, Bool.and(cvar_aliases_fit(as), cvar_cmds_fit(cs))) == (cvar_spell_aliases(as, cvar_spell_cmds(cs, rest)), True{}) : String & Bool}

# LAW cvar_open_answers_spelled: a press table spelled by the grammar, every number within the
# wire, opens the press state of exactly that table, with the empty reply
# EXCLUDES: a bind or alias lost, swapped or misread under a tag or field
#   order both sides of the entry share, a refused good table
law cvar_open_answers_spelled:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for fits: {Bool.and(cvar_binds_fit(bs), cvar_aliases_fit(as)) == True{} : Bool}
  {FCv.open(cvar_spell_binds(bs, cvar_spell_aliases(as, ""))) == (FCv.Table{bs, as}, "") : FCv.St & String}

# LAW cvar_open_left_over_spelled: a spelled press table that fits, then any more input, opens
# the refused state with the error form "cvar: input left over"
# EXCLUDES: trailing input ignored, a table opened from it, another error text
law cvar_open_left_over_spelled:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for fits: {Bool.and(cvar_binds_fit(bs), cvar_aliases_fit(as)) == True{} : Bool}
  for +c: Char
  for +t: String
  {FCv.open(cvar_spell_binds(bs, cvar_spell_aliases(as, SCon{c, t}))) == (FCv.Refused{}, Wr.err("cvar: input left over")) : FCv.St & String}

# LAW cvar_open_reads_only_tables: an open whose reply is not the error form read exactly a
# spelled table that fits, and opens its press state with the empty reply
# EXCLUDES: a table opened from an unknown tag, a short list, a number past
#   the wire or input left over
law cvar_open_reads_only_tables:
  for +s: String
  for ok: {LawsBase.wire_opens_err(cvar_reply_of(FCv.open(s))) == False{} : Bool}
  exs bs: List<&2, Cv.KeyBind>
  exs as: List<&2, Cv.Alias>
  {(s, (Bool.and(cvar_binds_fit(bs), cvar_aliases_fit(as)), FCv.open(s))) == (cvar_spell_binds(bs, cvar_spell_aliases(as, "")), (True{}, (FCv.Table{bs, as}, ""))) : String & (Bool & (FCv.St & String))}

# LAW cvar_open_malformed_unless_table: every open but the refused state with the error form
# "cvar: malformed press table" reads an input that begins with a spelled table that fits
# EXCLUDES: a table (or the left-over error) for input that holds no table,
#   a malformed table that opens anything but the refused state, the
#   malformed error spelled with another text
law cvar_open_malformed_unless_table:
  for +s: String
  for other: {cvar_refused_with(FCv.open(s), "cvar: malformed press table") == False{} : Bool}
  exs bs: List<&2, Cv.KeyBind>
  exs as: List<&2, Cv.Alias>
  exs rest: String
  {(s, Bool.and(cvar_binds_fit(bs), cvar_aliases_fit(as))) == (cvar_spell_binds(bs, cvar_spell_aliases(as, rest)), True{}) : String & Bool}

# LAW cvar_step_answers_spelled: a press of a key spelled on the wire, within it, answers the
# spelled expansion of the model's press (Cv.press) on the table, and the table stays
# EXCLUDES: an expansion tag that drifts from Rust's grammar on both sides,
#   a press by another rule, a table that changes between presses
law cvar_step_answers_spelled:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for +k: Nat
  for fits: {LawsBase.wire_fits(k) == True{} : Bool}
  {FCv.step(FCv.Table{bs, as}, Wr.put_nat(k, "")) == (FCv.Table{bs, as}, cvar_spell_exp(Cv.press(bs, k, as), "")) : FCv.St & String}

# LAW cvar_step_left_over_spelled: a spelled key that fits, then any more input, answers the
# error form "cvar: input left over", and the table stays
# EXCLUDES: trailing input ignored or read as part of the key, another error text
law cvar_step_left_over_spelled:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for +k: Nat
  for fits: {LawsBase.wire_fits(k) == True{} : Bool}
  for +c: Char
  for +t: String
  {FCv.step(FCv.Table{bs, as}, Wr.put_nat(k, SCon{c, t})) == (FCv.Table{bs, as}, Wr.err("cvar: input left over")) : FCv.St & String}

# the replies of the shipped stepper to the inputs ins, one step each,
# from the state st
def cvar_feed(ins: List<&2, String>, +st: FCv.St) -> List<&2, String>:
  match ins:
    case Nil{}:
      Nil{}
    case Con{+i, rest}:
      cvar_reply_of(FCv.step(st, i)) <> cvar_feed(rest, cvar_st_of(FCv.step(st, i)))

# the replies to the inputs ins, each sent alone to the press state of the
# table of binds bs and aliases as
def cvar_fresh(ins: List<&2, String>, +bs: List<&2, Cv.KeyBind>, +as: List<&2, Cv.Alias>) -> List<&2, String>:
  match ins:
    case Nil{}:
      Nil{}
    case Con{i, rest}:
      cvar_reply_of(FCv.step(FCv.Table{bs, as}, i)) <> cvar_fresh(rest, bs, as)

# LAW cvar_history_keeps_table: open a press table spelled by the grammar, every number within
# the wire, then send it any inputs, malformed or not: every reply is the
# reply the opened table gives that input alone (with cvar_step_answers_spelled,
# cvar_step_left_over_spelled, cvar_step_reads_only_keys and
# cvar_step_malformed_unless_key: at every point of every history, a key
# within the wire answers the spelled press of the table that was opened,
# and every other input an error form)
# EXCLUDES: a press, malformed or not, that drops, refuses, changes or
#   reorders the table for the presses after it, a stepper that answers a
#   press from an earlier one
law cvar_history_keeps_table:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for fits: {Bool.and(cvar_binds_fit(bs), cvar_aliases_fit(as)) == True{} : Bool}
  for +ins: List<&2, String>
  {cvar_feed(ins, cvar_st_of(FCv.open(cvar_spell_binds(bs, cvar_spell_aliases(as, ""))))) == cvar_fresh(ins, bs, as) : List<&2, String>}

# LAW cvar_step_reads_only_keys: a press reply that is not the error form answers exactly a
# spelled key within the wire, with the spelled expansion of its press
# EXCLUDES: a key read with leading zeros, past the wire or with input left
#   over, and answered anyway
law cvar_step_reads_only_keys:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for +s: String
  for ok: {LawsBase.wire_opens_err(cvar_reply_of(FCv.step(FCv.Table{bs, as}, s))) == False{} : Bool}
  exs k: Nat
  {(s, (LawsBase.wire_fits(k), cvar_reply_of(FCv.step(FCv.Table{bs, as}, s)))) == (Wr.put_nat(k, ""), (True{}, cvar_spell_exp(Cv.press(bs, k, as), ""))) : String & (Bool & String)}

# LAW cvar_step_malformed_unless_key: every press reply but the error form "cvar: malformed
# key" reads an input that begins with a spelled key within the wire
# EXCLUDES: the left-over error or an expansion for input that holds no
#   key, the malformed error spelled with another text
law cvar_step_malformed_unless_key:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for +s: String
  for other: {String.eq(cvar_reply_of(FCv.step(FCv.Table{bs, as}, s)), Wr.err("cvar: malformed key")) == False{} : Bool}
  exs k: Nat
  exs rest: String
  {(s, LawsBase.wire_fits(k)) == (Wr.put_nat(k, rest), True{}) : String & Bool}

# LAW cvar_tags_example: anchor: the bytes Rust sends and reads: alias 0 = [toggle 3], then
# [toggle 0, run 0] is flat [toggle 0, toggle 3]; alias 0 = [run 0] run is a cycle at 0; a run
# of a missing alias and a gone command name it; sets of a Bool and a Nat pass through; a
# command tag 4, a value tag 2, input left over are refused. The table key 0 = [run 0], alias 0
# = [toggle 1] opens with the empty reply; key 0 runs toggle 1, key 1 nothing; a key with
# input left over, a key that is no number, a short or left-over table, a press after a
# refused open get their error forms
# EXCLUDES: a tag table both sides of the Bend entry agree on but Rust does
#   not, an unknown tag read as a known one, an error text swapped
law cvar_tags_example:
  {[FCv.ffi("1,0,1,1,3,2,1,0,2,0,"), FCv.ffi("1,0,1,2,0,1,2,0,"), FCv.ffi("0,1,2,0,"), FCv.ffi("0,1,3,5,"), FCv.ffi("0,2,0,4,1,T0,9,0,7,"), FCv.ffi("0,1,4,0,"), FCv.ffi("0,1,0,4,2,0,"), FCv.ffi("0,0,x")] == ["0,2,1,0,1,3,", "1,0,", "2,0,", "2,5,", "0,2,0,4,1,T0,9,0,7,", Wr.err("cvar: malformed expand request"), Wr.err("cvar: malformed expand request"), Wr.err("cvar: input left over")] : List<&2, String>} &
  {FCv.open("1,0,1,2,0,1,0,1,1,1,") == (FCv.Table{[Cv.KeyBind{0n, [Cv.CRun{0n}]}], [Cv.Alias{0n, [Cv.CToggle{1n}]}]}, "") : FCv.St & String} &
  {[cvar_reply_of(FCv.step(cvar_st_of(FCv.open("1,0,1,2,0,1,0,1,1,1,")), "0,")), cvar_reply_of(FCv.step(cvar_st_of(FCv.open("1,0,1,2,0,1,0,1,1,1,")), "1,")), cvar_reply_of(FCv.step(cvar_st_of(FCv.open("1,0,1,2,0,1,0,1,1,1,")), "0,x")), cvar_reply_of(FCv.step(cvar_st_of(FCv.open("1,0,1,2,0,1,0,1,1,1,")), "x")), cvar_reply_of(FCv.open("1,")), cvar_reply_of(FCv.open("1,0,1,2,0,1,0,1,1,1,x")), cvar_reply_of(FCv.step(cvar_st_of(FCv.open("1,")), "0,"))] == ["0,1,1,1,", "0,0,", Wr.err("cvar: input left over"), Wr.err("cvar: malformed key"), Wr.err("cvar: malformed press table"), Wr.err("cvar: input left over"), Wr.err("cvar: the press table was refused")] : List<&2, String>}

def spec_body.pick(hit: Bool, b: List<&2, Cv.Cmd>, r: List<&2, Cv.Cmd>) -> List<&2, Cv.Cmd>:
  match hit:
    case True{}:
      b
    case False{}:
      r

# the body of the first alias named n, else the run of a missing alias
def spec_body_orig(as: List<&2, Cv.Alias>, +n: Nat) -> List<&2, Cv.Cmd>:
  match as:
    case Nil{}:
      [Cv.CGone{n}]
    case Cv.Alias{m, b} <> rest:
      spec_body.pick(Nat.is_eq(m, n), b, spec_body_orig(rest, n))

# cs expanded with d levels of alias nesting left: a command that runs no
# alias stays; a run runs the alias's body one level deeper, or is a cycle
# with no level left; a run of a missing alias is unknown; the commands of
# the parts in order, the first error stopping the rest (cvar_cat)
def spec_expand.go(d: Nat, cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>) -> Cv.Exp:
  match d:
    case 0n:
      match cs:
        case Nil{}:
          Cv.Flat{Nil{}}
        case c <> rest:
          match c:
            case Cv.CSet{i, v}:
              CvarModel.cvar_cat(Cv.Flat{[Cv.CSet{i, v}]}, spec_expand.go(0n, rest, as))
            case Cv.CToggle{i}:
              CvarModel.cvar_cat(Cv.Flat{[Cv.CToggle{i}]}, spec_expand.go(0n, rest, as))
            case Cv.CRun{n}:
              Cv.Cycle{n}
            case Cv.CGone{n}:
              Cv.Unknown{n}
    case 1n+(+e):
      match cs:
        case Nil{}:
          Cv.Flat{Nil{}}
        case c <> rest:
          match c:
            case Cv.CSet{i, v}:
              CvarModel.cvar_cat(Cv.Flat{[Cv.CSet{i, v}]}, spec_expand.go(1n+e, rest, as))
            case Cv.CToggle{i}:
              CvarModel.cvar_cat(Cv.Flat{[Cv.CToggle{i}]}, spec_expand.go(1n+e, rest, as))
            case Cv.CRun{+n}:
              CvarModel.cvar_cat(spec_expand.go(e, spec_body_orig(as, n), as), spec_expand.go(1n+e, rest, as))
            case Cv.CGone{n}:
              Cv.Unknown{n}

# cs expanded with the table as: the top level and one level per alias
def spec_expand(cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>) -> Cv.Exp:
  spec_expand.go(1n+List.length(&2, Cv.Alias, as), cs, as)

# LAW alias_expand_exact: every expansion is the spec's: a command that runs no alias stays, a run runs the body of the first alias of its name one nesting level deeper, a nest deeper than the table is a cycle named by the run at which it ran out, a run of a missing alias is unknown, and the first error, left to right, is the outcome; the body of an alias is the first one's of its name, else the run of a missing alias
# EXCLUDES: a command lost, added, reordered or changed, a cycle or an
#   unknown alias reported otherwise, a nesting bound other than the
#   table's size, a later alias of a name used
law alias_expand_exact:
  for +cs: List<&2, Cv.Cmd>
  for +as: List<&2, Cv.Alias>
  for +n: Nat
  {Cv.expand(cs, as) == spec_expand(cs, as) : Cv.Exp} & {Cv.body(as, n) == spec_body_orig(as, n) : List<&2, Cv.Cmd>}

def spec_bound.pick(hit: Bool, c: List<&2, Cv.Cmd>, r: List<&2, Cv.Cmd>) -> List<&2, Cv.Cmd>:
  match hit:
    case True{}:
      c
    case False{}:
      r

# the commands of the first bind of key k, else none
def spec_bound(bs: List<&2, Cv.KeyBind>, +k: Nat) -> List<&2, Cv.Cmd>:
  match bs:
    case Nil{}:
      Nil{}
    case Cv.KeyBind{j, c} <> rest:
      spec_bound.pick(Nat.is_eq(j, k), c, spec_bound(rest, k))

# a press of key k: its commands expanded with the table as
def spec_press(+bs: List<&2, Cv.KeyBind>, +k: Nat, +as: List<&2, Cv.Alias>) -> Cv.Exp:
  spec_expand(spec_bound(bs, k), as)

# LAW bind_press_exact: every press of a key is the spec's: the commands of the key's first bind (none for an unbound key), expanded
# EXCLUDES: a later bind of a key used, a bind of another key run, an
#   unbound key that runs anything
law bind_press_exact:
  for +bs: List<&2, Cv.KeyBind>
  for +k: Nat
  for +as: List<&2, Cv.Alias>
  {Cv.press(bs, k, as) == spec_press(bs, k, as) : Cv.Exp} & {Cv.bound(bs, k) == spec_bound(bs, k) : List<&2, Cv.Cmd>}
