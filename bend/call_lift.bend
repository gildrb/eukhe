# call_lift: a stored tool call lifted to the current dialect of its
# family (omp² lesson 8, "version everything the model sees"). Every tool
# result's details carry the call's `family@rev`; when a transcript is
# replayed into a model request, a call stamped with an older rev of a
# family is lifted, step by step, to the family's current rev, so a
# history read by another model, or after a resume or a fork, speaks one
# dialect. Entry: bend/ffi_call_lift.bend (Rust: eukhe-bend
# rules/call_lift.rs, applied by eukhe-durable harness/lift.rs when the
# context orders a transcript's tool results). Laws: laws/call_lift.bend.
#
# The lift reads only the names of a call's arguments, never their values:
# Rust keeps each value and places it where the answer says.
#
# - A family absent from the table: unknown, the call is untouched.
# - A call at the family's current rev: current, the call is untouched.
# - Otherwise the steps from the call's rev are followed (the first step
#   leaving each rev, at most one step per step of the family, so a cycle
#   ends) until one arrives at the current rev; their ops, in order, map
#   the arguments, and the call takes the current rev. A rev no chain
#   lifts to the current one is stranded: the call is kept as stored.
# - Rename{from, to}: the first argument named `from` is named `to`, with
#   a renamed receipt; when `to` is taken, nothing moves and a clashed
#   receipt says so; no `from`, nothing.
# - Fill{key, json}: a missing `key` is added with the value `json`, with
#   a filled receipt; a present one is kept.
# No argument is ever dropped: every argument of the stored call comes
# back once, in its place (Kept, by index), added ones after them.
#
# Pure: no IO, no @unsafe.

import Base

# Types
# -----

# an argument change of one revision step
type Op is Data:
  Rename{from: String, to: String}
  Fill{key: String, json: String}

# one revision step of a family: from rev `from` to rev `to`
type Step is Data:
  Step{from: String, to: String, ops: List<&2, Op>}

# a family: its name, its current rev, its steps
type Fam is Data:
  Fam{name: String, current: String, steps: List<&2, Step>}

# a stored call: its family and rev (its stamp `family@rev`), its argument
# names in order
type Call is Data:
  Call{family: String, rev: String, keys: List<&2, String>}

# an argument of a lifted call: the stored argument at `index` under
# `key`, or one a step added
type Arg is Data:
  Kept{index: Nat, key: String}
  Added{key: String, json: String}

# what a step did to the arguments
type Receipt is Data:
  Renamed{from: String, to: String}
  Clashed{from: String, to: String}
  Filled{key: String}

# the lift of a call
type Lift is Data:
  Unknown{}
  Current{}
  Stranded{}
  Lifted{rev: String, args: List<&2, Arg>, receipts: List<&2, Receipt>}

# the arguments and receipts while the ops of a path apply
type St is Data:
  St{args: List<&2, Arg>, receipts: List<&2, Receipt>}

# The shipped table
# -----------------

# Every family a eukhe tool stamps, at its current rev. A rev bump adds
# the step from the old rev here (and its ops when the argument shape
# changed). zoom@1 -> zoom@2 (9695afec6): `id` may also name an agent
# and `n` became optional, so every zoom@1 call is a zoom@2 call as
# stored.
def table() -> List<&2, Fam>:
  [Fam{"bash", "1", []}, Fam{"read", "1", []}, Fam{"write", "1", []}, Fam{"edit", "hl.1", []}, Fam{"grep", "1", []}, Fam{"glob", "1", []}, Fam{"python", "1", []}, Fam{"dyn", "1", []}, Fam{"zoom", "2", [Step{"1", "2", []}]}, Fam{"date", "1", []}, Fam{"remote", "1", []}]

# Lookups
# -------

def fam_of.pick(hit: Bool, x: Fam, rest: Maybe<&2, Fam>) -> Maybe<&2, Fam>:
  match hit:
    case True{}:
      Some{x}
    case False{}:
      rest

# the first family of the table named f
def fam_of(t: List<&2, Fam>, +f: String) -> Maybe<&2, Fam>:
  match t:
    case Nil{}:
      None{}
    case Con{x, rest}:
      match x:
        case Fam{+n, c, s}:
          fam_of.pick(String.eq(n, f), Fam{n, c, s}, fam_of(rest, f))

def step_of.pick(hit: Bool, x: Step, rest: Maybe<&2, Step>) -> Maybe<&2, Step>:
  match hit:
    case True{}:
      Some{x}
    case False{}:
      rest

# the first step leaving rev r
def step_of(ss: List<&2, Step>, +r: String) -> Maybe<&2, Step>:
  match ss:
    case Nil{}:
      None{}
    case Con{x, rest}:
      match x:
        case Step{+a, b, o}:
          step_of.pick(String.eq(a, r), Step{a, b, o}, step_of(rest, r))

# The path
# --------

def walk.join(ops: List<&2, Op>, arrived: Bool, rest: Maybe<&2, List<&2, Op>>) -> Maybe<&2, List<&2, Op>>:
  match arrived:
    case True{}:
      Some{ops}
    case False{}:
      match rest:
        case None{}:
          None{}
        case Some{more}:
          Some{List.append(&2, Op, ops, more)}

# the ops from the step found to the current rev cur, at most fuel steps;
# none when no chain arrives
def walk(fuel: Nat, +ss: List<&2, Step>, +cur: String, found: Maybe<&2, Step>) -> Maybe<&2, List<&2, Op>>:
  match fuel:
    case 0n:
      None{}
    case 1n+f:
      match found:
        case None{}:
          None{}
        case Some{st}:
          match st:
            case Step{a, +b, o}:
              walk.join(o, String.eq(b, cur), walk(f, ss, cur, step_of(ss, b)))

# The ops
# -------

def arg_key(a: Arg) -> String:
  match a:
    case Kept{i, k}:
      k
    case Added{k, j}:
      k

def arg_named(a: Arg, k: String) -> Arg:
  match a:
    case Kept{i, o}:
      Kept{i, k}
    case Added{o, j}:
      Added{k, j}

# some argument is named k
def has(args: List<&2, Arg>, +k: String) -> Bool:
  match args:
    case Nil{}:
      False{}
    case Con{+a, rest}:
      Bool.or(String.eq(arg_key(a), k), has(rest, k))

def rename.at(hit: Bool, a: Arg, rest: List<&2, Arg>, renamed: List<&2, Arg>, to: String) -> List<&2, Arg>:
  match hit:
    case True{}:
      Con{arg_named(a, to), rest}
    case False{}:
      Con{a, renamed}

# the first argument named from, named to
def rename(args: List<&2, Arg>, +from: String, +to: String) -> List<&2, Arg>:
  match args:
    case Nil{}:
      Nil{}
    case Con{+a, +rest}:
      rename.at(String.eq(arg_key(a), from), a, rest, rename(rest, from, to), to)

def apply_op.rename(present: Bool, taken: Bool, +from: String, +to: String, +args: List<&2, Arg>, rs: List<&2, Receipt>) -> St:
  match present:
    case False{}:
      St{args, rs}
    case True{}:
      match taken:
        case True{}:
          St{args, List.append(&2, Receipt, rs, [Clashed{from, to}])}
        case False{}:
          St{rename(args, from, to), List.append(&2, Receipt, rs, [Renamed{from, to}])}

def apply_op.fill(present: Bool, +key: String, json: String, args: List<&2, Arg>, rs: List<&2, Receipt>) -> St:
  match present:
    case True{}:
      St{args, rs}
    case False{}:
      St{List.append(&2, Arg, args, [Added{key, json}]), List.append(&2, Receipt, rs, [Filled{key}])}

def apply_op(op: Op, st: St) -> St:
  match op:
    case Rename{+from, +to}:
      match st:
        case St{+args, rs}:
          apply_op.rename(has(args, from), has(args, to), from, to, args, rs)
    case Fill{+key, json}:
      match st:
        case St{+args, rs}:
          apply_op.fill(has(args, key), key, json, args, rs)

# the ops, in order
def apply_ops(ops: List<&2, Op>, st: St) -> St:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      apply_ops(rest, apply_op(op, st))

# the stored arguments, each kept at its index from i
def kept(ks: List<&2, String>, +i: Nat) -> List<&2, Arg>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{k, rest}:
      Con{Kept{i, k}, kept(rest, 1n+i)}

# The lift
# --------

def lift.done(cur: String, st: St) -> Lift:
  match st:
    case St{a, rs}:
      Lifted{cur, a, rs}

def lift.path(cur: String, ks: List<&2, String>, path: Maybe<&2, List<&2, Op>>) -> Lift:
  match path:
    case None{}:
      Stranded{}
    case Some{ops}:
      lift.done(cur, apply_ops(ops, St{kept(ks, 0n), []}))

def lift.at(at: Bool, cur: String, ks: List<&2, String>, path: Maybe<&2, List<&2, Op>>) -> Lift:
  match at:
    case True{}:
      Current{}
    case False{}:
      lift.path(cur, ks, path)

def lift.fam(+r: String, ks: List<&2, String>, m: Maybe<&2, Fam>) -> Lift:
  match m:
    case None{}:
      Unknown{}
    case Some{x}:
      match x:
        case Fam{n, +cur, +ss}:
          lift.at(String.eq(r, cur), cur, ks, walk(List.length(&2, Step, ss), ss, cur, step_of(ss, r)))

# the lift of call c by table t
def lift(t: List<&2, Fam>, c: Call) -> Lift:
  match c:
    case Call{f, r, ks}:
      lift.fam(r, ks, fam_of(t, f))
