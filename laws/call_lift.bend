# eukhe: the laws of area call_lift

import Base
import ../bend/call_lift.bend as Cl
import ../bend/ffi_call_lift.bend as FCl
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ../spec/harness/lift_wire.bend as SpW
import ../spec/harness/lift.bend as Sp

# (H1) Stored calls lifted to the current dialect
# -----------------------------------------------
# bend/call_lift.bend, run as the compiled core by bend/ffi_call_lift.bend
# (eukhe-bend rules/call_lift.rs; asked by eukhe-durable harness/lift.rs
# for the stamped calls of every transcript the context orders, so every
# model request, after a resume, a fork or a model switch, sends the
# calls in their families' current dialects). spec/harness/lift_wire.bend
# spells the entry's wire (W1, W2) with the wire's writers only. Every
# input is free: any table, family, call, argument list and string, unless
# a law names the shipped table, Cl.table().
#
# R1: a call's family is the first of the table with its name. From the
#     call's rev the family's steps are followed, each the first step
#     leaving the rev the last one arrived at, until one arrives at the
#     family's current rev; the ops of those steps, in order, change the
#     stored arguments (each kept at its index, in order), and the call
#     takes the current rev. A rename moves the first argument named
#     `from` to `to` when no argument is named `to` (receipt renamed),
#     else moves nothing (receipt clashed), and does nothing without a
#     `from`; a fill adds a missing name after the others (receipt
#     filled) and leaves a present one. A rev no step leaves is stranded:
#     the call is kept as stored.
# R2: a rev whose chain arrives at the current rev (in at most as many
#     steps as the family has) ends at the current rev: nothing known is
#     left behind or stranded. In the shipped table every rev a step
#     leaves arrives.
# R3: a lift is idempotent: the call it leaves lifts as current, or as
#     before when it was left untouched.
# R4: a call at its family's current rev, and a call of a family the
#     table lacks, are untouched. The shipped table's families are exactly
#     the stamps the eukhe tools write in their results, at those revs.
# R5: no argument is lost: every stored argument comes back once, in its
#     order, and a lift adds exactly as many arguments as it has filled
#     receipts (a later rename may rename an added argument, so the names
#     of the added arguments and of the filled receipts need not pair).
# R6: replay is byte-stable call by call: a call's lift depends on that
#     call and the table alone (Cl.lift takes one call), and the entry's
#     reply is the count of the calls, then each call's lift spelled by
#     itself, in the order of the calls (R7). The bytes the provider's
#     prefix cache sees are built by Rust (eukhe-durable harness/lift.rs),
#     which no law here reaches.
# R7: the entry answers each request Rust writes (W1, every count and
#     name within the wire) with the spelling (W2) of the lifts by the
#     shipped table, and any input that is not exactly one request
#     with exactly `E call_lift: malformed request`.

# Terms
# -----

# no family of t is named f
def names_lack(t: List<&2, Cl.Fam>, +f: String) -> Bool:
  match t:
    case Nil{}:
      True{}
    case Con{x, rest}:
      match x:
        case Cl.Fam{+n, c, s}:
          Bool.and(Bool.not(String.eq(n, f)), names_lack(rest, f))

# no two families of t share a name
def names_distinct(t: List<&2, Cl.Fam>) -> Bool:
  match t:
    case Nil{}:
      True{}
    case Con{x, +rest}:
      match x:
        case Cl.Fam{+n, c, s}:
          Bool.and(names_lack(rest, n), names_distinct(rest))

# no step of ss leaves rev x
def leaves_none(ss: List<&2, Cl.Step>, +x: String) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{s, rest}:
      match s:
        case Cl.Step{+a, b, o}:
          Bool.and(Bool.not(String.eq(a, x)), leaves_none(rest, x))

# the step m, when there is one, arrives at rev y
def goes_to(m: Maybe<&2, Cl.Step>, +y: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{s}:
      match s:
        case Cl.Step{a, +b, o}:
          String.eq(b, y)

# after a rev of the chain: the current rev ends it (nothing after it),
# any other rev goes on (ih: the rest is a chain from it)
def chain_ok.after(at: Bool, more: List<&2, String>, ih: Bool) -> Bool:
  match at:
    case True{}:
      match more:
        case Nil{}:
          True{}
        case Con{z, rest}:
          False{}
    case False{}:
      ih

# ys is a chain of revs from rev x to the current rev cur: the step the
# family takes from x (Cl.step_of, the first step leaving x:
# call_lift_first_step) arrives at the first rev of ys, the step it takes
# from there at the next, and so on; the last rev of ys is cur and no
# earlier one is
def chain_ok(ys: List<&2, String>, +ss: List<&2, Cl.Step>, +x: String, +cur: String) -> Bool:
  match ys:
    case Nil{}:
      False{}
    case Con{+y, +more}:
      Bool.and(goes_to(Cl.step_of(ss, x), y), chain_ok.after(String.eq(y, cur), more, chain_ok(more, ss, y, cur)))

# ys has at most n revs
def at_most(ys: List<&2, String>, n: Nat) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{y, more}:
      match n:
        case 0n:
          False{}
        case 1n+m:
          at_most(more, m)

# the ops of the step m, when there is one
def ops_at(m: Maybe<&2, Cl.Step>) -> List<&2, Cl.Op>:
  match m:
    case None{}:
      Nil{}
    case Some{s}:
      match s:
        case Cl.Step{a, b, o}:
          o

# the ops of the steps of the chain ys from x, in the chain's order
def chain_ops(ys: List<&2, String>, +ss: List<&2, Cl.Step>, +x: String) -> List<&2, Cl.Op>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{+y, more}:
      List.append(&2, Cl.Op, ops_at(Cl.step_of(ss, x)), chain_ops(more, ss, y))

# the stored argument names ks, each kept at its index, from i
def stored(ks: List<&2, String>, +i: Nat) -> List<&2, Cl.Arg>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{k, rest}:
      Cl.Kept{i, k} <> stored(rest, 1n+i)

# a call lifted to rev cur with the arguments and receipts of st
def lifted_as(cur: String, st: Cl.St) -> Cl.Lift:
  match st:
    case Cl.St{a, rs}:
      Cl.Lifted{cur, a, rs}

# the name of an argument
def key_of(a: Cl.Arg) -> String:
  match a:
    case Cl.Kept{i, k}:
      k
    case Cl.Added{k, j}:
      k

# the names of the arguments, in order
def keys_of(a: List<&2, Cl.Arg>) -> List<&2, String>:
  match a:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      key_of(x) <> keys_of(rest)

# no name of ks is k
def lacks(ks: List<&2, String>, +k: String) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Bool.not(String.eq(x, k)), lacks(rest, k))

# the argument a under the name k: its stored index, or its added value,
# unchanged
def renamed(a: Cl.Arg, k: String) -> Cl.Arg:
  match a:
    case Cl.Kept{i, o}:
      Cl.Kept{i, k}
    case Cl.Added{o, j}:
      Cl.Added{k, j}

# the call a lift leaves: its family at the lifted rev with the lifted
# argument names, or the call as stored
def applied.l(f: String, r: String, ks: List<&2, String>, l: Cl.Lift) -> Cl.Call:
  match l:
    case Cl.Unknown{}:
      Cl.Call{f, r, ks}
    case Cl.Current{}:
      Cl.Call{f, r, ks}
    case Cl.Stranded{}:
      Cl.Call{f, r, ks}
    case Cl.Lifted{rev, a, rs}:
      Cl.Call{f, rev, keys_of(a)}

def applied(c: Cl.Call, l: Cl.Lift) -> Cl.Call:
  match c:
    case Cl.Call{f, r, ks}:
      applied.l(f, r, ks, l)

# what a second lift of the applied call answers: a lifted call is current
def settled(l: Cl.Lift) -> Cl.Lift:
  match l:
    case Cl.Unknown{}:
      Cl.Unknown{}
    case Cl.Current{}:
      Cl.Current{}
    case Cl.Stranded{}:
      Cl.Stranded{}
    case Cl.Lifted{rev, a, rs}:
      Cl.Current{}

# the stored indices, in order, of the kept arguments
def kept_indices(a: List<&2, Cl.Arg>) -> List<&2, Nat>:
  match a:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      match x:
        case Cl.Kept{i, k}:
          i <> kept_indices(rest)
        case Cl.Added{k, j}:
          kept_indices(rest)

# the indices i, i+1, ... of the names ks
def upto(ks: List<&2, String>, +i: Nat) -> List<&2, Nat>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{k, rest}:
      i <> upto(rest, 1n+i)

# the stored indices a lift keeps: those of its arguments, every one of a
# call kept as stored
def kept_of(ks: List<&2, String>, l: Cl.Lift) -> List<&2, Nat>:
  match l:
    case Cl.Unknown{}:
      upto(ks, 0n)
    case Cl.Current{}:
      upto(ks, 0n)
    case Cl.Stranded{}:
      upto(ks, 0n)
    case Cl.Lifted{rev, a, rs}:
      kept_indices(a)

def added_count(a: List<&2, Cl.Arg>) -> Nat:
  match a:
    case Nil{}:
      0n
    case Con{x, rest}:
      match x:
        case Cl.Kept{i, k}:
          added_count(rest)
        case Cl.Added{k, j}:
          1n+added_count(rest)

def filled_count(rs: List<&2, Cl.Receipt>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case Con{x, rest}:
      match x:
        case Cl.Renamed{a, b}:
          filled_count(rest)
        case Cl.Clashed{a, b}:
          filled_count(rest)
        case Cl.Filled{k}:
          1n+filled_count(rest)

# how many arguments a lift added, and how many filled receipts it has
def added_of(l: Cl.Lift) -> Nat:
  match l:
    case Cl.Unknown{}:
      0n
    case Cl.Current{}:
      0n
    case Cl.Stranded{}:
      0n
    case Cl.Lifted{rev, a, rs}:
      added_count(a)

def filled_of(l: Cl.Lift) -> Nat:
  match l:
    case Cl.Unknown{}:
      0n
    case Cl.Current{}:
      0n
    case Cl.Stranded{}:
      0n
    case Cl.Lifted{rev, a, rs}:
      filled_count(rs)

# Laws: the lift (R1-R5)
# ----------------------

# LAW call_lift_first_step (R1): in steps whose first steps (pre) leave no
# rev x, the step a call at x takes is the first step leaving x, whatever
# follows it
# EXCLUDES: a step taken from another rev, a later step leaving x taken
#   over the first, no step found where one leaves x
law call_lift_first_step:
  for +pre: List<&2, Cl.Step>
  for post: List<&2, Cl.Step>
  for +x: String
  for +b: String
  for +o: List<&2, Cl.Op>
  for before: {leaves_none(pre, x) == True{} : Bool}
  {Cl.step_of(List.append(&2, Cl.Step, pre, Cl.Step{x, b, o} <> post), x) == Some{Cl.Step{x, b, o}} : Maybe<&2, Cl.Step>}

# LAW call_lift_reaches_current (R1, R2): a call of family f, in a table
# whose families before the first f (pre) are named otherwise, at a rev r
# other than the current rev cur, whose steps ss carry it from r to cur
# along a chain of revs ys (chain_ok) of at most as many steps as ss has,
# is lifted to cur with the arguments and receipts the chain's ops leave,
# applied in the chain's order to the stored arguments, each kept at its
# index
# EXCLUDES: a known old rev stranded, a lift that stops one step short or
#   runs past the current rev, a lifted call stamped with an intermediate
#   rev, ops of a step left out or applied out of order, a family found
#   by a later row
law call_lift_reaches_current:
  for +pre: List<&2, Cl.Fam>
  for post: List<&2, Cl.Fam>
  for +f: String
  for +cur: String
  for +ss: List<&2, Cl.Step>
  for +r: String
  for +ks: List<&2, String>
  for +ys: List<&2, String>
  for first: {names_lack(pre, f) == True{} : Bool}
  for old: {String.eq(r, cur) == False{} : Bool}
  for chain: {chain_ok(ys, ss, r, cur) == True{} : Bool}
  for short: {at_most(ys, List.length(&2, Cl.Step, ss)) == True{} : Bool}
  {Cl.lift(List.append(&2, Cl.Fam, pre, Cl.Fam{f, cur, ss} <> post), Cl.Call{f, r, ks}) == lifted_as(cur, Cl.apply_ops(chain_ops(ys, ss, r), Cl.St{stored(ks, 0n), []})) : Cl.Lift}

# LAW call_lift_stranded (R1): a call of family f (the first f of the
# table) at a rev r other than its current rev, with no step leaving r,
# is stranded, whatever its arguments
# EXCLUDES: a call at a rev no step leaves lifted anyway (stamped with the
#   current rev, its arguments unmapped), answered as current or unknown
law call_lift_stranded:
  for +pre: List<&2, Cl.Fam>
  for post: List<&2, Cl.Fam>
  for +f: String
  for +cur: String
  for +ss: List<&2, Cl.Step>
  for +r: String
  for ks: List<&2, String>
  for first: {names_lack(pre, f) == True{} : Bool}
  for old: {String.eq(r, cur) == False{} : Bool}
  for none: {leaves_none(ss, r) == True{} : Bool}
  {Cl.lift(List.append(&2, Cl.Fam, pre, Cl.Fam{f, cur, ss} <> post), Cl.Call{f, r, ks}) == Cl.Stranded{} : Cl.Lift}

# LAW call_lift_current_is_identity (R4): a call at the current rev of its
# family (the first of the table with its name) is current, whatever its
# arguments and the family's steps
# EXCLUDES: a current call rewritten (its arguments renamed, filled or
#   reordered), a current call stamped again, a step leaving the current
#   rev taken
law call_lift_current_is_identity:
  for +pre: List<&2, Cl.Fam>
  for post: List<&2, Cl.Fam>
  for +f: String
  for +r: String
  for ss: List<&2, Cl.Step>
  for ks: List<&2, String>
  for first: {names_lack(pre, f) == True{} : Bool}
  {Cl.lift(List.append(&2, Cl.Fam, pre, Cl.Fam{f, r, ss} <> post), Cl.Call{f, r, ks}) == Cl.Current{} : Cl.Lift}

# LAW call_lift_unknown_family_untouched (R4): a call of a family no row
# of the table names is unknown, whatever its rev and arguments
# EXCLUDES: a foreign tool's call (an MCP tool, a plugin) rewritten or
#   stamped by another family's steps
law call_lift_unknown_family_untouched:
  for +t: List<&2, Cl.Fam>
  for +f: String
  for r: String
  for ks: List<&2, String>
  for no: {names_lack(t, f) == True{} : Bool}
  {Cl.lift(t, Cl.Call{f, r, ks}) == Cl.Unknown{} : Cl.Lift}

# LAW call_lift_rename_moves (R1): a rename of `from` to `to`, on arguments
# whose first one named `from` is x (none before it, pre, is) and none
# named `to`, names x `to` in its place (its index or value unchanged),
# keeps every other argument where it is, and appends a renamed receipt
# EXCLUDES: every argument named `from` renamed, a later one renamed, the
#   renamed argument moved, dropped or given another index or value, a
#   rename without its receipt
law call_lift_rename_moves:
  for +pre: List<&2, Cl.Arg>
  for +x: Cl.Arg
  for +post: List<&2, Cl.Arg>
  for +from: String
  for +to: String
  for +rs: List<&2, Cl.Receipt>
  for named: {key_of(x) == from : String}
  for before: {lacks(keys_of(pre), from) == True{} : Bool}
  for free: {lacks(keys_of(List.append(&2, Cl.Arg, pre, x <> post)), to) == True{} : Bool}
  {Cl.apply_op(Cl.Rename{from, to}, Cl.St{List.append(&2, Cl.Arg, pre, x <> post), rs}) == Cl.St{List.append(&2, Cl.Arg, pre, renamed(x, to) <> post), List.append(&2, Cl.Receipt, rs, [Cl.Renamed{from, to}])} : Cl.St}

# LAW call_lift_rename_clashes (R1): a rename of `from` to `to` when some
# argument is named `from` and some is named `to` moves nothing and
# appends a clashed receipt
# EXCLUDES: a rename onto a taken name (two arguments under one name, or
#   the other one overwritten), a clash without its receipt
law call_lift_rename_clashes:
  for +args: List<&2, Cl.Arg>
  for +from: String
  for +to: String
  for +rs: List<&2, Cl.Receipt>
  for present: {lacks(keys_of(args), from) == False{} : Bool}
  for taken: {lacks(keys_of(args), to) == False{} : Bool}
  {Cl.apply_op(Cl.Rename{from, to}, Cl.St{args, rs}) == Cl.St{args, List.append(&2, Cl.Receipt, rs, [Cl.Clashed{from, to}])} : Cl.St}

# LAW call_lift_rename_absent (R1): a rename of `from` when no argument is
# named `from` changes nothing and adds no receipt
# EXCLUDES: an argument invented under `to`, a receipt for a rename that
#   did not happen
law call_lift_rename_absent:
  for +args: List<&2, Cl.Arg>
  for +from: String
  for +to: String
  for +rs: List<&2, Cl.Receipt>
  for absent: {lacks(keys_of(args), from) == True{} : Bool}
  {Cl.apply_op(Cl.Rename{from, to}, Cl.St{args, rs}) == Cl.St{args, rs} : Cl.St}

# LAW call_lift_fill_adds (R1): a fill of a name no argument has appends
# that argument, added with the fill's JSON value, after all the others,
# and appends a filled receipt
# EXCLUDES: a fill dropped, put before a stored argument or given another
#   value, a fill without its receipt
law call_lift_fill_adds:
  for +args: List<&2, Cl.Arg>
  for +key: String
  for +json: String
  for +rs: List<&2, Cl.Receipt>
  for absent: {lacks(keys_of(args), key) == True{} : Bool}
  {Cl.apply_op(Cl.Fill{key, json}, Cl.St{args, rs}) == Cl.St{List.append(&2, Cl.Arg, args, [Cl.Added{key, json}]), List.append(&2, Cl.Receipt, rs, [Cl.Filled{key}])} : Cl.St}

# LAW call_lift_fill_present (R1): a fill of a name some argument has
# changes nothing and adds no receipt
# EXCLUDES: a present argument overwritten by the fill's default or
#   duplicated, a receipt for a fill that did not happen
law call_lift_fill_present:
  for +args: List<&2, Cl.Arg>
  for +key: String
  for json: String
  for +rs: List<&2, Cl.Receipt>
  for present: {lacks(keys_of(args), key) == False{} : Bool}
  {Cl.apply_op(Cl.Fill{key, json}, Cl.St{args, rs}) == Cl.St{args, rs} : Cl.St}

# LAW call_lift_ops_in_order (R1): ops apply one after another in their
# order: no ops change nothing, one op is that op, and the ops os1 then
# os2 are os2 applied to what os1 leaves
# EXCLUDES: ops applied in reverse or all to the stored arguments, an op
#   skipped or applied twice
law call_lift_ops_in_order:
  for +os1: List<&2, Cl.Op>
  for +os2: List<&2, Cl.Op>
  for +o: Cl.Op
  for +st: Cl.St
  {Cl.apply_ops([], st) == st : Cl.St} & {Cl.apply_ops([o], st) == Cl.apply_op(o, st) : Cl.St} & {Cl.apply_ops(List.append(&2, Cl.Op, os1, os2), st) == Cl.apply_ops(os2, Cl.apply_ops(os1, st)) : Cl.St}

# LAW call_lift_idempotent (R3): the call a lift leaves lifts as current
# (or as before, when the lift left it untouched)
# EXCLUDES: a lifted call lifted again on the next replay (the ops applied
#   twice), a lift that changes its answer between replays
law call_lift_idempotent:
  for +t: List<&2, Cl.Fam>
  for +c: Cl.Call
  {Cl.lift(t, applied(c, Cl.lift(t, c))) == settled(Cl.lift(t, c)) : Cl.Lift}

# LAW call_lift_preserves_unmapped (R5): every stored argument comes back
# once, in order (renamed or not), and a lift adds exactly as many
# arguments as it has filled receipts (their count, not their names: a
# later rename may rename an added argument)
# EXCLUDES: an argument the table does not name dropped, duplicated or
#   moved, a rename that drops the argument it renames, a fill without a
#   receipt or a receipt without a fill
law call_lift_preserves_unmapped:
  for +t: List<&2, Cl.Fam>
  for +f: String
  for +r: String
  for +ks: List<&2, String>
  {kept_of(ks, Cl.lift(t, Cl.Call{f, r, ks})) == upto(ks, 0n) : List<&2, Nat>} & {added_of(Cl.lift(t, Cl.Call{f, r, ks})) == filled_of(Cl.lift(t, Cl.Call{f, r, ks})) : Nat}

# Laws: the shipped table (R2, R4)
# -------------------------------

# The stamps `family@rev` the eukhe tools write in their results' details:
# bash@1 (crates/eukhe-core/src/durable/shell.rs:60); read@1, write@1,
# edit@hl.1, grep@1, glob@1 (crates/eukhe-core/src/durable/documents/
# contract.rs:70-74); ipython@1 (crates/eukhe-core/src/durable/rlm/
# tool.rs:87); dyn@1 (crates/eukhe-core/src/durable/tool_surface/
# mod.rs:42); zoom@2, date@1 (crates/eukhe-core/src/durable/optchat/
# tools.rs:28-29); remote@1 (crates/eukhe-core/src/durable/rlm/
# remote.rs:33). Each as a call at that rev with no arguments.
def rust_stamps() -> List<&2, Cl.Call>:
  [Cl.Call{"bash", "1", []}, Cl.Call{"read", "1", []}, Cl.Call{"write", "1", []}, Cl.Call{"edit", "hl.1", []}, Cl.Call{"grep", "1", []}, Cl.Call{"glob", "1", []}, Cl.Call{"ipython", "1", []}, Cl.Call{"dyn", "1", []}, Cl.Call{"zoom", "2", []}, Cl.Call{"date", "1", []}, Cl.Call{"remote", "1", []}]

def is_current(l: Cl.Lift) -> Bool:
  match l:
    case Cl.Unknown{}:
      False{}
    case Cl.Current{}:
      True{}
    case Cl.Stranded{}:
      False{}
    case Cl.Lifted{rev, a, rs}:
      False{}

# every call of cs lifts by t as current
def all_current(+t: List<&2, Cl.Fam>, cs: List<&2, Cl.Call>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, rest}:
      Bool.and(is_current(Cl.lift(t, c)), all_current(t, rest))

# the lift l is a call lifted to rev c
def lifted_at(l: Cl.Lift, +c: String) -> Bool:
  match l:
    case Cl.Unknown{}:
      False{}
    case Cl.Current{}:
      False{}
    case Cl.Stranded{}:
      False{}
    case Cl.Lifted{rev, a, rs}:
      String.eq(rev, c)

# every step ss of family n (current rev c) leaves a rev other than c, and
# a call at that rev lifts by t to c
def steps_arrive.fam(+t: List<&2, Cl.Fam>, +n: String, +c: String, ss: List<&2, Cl.Step>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{s, rest}:
      match s:
        case Cl.Step{+a, b, o}:
          Bool.and(Bool.and(Bool.not(String.eq(a, c)), lifted_at(Cl.lift(t, Cl.Call{n, a, []}), c)), steps_arrive.fam(t, n, c, rest))

# every step of every family of fs arrives (steps_arrive.fam) in table t
def steps_arrive(+t: List<&2, Cl.Fam>, fs: List<&2, Cl.Fam>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      match x:
        case Cl.Fam{+n, +c, ss}:
          Bool.and(steps_arrive.fam(t, n, c, ss), steps_arrive(t, rest))

# LAW call_lift_table_families (R4): every stamp a eukhe tool writes
# (rust_stamps, read from the tools' sources) is current in the shipped
# table, whose families have distinct names and are as many as the
# stamps: so its families are exactly the tools' families, each at the
# rev its tool writes
# EXCLUDES: a tool's family missing (its calls answered unknown), a
#   current rev the tool does not write (its fresh calls lifted or
#   stranded), a foreign family (an MCP tool) in the table, a family
#   listed twice (the second never read)
law call_lift_table_families:
  {all_current(Cl.table(), rust_stamps()) == True{} : Bool} & {names_distinct(Cl.table()) == True{} : Bool} & {List.length(&2, Cl.Fam, Cl.table()) == List.length(&2, Cl.Call, rust_stamps()) : Nat}

# LAW call_lift_table_steps_arrive (R2): in the shipped table, every step
# leaves a rev other than its family's current rev, and a call at that
# rev lifts to the family's current rev
# EXCLUDES: a dangling step (edit@1 -> edit@hl.0, no step out of hl.0)
#   that strands every stored call at its source rev; a step chain that
#   loops without reaching the current rev; a step out of a current rev
law call_lift_table_steps_arrive:
  {steps_arrive(Cl.table(), Cl.table()) == True{} : Bool}

# LAW call_lift_table_example (R1-R4): anchor: the shipped table: zoom@1
# (9695afec6) lifts to zoom@2 with its arguments as stored, zoom@2 and
# edit@hl.1 are current, an MCP tool is unknown, a zoom rev that never
# existed is stranded
# EXCLUDES: a lift that differs on these calls
law call_lift_table_example:
  {[Cl.lift(Cl.table(), Cl.Call{"zoom", "1", ["i", "id", "n"]}), Cl.lift(Cl.table(), Cl.Call{"zoom", "2", ["i", "id"]}), Cl.lift(Cl.table(), Cl.Call{"edit", "hl.1", ["i", "input"]}), Cl.lift(Cl.table(), Cl.Call{"mcp", "1", ["q"]}), Cl.lift(Cl.table(), Cl.Call{"zoom", "0", []})] == [Cl.Lifted{"2", [Cl.Kept{0n, "i"}, Cl.Kept{1n, "id"}, Cl.Kept{2n, "n"}], []}, Cl.Current{}, Cl.Current{}, Cl.Unknown{}, Cl.Stranded{}] : List<&2, Cl.Lift>}

# LAW call_lift_ops_example (R1, R5): anchor: two steps: a rename and a
# fill, then a rename onto a taken name (clashed); a fill of a present
# argument and a rename without its argument do nothing; a cycle strands
# EXCLUDES: a lift that differs on these calls
law call_lift_ops_example:
  {[Cl.lift([Cl.Fam{"t", "3", [Cl.Step{"1", "2", [Cl.Rename{"file", "path"}, Cl.Fill{"limit", "10"}]}, Cl.Step{"2", "3", [Cl.Rename{"a", "path"}]}]}], Cl.Call{"t", "1", ["a", "file", "x"]}), Cl.lift([Cl.Fam{"t", "3", [Cl.Step{"1", "2", [Cl.Rename{"file", "path"}, Cl.Fill{"limit", "10"}]}, Cl.Step{"2", "3", [Cl.Rename{"a", "path"}]}]}], Cl.Call{"t", "2", ["path", "limit"]}), Cl.lift([Cl.Fam{"c", "3", [Cl.Step{"1", "2", []}, Cl.Step{"2", "1", []}]}], Cl.Call{"c", "1", []})] == [Cl.Lifted{"3", [Cl.Kept{0n, "a"}, Cl.Kept{1n, "path"}, Cl.Kept{2n, "x"}, Cl.Added{"limit", "10"}], [Cl.Renamed{"file", "path"}, Cl.Filled{"limit"}, Cl.Clashed{"a", "path"}]}, Cl.Lifted{"3", [Cl.Kept{0n, "path"}, Cl.Kept{1n, "limit"}], []}, Cl.Stranded{}] : List<&2, Cl.Lift>}

# Laws: the entry (R6, R7)
# ------------------------

# LAW call_lift_entry_answers (R6, R7): the entry answers every request
# Rust spells, every count and name within the wire, with the count of
# the calls, then each call's lift by the shipped table spelled by
# itself, in the order of the calls
# EXCLUDES: a field misread or swapped (a family and a rev, two names), a
#   lift tag of another answer, a lift answered for another call or out
#   of order, a count that differs from the calls, a default
law call_lift_entry_answers:
  for +cs: List<&2, Cl.Call>
  for fit: {SpW.fit_req(cs) == True{} : Bool}
  {FCl.ffi(SpW.w_req(cs, "")) == SpW.w_reply(cs) : String}

# LAW call_lift_entry_reads (R7): the entry's decoder reads every spelled
# request that fits the wire back whole, and leaves the input after it
# untouched
# EXCLUDES: a decoder that refuses or misreads a request Rust writes, or
#   eats into what follows it
law call_lift_entry_reads:
  for +cs: List<&2, Cl.Call>
  for +rest: String
  for fit: {SpW.fit_req(cs) == True{} : Bool}
  {FCl.get_req(SpW.w_req(cs, rest)) == Wr.Got{cs, rest} : Wr.Dec<List<&2, Cl.Call>>}

# LAW call_lift_entry_exact (R7): every input the entry does not answer
# with the error form is a spelled request (W1, spelled with the wire's
# writers only) that fits the wire
# EXCLUDES: an answer for input that is no request (a list of calls or of
#   names shorter than its count, a malformed field, input left over)
law call_lift_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FCl.ffi(s)) == False{} : Bool}
  exs cs: List<&2, Cl.Call>
  {s == SpW.w_req(cs, "") : String} & {SpW.fit_req(cs) == True{} : Bool}

# LAW call_lift_entry_refuses (R7): every error the entry answers is
# exactly `E call_lift: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law call_lift_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FCl.ffi(s)) == True{} : Bool}
  {FCl.ffi(s) == Wr.err("call_lift: malformed request") : String}

# LAW call_lift_entry_example (R7): anchor: the strings Rust sends and the
# replies it reads: a zoom@1 call lifted next to a current bash call, no
# calls, a stranded rev, an unknown family; input left over and a bare
# count
# EXCLUDES: another spelling of a request or a reply
law call_lift_entry_example:
  {[FCl.ffi("2,4,zoom1,13,1,i2,id1,n4,bash1,11,1,i"), FCl.ffi("0,"), FCl.ffi("1,4,zoom1,00,"), FCl.ffi("1,3,mcp1,10,"), FCl.ffi("1,4,zoom1,20,x"), FCl.ffi("9")] == ["2,3,1,23,0,0,1,i0,1,2,id0,2,1,n0,1,", "0,", "1,2,", "1,0,", Wr.err("call_lift: malformed request"), Wr.err("call_lift: malformed request")] : List<&2, String>}

# LAW call_lift_entry_short_example (R7): anchor: requests cut short: a
# count of 2 calls with one call, a count of 3 with two
# EXCLUDES: a list of calls cut short answered as a shorter list
law call_lift_entry_short_example:
  {[FCl.ffi("2,4,zoom1,10,"), FCl.ffi("3,4,zoom1,13,1,i2,id1,n4,bash1,11,1,i")] == [Wr.err("call_lift: malformed request"), Wr.err("call_lift: malformed request")] : List<&2, String>}

# LAW call_lift_refines_spec (R1): the lift of every call by every table is
# the spec's
# EXCLUDES: a family found by a later row or another name, a step taken
#   from another rev, a chain that loops past the family's steps, ops out
#   of order, a rename of every argument named `from` or onto a taken
#   name, a fill over a present argument, a receipt dropped or reordered,
#   a lifted call that keeps its old rev
law call_lift_refines_spec:
  for +t: List<&2, Cl.Fam>
  for +c: Cl.Call
  {Cl.lift(t, c) == Sp.lift_spec(t, c) : Cl.Lift}

# The shipped table, frozen: every family a eukhe tool stamps, its current
# rev and its steps, as bend/call_lift.bend ships them. A new family, a rev
# bump or a new step changes this constant, and so needs a law change.
def cl_shipped_table() -> List<&2, Cl.Fam>:
  [Cl.Fam{"bash", "1", []}, Cl.Fam{"read", "1", []}, Cl.Fam{"write", "1", []}, Cl.Fam{"edit", "hl.1", []}, Cl.Fam{"grep", "1", []}, Cl.Fam{"glob", "1", []}, Cl.Fam{"ipython", "1", []}, Cl.Fam{"dyn", "1", []}, Cl.Fam{"zoom", "2", [Cl.Step{"1", "2", []}]}, Cl.Fam{"date", "1", []}, Cl.Fam{"remote", "1", []}]

# LAW call_lift_table_exact (R2, R4): the shipped table is exactly the frozen
# one above: its families in order, each current rev, each step and its ops
# EXCLUDES: a foreign family (an MCP tool) added to the table, so its calls
#   are rewritten; a step or an op added, dropped or changed; a current rev
#   moved; a family dropped, renamed or reordered
law call_lift_table_exact:
  {Cl.table() == cl_shipped_table() : List<&2, Cl.Fam>}
