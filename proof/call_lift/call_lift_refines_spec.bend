# eukhe: the proof of LAW call_lift_refines_spec
#
# PROOF: induction on the table (clm.fam): a row whose name differs leaves both sides at the rest's lift (the induction hypothesis), the matching row reduces both sides to the lift at the family's current rev; there step_of is next (clm.step), walk is the ops of the spec's chain (clm.walk, induction on the fuel, with List.append(o, Nil) == o), and on a found chain apply_ops is ops (clm.ops: apply_op is op, through has == taken, rename == move, arg_key == key_of) on kept == stored (clm.kept).

import Base
import ../../bend/call_lift.bend as Cl
import ../../spec/harness/lift.bend as Sp
import ../../laws/call_lift.bend as CallLift

# the ops of a chain, when there is one
def clm.mops(m: Maybe<&2, List<&2, Cl.Step>>) -> Maybe<&2, List<&2, Cl.Op>>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      Some{Sp.ops_of(p)}

def clm.append_nil(+o: List<&2, Cl.Op>) -> {List.append(&2, Cl.Op, o, Nil{}) == o : List<&2, Cl.Op>}:
  match o:
    case Nil{}:
      {==}
    case Con{x, +rest}:
      %clm.append_nil(rest) : {Con{x, List.append(&2, Cl.Op, rest, Nil{})} == Con{x, _} : List<&2, Cl.Op>}
      {==}

# Lookups
# -------

def clm.step_pick(hit: Bool, x: Cl.Step, m: Maybe<&2, Cl.Step>) -> {Cl.step_of.pick(hit, x, m) == Sp.pick_step(hit, x, m) : Maybe<&2, Cl.Step>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def clm.step(+ss: List<&2, Cl.Step>, +r: String) -> {Cl.step_of(ss, r) == Sp.next(ss, r) : Maybe<&2, Cl.Step>}:
  match ss:
    case Nil{}:
      {==}
    case Con{x, +rest}:
      match x:
        case Cl.Step{+a, +b, +o}:
          %clm.step(rest, r) : {Cl.step_of.pick(String.eq(a, r), Cl.Step{a, b, o}, Cl.step_of(rest, r)) == Sp.pick_step(String.eq(a, r), Cl.Step{a, b, o}, _) : Maybe<&2, Cl.Step>}
          clm.step_pick(String.eq(a, r), Cl.Step{a, b, o}, Cl.step_of(rest, r))

# The path
# --------

def clm.join2(arr: Bool, +o: List<&2, Cl.Op>, a: String, b: String, m: Maybe<&2, List<&2, Cl.Step>>) -> {clm.mops(Sp.chain.join(Cl.Step{a, b, o}, arr, m)) == Cl.walk.join(o, arr, clm.mops(m)) : Maybe<&2, List<&2, Cl.Op>>}:
  match arr:
    case True{}:
      %clm.append_nil(o) : {Some{List.append(&2, Cl.Op, o, Nil{})} == Some{_} : Maybe<&2, List<&2, Cl.Op>>}
      {==}
    case False{}:
      match m:
        case None{}:
          {==}
        case Some{p}:
          {==}

def clm.join(+o: List<&2, Cl.Op>, a: String, b: String, arr: Bool, -w: Maybe<&2, List<&2, Cl.Op>>, +m: Maybe<&2, List<&2, Cl.Step>>, h: {clm.mops(m) == w : Maybe<&2, List<&2, Cl.Op>>}) -> {clm.mops(Sp.chain.join(Cl.Step{a, b, o}, arr, m)) == Cl.walk.join(o, arr, w) : Maybe<&2, List<&2, Cl.Op>>}:
  %h : {clm.mops(Sp.chain.join(Cl.Step{a, b, o}, arr, m)) == Cl.walk.join(o, arr, _) : Maybe<&2, List<&2, Cl.Op>>}
  clm.join2(arr, o, a, b, m)

# the code's walk is the ops of the spec's chain
def clm.walk(fuel: Nat, +ss: List<&2, Cl.Step>, +cur: String, found: Maybe<&2, Cl.Step>) -> {clm.mops(Sp.chain(fuel, ss, cur, found)) == Cl.walk(fuel, ss, cur, found) : Maybe<&2, List<&2, Cl.Op>>}:
  match fuel:
    case 0n:
      {==}
    case 1n++f:
      match found:
        case None{}:
          {==}
        case Some{st}:
          match st:
            case Cl.Step{a, +b, +o}:
              %clm.step(ss, b) : {clm.mops(Sp.chain.join(Cl.Step{a, b, o}, String.eq(b, cur), Sp.chain(f, ss, cur, _))) == Cl.walk.join(o, String.eq(b, cur), Cl.walk(f, ss, cur, Cl.step_of(ss, b))) : Maybe<&2, List<&2, Cl.Op>>}
              clm.join(o, a, b, String.eq(b, cur), Cl.walk(f, ss, cur, Cl.step_of(ss, b)), Sp.chain(f, ss, cur, Cl.step_of(ss, b)), clm.walk(f, ss, cur, Cl.step_of(ss, b)))

# The ops
# -------

def clm.key(a: Cl.Arg) -> {Cl.arg_key(a) == Sp.key_of(a) : String}:
  match a:
    case Cl.Kept{i, k}:
      {==}
    case Cl.Added{k, j}:
      {==}

def clm.has(+args: List<&2, Cl.Arg>, +k: String) -> {Cl.has(args, k) == Sp.taken(args, k) : Bool}:
  match args:
    case Nil{}:
      {==}
    case Con{+a, +rest}:
      %clm.key(a) : {Cl.has(Con{a, rest}, k) == Bool.or(String.eq(_, k), Sp.taken(rest, k)) : Bool}
      %clm.has(rest, k) : {Cl.has(Con{a, rest}, k) == Bool.or(String.eq(Cl.arg_key(a), k), _) : Bool}
      {==}

def clm.rename_at(hit: Bool, a: Cl.Arg, rest: List<&2, Cl.Arg>, mv: List<&2, Cl.Arg>, to: String) -> {Cl.rename.at(hit, a, rest, mv, to) == Sp.move.at(hit, a, rest, mv, to) : List<&2, Cl.Arg>}:
  match hit:
    case True{}:
      match a:
        case Cl.Kept{i, k}:
          {==}
        case Cl.Added{k, j}:
          {==}
    case False{}:
      {==}

def clm.rename(+args: List<&2, Cl.Arg>, +from: String, +to: String) -> {Cl.rename(args, from, to) == Sp.move(args, from, to) : List<&2, Cl.Arg>}:
  match args:
    case Nil{}:
      {==}
    case Con{+a, +rest}:
      %clm.key(a) : {Cl.rename(Con{a, rest}, from, to) == Sp.move.at(String.eq(_, from), a, rest, Sp.move(rest, from, to), to) : List<&2, Cl.Arg>}
      %clm.rename(rest, from, to) : {Cl.rename(Con{a, rest}, from, to) == Sp.move.at(String.eq(Cl.arg_key(a), from), a, rest, _, to) : List<&2, Cl.Arg>}
      clm.rename_at(String.eq(Cl.arg_key(a), from), a, rest, Cl.rename(rest, from, to), to)

def clm.op_rename(present: Bool, taken: Bool, +from: String, +to: String, +args: List<&2, Cl.Arg>, rs: List<&2, Cl.Receipt>) -> {Cl.apply_op.rename(present, taken, from, to, args, rs) == Sp.op_rename(present, taken, from, to, args, rs) : Cl.St}:
  match present:
    case False{}:
      {==}
    case True{}:
      match taken:
        case True{}:
          {==}
        case False{}:
          %clm.rename(args, from, to) : {Cl.St{Cl.rename(args, from, to), List.append(&2, Cl.Receipt, rs, [Cl.Renamed{from, to}])} == Cl.St{_, List.append(&2, Cl.Receipt, rs, [Cl.Renamed{from, to}])} : Cl.St}
          {==}

def clm.op_fill(present: Bool, +key: String, json: String, args: List<&2, Cl.Arg>, rs: List<&2, Cl.Receipt>) -> {Cl.apply_op.fill(present, key, json, args, rs) == Sp.op_fill(present, key, json, args, rs) : Cl.St}:
  match present:
    case True{}:
      {==}
    case False{}:
      {==}

def clm.op(o: Cl.Op, st: Cl.St) -> {Cl.apply_op(o, st) == Sp.op(o, st) : Cl.St}:
  match o:
    case Cl.Rename{+from, +to}:
      match st:
        case Cl.St{+args, rs}:
          %clm.has(args, from) : {Cl.apply_op(Cl.Rename{from, to}, Cl.St{args, rs}) == Sp.op_rename(_, Sp.taken(args, to), from, to, args, rs) : Cl.St}
          %clm.has(args, to) : {Cl.apply_op(Cl.Rename{from, to}, Cl.St{args, rs}) == Sp.op_rename(Cl.has(args, from), _, from, to, args, rs) : Cl.St}
          clm.op_rename(Cl.has(args, from), Cl.has(args, to), from, to, args, rs)
    case Cl.Fill{+key, json}:
      match st:
        case Cl.St{+args, rs}:
          %clm.has(args, key) : {Cl.apply_op(Cl.Fill{key, json}, Cl.St{args, rs}) == Sp.op_fill(_, key, json, args, rs) : Cl.St}
          clm.op_fill(Cl.has(args, key), key, json, args, rs)

def clm.ops(os: List<&2, Cl.Op>, +st: Cl.St) -> {Cl.apply_ops(os, st) == Sp.ops(os, st) : Cl.St}:
  match os:
    case Nil{}:
      {==}
    case Con{+o, rest}:
      %clm.op(o, st) : {Cl.apply_ops(rest, Cl.apply_op(o, st)) == Sp.ops(rest, _) : Cl.St}
      clm.ops(rest, Cl.apply_op(o, st))

def clm.kept(ks: List<&2, String>, +i: Nat) -> {Cl.kept(ks, i) == Sp.stored(ks, i) : List<&2, Cl.Arg>}:
  match ks:
    case Nil{}:
      {==}
    case Con{+k, rest}:
      %clm.kept(rest, 1n+i) : {Con{Cl.Kept{i, k}, Cl.kept(rest, 1n+i)} == Con{Cl.Kept{i, k}, _} : List<&2, Cl.Arg>}
      {==}

# The lift
# --------

def clm.done(cur: String, st: Cl.St) -> {Cl.lift.done(cur, st) == Sp.lift_spec.done(cur, st) : Cl.Lift}:
  match st:
    case Cl.St{a, rs}:
      {==}

def clm.path(+cur: String, +ks: List<&2, String>, m: Maybe<&2, List<&2, Cl.Step>>) -> {Cl.lift.path(cur, ks, clm.mops(m)) == Sp.lift_spec.chain(cur, ks, m) : Cl.Lift}:
  match m:
    case None{}:
      {==}
    case Some{+p}:
      %clm.kept(ks, 0n) : {Cl.lift.done(cur, Cl.apply_ops(Sp.ops_of(p), Cl.St{Cl.kept(ks, 0n), []})) == Sp.lift_spec.done(cur, Sp.ops(Sp.ops_of(p), Cl.St{_, []})) : Cl.Lift}
      %clm.ops(Sp.ops_of(p), Cl.St{Cl.kept(ks, 0n), []}) : {Cl.lift.done(cur, Cl.apply_ops(Sp.ops_of(p), Cl.St{Cl.kept(ks, 0n), []})) == Sp.lift_spec.done(cur, _) : Cl.Lift}
      clm.done(cur, Cl.apply_ops(Sp.ops_of(p), Cl.St{Cl.kept(ks, 0n), []}))

def clm.at(at: Bool, +cur: String, +ks: List<&2, String>, m: Maybe<&2, List<&2, Cl.Step>>) -> {Cl.lift.at(at, cur, ks, clm.mops(m)) == Sp.lift_spec.at(at, cur, ks, m) : Cl.Lift}:
  match at:
    case True{}:
      {==}
    case False{}:
      clm.path(cur, ks, m)

# the matching row: both sides lift at the family's current rev
def clm.row(+r: String, +ks: List<&2, String>, n: String, +c: String, +s: List<&2, Cl.Step>) -> {Cl.lift.fam(r, ks, Some{Cl.Fam{n, c, s}}) == Sp.lift_spec.cur(r, ks, Some{c}, s) : Cl.Lift}:
  %clm.step(s, r) : {Cl.lift.at(String.eq(r, c), c, ks, Cl.walk(List.length(&2, Cl.Step, s), s, c, Cl.step_of(s, r))) == Sp.lift_spec.at(String.eq(r, c), c, ks, Sp.chain(List.length(&2, Cl.Step, s), s, c, _)) : Cl.Lift}
  %clm.walk(List.length(&2, Cl.Step, s), s, c, Cl.step_of(s, r)) : {Cl.lift.at(String.eq(r, c), c, ks, _) == Sp.lift_spec.at(String.eq(r, c), c, ks, Sp.chain(List.length(&2, Cl.Step, s), s, c, Cl.step_of(s, r))) : Cl.Lift}
  clm.at(String.eq(r, c), c, ks, Sp.chain(List.length(&2, Cl.Step, s), s, c, Cl.step_of(s, r)))

def clm.fam_pick(hit: Bool, +r: String, +ks: List<&2, String>, n: String, c: String, s: List<&2, Cl.Step>, -mf: Maybe<&2, Cl.Fam>, -mc: Maybe<&2, String>, -ms: List<&2, Cl.Step>, ih: {Cl.lift.fam(r, ks, mf) == Sp.lift_spec.cur(r, ks, mc, ms) : Cl.Lift}) -> {Cl.lift.fam(r, ks, Cl.fam_of.pick(hit, Cl.Fam{n, c, s}, mf)) == Sp.lift_spec.cur(r, ks, Sp.pick_rev(hit, c, mc), Sp.pick_steps(hit, s, ms)) : Cl.Lift}:
  match hit:
    case True{}:
      clm.row(r, ks, n, c, s)
    case False{}:
      ih

def clm.fam(+t: List<&2, Cl.Fam>, +f: String, +r: String, +ks: List<&2, String>) -> {Cl.lift.fam(r, ks, Cl.fam_of(t, f)) == Sp.lift_spec.cur(r, ks, Sp.current(t, f), Sp.steps_of(t, f)) : Cl.Lift}:
  match t:
    case Nil{}:
      {==}
    case Con{x, +rest}:
      match x:
        case Cl.Fam{+n, +c, +s}:
          clm.fam_pick(String.eq(n, f), r, ks, n, c, s, Cl.fam_of(rest, f), Sp.current(rest, f), Sp.steps_of(rest, f), clm.fam(rest, f, r, ks))

def CallLift.call_lift_refines_spec(t, c):
  match c:
    case Cl.Call{+f, +r, +ks}:
      clm.fam(t, f, r, ks)
